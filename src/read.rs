use std::convert::TryInto;
use std::io::{self, BufRead, Read, Seek, SeekFrom};

#[cfg(target_family = "unix")]
use std::os::unix::fs::FileExt;

/// A helper function to convert `u64` to `usize`.
///
/// This will panic if the value doesn't fit in a `usize`.
#[track_caller]
fn to_usize(x: u64) -> usize {
    x.try_into().expect("u64->usize overflow")
}

/// A wrapper around a `Read`+`Sync` stream that constrains reads to a byte range.
pub struct BoundedReader<'r, R> {
    reader: &'r mut R,
    start: u64,
    length: u64,
    pos: Option<u64>,
}

impl<'r, R> BoundedReader<'r, R>
where
    R: Read + Seek,
{
    /// Create a new BoundedReader
    pub fn new(reader: &'r mut R, start: u64, length: u64) -> Self {
        BoundedReader {
            reader,
            start,
            length,
            pos: None,
        }
    }

    /// Create a BoundedReader that returns 0 bytes.
    pub fn empty(reader: &'r mut R) -> Self {
        BoundedReader {
            reader,
            start: 0,
            length: 0,
            pos: None,
        }
    }

    fn initialize_pos(&mut self) -> io::Result<u64> {
        match &self.pos {
            None => {
                self.seek(SeekFrom::Start(0))?;
                self.pos = Some(0);
                Ok(0)
            }
            Some(p) => Ok(*p),
        }
    }

    // Caller must ensure that `initialize_pos` has been called,
    // or a panic may result.
    fn move_pos(&mut self, delta: usize) {
        *self.pos.as_mut().expect("uninitialized pos") += delta as u64;
    }
}

impl<R> Read for BoundedReader<'_, R>
where
    R: Read + Seek,
{
    fn read(&mut self, mut buf: &mut [u8]) -> io::Result<usize> {
        // If we are reading an empty range, always return EOF.
        if self.length == 0 {
            return Ok(0);
        }
        let pos = self.initialize_pos()?;
        if pos == self.length {
            // EOF for the bounded range.
            return Ok(0);
        }
        if pos > self.length {
            panic!("BoundedReader pos went out of bounds");
        }
        let max_len = self.length - pos;
        if buf.len() as u64 > max_len {
            // max_len must fit in a usize since it's smaller than buf.len()
            buf = &mut buf[..to_usize(max_len)];
        }
        let bytes_read = self.reader.read(buf)?;
        self.move_pos(bytes_read);
        Ok(bytes_read)
    }
}

impl<R> Seek for BoundedReader<'_, R>
where
    R: Seek,
{
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        fn seek_error() -> io::Error {
            io::Error::new(io::ErrorKind::InvalidInput, "seek out of bounds")
        }

        let real_pos = match pos {
            SeekFrom::Start(s) => self.start.checked_add(s).ok_or_else(seek_error)?,
            SeekFrom::End(e) => {
                let end = self.start + self.length;
                let e: u64 = (-e).try_into().map_err(|_| seek_error())?;
                end.checked_sub(e).ok_or_else(seek_error)?
            }
            SeekFrom::Current(c) => {
                let real_pos = self.reader.stream_position()?;
                let real_pos: i64 = real_pos.try_into().map_err(|_| seek_error())?;
                let real_pos = real_pos.checked_add(c).ok_or_else(seek_error)?;
                let real_pos: u64 = real_pos.try_into().map_err(|_| seek_error())?;
                real_pos
            }
        };
        if real_pos > self.start + self.length {
            return Err(seek_error());
        }
        self.reader.seek(SeekFrom::Start(real_pos)).map(|new_pos| {
            let bounded_pos = new_pos
                .checked_sub(self.start)
                .expect("allowed seek to bad position");
            self.pos = Some(bounded_pos);
            bounded_pos
        })
    }
}

// If the underlying Read stream implements BufRead, then we should too.
impl<R> BufRead for BoundedReader<'_, R>
where
    R: BufRead + Seek,
{
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        let pos = self.initialize_pos()?;
        let buf = self.reader.fill_buf()?;
        let max_len = self.length - pos;
        if buf.len() as u64 > max_len {
            // max_len must fit in a usize since it's smaller than buf.len()
            let max_len: usize = max_len.try_into().unwrap();
            Ok(&buf[..max_len])
        } else {
            Ok(buf)
        }
    }

    fn consume(&mut self, amt: usize) {
        // The act of reading should have caused self.pos to be Some(_).
        let max_len = self.length - self.pos.unwrap();
        if amt as u64 > max_len {
            panic!(
                "consume({}) exceeds bound; only {} bytes until end",
                amt, max_len
            );
        }
        self.reader.consume(amt);
        self.move_pos(amt);
    }
}

// This is a half implementation of the FileExt trait, but since that trait
// is os-specific, and we don't support `write_at`, supplying a function with
// the same name seems like an acceptable compromise.
#[cfg(target_family = "unix")]
impl<R> BoundedReader<'_, R>
where
    R: FileExt,
{
    pub fn read_at(&self, buf: &mut [u8], offset: u64) -> io::Result<usize> {
        let bound_end = self.start.checked_add(self.length).unwrap();
        if offset > bound_end {
            // Trying to read past the end of the bounded region.
            return Ok(0);
        }
        let requested_end = self.start + offset + buf.len() as u64;
        let end_reduction = requested_end.saturating_sub(bound_end);
        // Will always succeed, since end_reduction can never be larger than buf.len()
        let end_reduction: usize = end_reduction.try_into().unwrap();
        let capped_len: usize = buf.len().checked_sub(end_reduction).unwrap();
        let capped_buf = &mut buf[..capped_len];

        // Will always succeed, since we already checked that the offset
        // fits within the bounded range.
        let adjusted_offset = self.start.checked_add(offset).unwrap();
        self.reader.read_at(capped_buf, adjusted_offset)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{BufReader, Cursor, ErrorKind, Write};

    #[test]
    fn bounds_test() {
        let mut buf = Vec::<u8>::new();
        for ii in 0..128 {
            buf.push(ii);
        }
        let mut cursor = Cursor::new(buf);
        let mut subcursor = BoundedReader::new(&mut cursor, 5, 5);

        // Try read past the end.
        let mut read_buf = [0u8; 8];
        let bytes_read = subcursor.read(&mut read_buf).unwrap();
        assert_eq!(bytes_read, 5);
        assert_eq!(read_buf, [5, 6, 7, 8, 9, 0, 0, 0]);

        // Try read, right at the end.
        subcursor.seek(SeekFrom::Start(5)).unwrap();
        let mut read_buf = [0u8; 2];
        let bytes_read = subcursor.read(&mut read_buf).unwrap();
        assert_eq!(bytes_read, 0);
        assert_eq!(read_buf, [0, 0]);

        // Seek past the end
        let err = subcursor.seek(SeekFrom::Start(6)).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::InvalidInput);

        // Seek relative to the end
        subcursor.seek(SeekFrom::End(-4)).unwrap();
        let mut read_buf = [0u8; 4];
        let bytes_read = subcursor.read(&mut read_buf).unwrap();
        assert_eq!(bytes_read, 4);
        assert_eq!(read_buf, [6, 7, 8, 9]);

        // Seek relative to the current position
        subcursor.seek(SeekFrom::Current(-2)).unwrap();
        subcursor.seek(SeekFrom::Current(-2)).unwrap();
        let mut read_buf = [0u8; 4];
        let bytes_read = subcursor.read(&mut read_buf).unwrap();
        assert_eq!(bytes_read, 4);
        assert_eq!(read_buf, [6, 7, 8, 9]);
    }

    #[test]
    fn bufread() {
        let mut buf = Vec::<u8>::new();
        for ii in 0..128 {
            buf.push(ii);
        }
        let cursor = Cursor::new(buf);
        let mut bufreader = BufReader::new(cursor);
        let mut reader = BoundedReader::new(&mut bufreader, 5, 5);

        // Use the BufRead interface to get some data
        let buffered = reader.fill_buf().unwrap();
        assert_eq!(buffered, [5, 6, 7, 8, 9]);
        reader.consume(3);
        let buffered = reader.fill_buf().unwrap();
        assert_eq!(buffered, [8, 9]);
    }

    #[test]
    fn read_at() {
        let mut buf = Vec::<u8>::new();
        for ii in 0..128 {
            buf.push(ii);
        }
        let mut file = tempfile::tempfile().unwrap();
        file.write_all(&buf).unwrap();

        let reader = BoundedReader::new(&mut file, 5, 5);

        // A read entirely contained within the bounded range.
        let mut read_buf = [0u8; 3];
        let bytes_read = reader.read_at(&mut read_buf, 1).unwrap();
        assert_eq!(bytes_read, 3);
        assert_eq!(read_buf, [6, 7, 8]);

        // Try read past the end.
        let mut read_buf = [0u8; 8];
        let bytes_read = reader.read_at(&mut read_buf, 0).unwrap();
        assert_eq!(bytes_read, 5);
        assert_eq!(read_buf, [5, 6, 7, 8, 9, 0, 0, 0]);

        // Try read, right at the end.
        let mut read_buf = [0u8; 2];
        let bytes_read = reader.read_at(&mut read_buf, 5).unwrap();
        assert_eq!(bytes_read, 0);
        assert_eq!(read_buf, [0, 0]);
    }
}
