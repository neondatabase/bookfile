use std::io::{self, Write};

use crc32c::crc32c_append;

/// Helper struct for checksumming and counting the bytes written to an
/// [`io::Write`].
#[derive(Debug)]
pub struct ChecksummedWriter<W> {
    writer: W,
    current_offset: usize,
    checksum: u32,
}

impl<I: Write> ChecksummedWriter<I> {
    pub fn new(writer: I) -> Self {
        Self {
            writer,
            current_offset: 0,
            checksum: 0,
        }
    }

    /// Returns the number of bytes written so far.
    pub fn get_offset(&self) -> usize {
        self.current_offset
    }

    /// Returns the crc32c checksum of all bytes written so far.
    pub fn get_checksum(&self) -> u32 {
        self.checksum
    }

    pub fn close(self) -> I {
        self.writer
    }
}

impl<I: Write> Write for ChecksummedWriter<I> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let bytes_written = self.writer.write(buf)?;
        self.current_offset += bytes_written;
        self.checksum = crc32c_append(self.checksum, &buf[..bytes_written]);
        Ok(bytes_written)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }
}
