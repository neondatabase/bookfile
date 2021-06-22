use crate::{BookError, Result};
use byteorder::{BigEndian, ReadBytesExt, WriteBytesExt};
use serde::{Deserialize, Serialize};
use serde_cbor::{from_slice, to_vec};
use std::convert::TryInto;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::num::NonZeroU64;
use std::thread::panicking;
use versioned::Versioned;

/// The version of BookWriter being used
const BOOK_V1_MAGIC: u32 = 0xFF33_0001;

/// The fixed size of a header block
const HEADER_SIZE: usize = 4096;

/// The maximum TOC size we will attempt to read
const MAX_TOC_SIZE: u64 = 0x400_0000; // 64MB

// Base-type placeholder for the Versioned trait
#[doc(hidden)]
pub enum FileHeaderBase {}

/// The `Book` file header struct.
///
/// This is used to communicate that this file is in `Book`
/// format, and what type of data it contains.
#[derive(Debug, Versioned, Serialize, Deserialize)]
pub struct FileHeaderV1 {
    bookwriter_magic: u32,
    pub user_magic: u32,
}

/// A type alias; this will always point to the latest version `FileHeader`.
pub type FileHeader = FileHeaderV1;

// Base-type placeholder for the Versioned trait
#[doc(hidden)]
pub enum FileSpanBase {}

/// A `FileSpan` stores the byte offset and length of some range of a file.
///
/// The `FileSpan` deliberately cannot store a zero-length span, because it
/// can be confusing if code attempts to read a zero-sized span. Use
/// `Option<FileSpan` to represent a zero-sized span.
///
#[derive(Debug, Versioned, Serialize, Deserialize)]
pub struct FileSpanV1 {
    pub offset: u64,
    pub length: NonZeroU64,
}

/// A type alias; this will always point to the latest version `FileSpan`.
pub type FileSpan = FileSpanV1;

impl FileSpan {
    /// Create a `FileSpan` from offset and length.
    ///
    /// If `length` is 0, `None` will be returned.
    pub fn from_offset_length(offset: usize, length: usize) -> Option<Self> {
        // usize always fits in u64, on every target arch we care about.
        // So this error path should be optimized away.
        let offset = offset.try_into().unwrap();
        let length: u64 = length.try_into().unwrap();
        // Try to create a NonZeroU64 length; if that returns Some(l)
        // then return Some(FileSpan{..}) else None.
        NonZeroU64::new(length).map(|length| FileSpan { offset, length })
    }

    #[track_caller]
    fn length_usize(&self) -> usize {
        let length: u64 = self.length.into();
        length.try_into().unwrap()
    }
}

// Base-type placeholder for the Versioned trait
#[doc(hidden)]
pub enum TocEntryBase {}

/// A Table-of-contents entry.
///
/// This contains an identifying number, and a file span that
/// tells us what chunk of the file contains this chapter.
#[derive(Debug, Versioned, Serialize, Deserialize)]
pub struct TocEntryV1 {
    pub id: u64,
    pub span: Option<FileSpan>,
}

/// A type alias; this will always point to the latest version `TocEntry`.
pub type TocEntry = TocEntryV1;

/// A tool for writing a `Chapter`.
///
/// A `ChapterWriter` creates a new chapter. Chapters will be written
/// sequentially in the file, and only one can be active at a time.
///
/// To write the chapter data, use the [`Write`] interface.
///
/// When the chapter is complete, call [`close()`] to flush any
/// remaining bytes and update the `Book` table-of-contents.
///
/// Attempting to drop a chapter without calling `close` will
/// cause a panic.
///
/// See [`BookWriter`] for more information.
///
/// [`close()`]: Self::close
pub struct ChapterWriter<'a, W> {
    writer: &'a mut W,
    toc_entries: &'a mut Vec<TocEntry>,
    id: u64,
    offset: usize,
    length: usize,
}

impl<'a, W> ChapterWriter<'a, W>
where
    W: Write,
{
    /// Create a new `ChapterWriter`.
    fn new(book: &'a mut BookWriter<W>, id: u64, offset: usize) -> Self {
        ChapterWriter {
            writer: &mut book.writer,
            toc_entries: &mut book.toc_entries,
            id,
            offset,
            length: 0,
        }
    }

    /// Complete the chapter.
    ///
    /// `Chapter` instances should not be dropped; they must be consumed
    /// by calling `close`. This allows us to detect any final IO errors
    /// and update the TOC.
    pub fn close(mut self) -> Result<()> {
        self.flush()?;

        let toc_entry = TocEntry {
            id: self.id,
            span: FileSpan::from_offset_length(self.offset, self.length),
        };

        self.toc_entries.push(toc_entry);

        // Mark this Chapter as safe to drop.
        self.length = 0;

        Ok(())
    }
}

impl<W> Drop for ChapterWriter<'_, W> {
    fn drop(&mut self) {
        // A `Chapter` must not be dropped if it has contents,
        // because we want the owner to call [`close`] and handle
        // any IO errors.
        if self.length != 0 {
            // We don't want to panic if the Chapter is being dropped
            // while unwinding.
            if !panicking() {
                panic!("Chapter was dropped without calling close()");
            }
        }
    }
}

impl<'a, W> Write for ChapterWriter<'a, W>
where
    W: Write,
{
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let bytes_written = self.writer.write(buf)?;
        self.length += bytes_written;
        Ok(bytes_written)
    }

    // Note `close` will call `flush` automatically.
    fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }
}

/// A tool for writing a `Book`.
///
/// A `BookWriter` creates a new `Book`.
///
/// To write a chapter, call [`new_chapter()`].
///
/// When the book is complete, call [`close()`] to flush any
/// remaining bytes and write out the table of contents.
///
/// [`close()`]: Self::close
/// [`new_chapter()`]: Self::new_chapter
///
#[derive(Debug)]
pub struct BookWriter<W: Write> {
    writer: W,
    current_offset: usize,
    header: FileHeader,
    toc_entries: Vec<TocEntry>,
}

impl<W: Write> BookWriter<W> {
    /// Create a new `BookWriter`.
    ///
    /// `user_magic` is a number stored in the file for later identification.
    /// It can contain any value the user wants, and can be used to
    /// disambiguate different kinds of files.
    ///
    pub fn new(writer: W, user_magic: u32) -> Result<Self> {
        let mut this = BookWriter {
            writer,
            current_offset: 0,
            header: FileHeader {
                bookwriter_magic: BOOK_V1_MAGIC,
                user_magic,
            },
            toc_entries: vec![],
        };
        this.write_header()?;
        Ok(this)
    }

    fn write_header(&mut self) -> Result<()> {
        // Serialize the header into a buffer.
        let mut header_buf = to_vec(&self.header)?;
        if header_buf.len() > HEADER_SIZE {
            panic!("serialized header exceeds maximum size");
        }
        // Pad the buffer with zeroes so that it's the expected
        // size.
        header_buf.resize(HEADER_SIZE, 0);

        // FIXME: wrap the writer in some struct that automatically counts
        // the number of bytes written.
        self.writer.write_all(&header_buf)?;
        self.current_offset = HEADER_SIZE;
        Ok(())
    }

    /// Create a new `ChapterWriter`.
    ///
    /// The chapter `id` can be any value the user wants, and can be
    /// used to later locate a chapter.
    ///
    pub fn new_chapter(&mut self, id: u64) -> ChapterWriter<'_, W> {
        ChapterWriter::new(self, id, self.current_offset)
    }

    /// Finish writing the `Book` file.
    ///
    /// On success, this returns the original writer stream.
    /// It is normal to discard it, except in unit tests.
    pub fn close(mut self) -> Result<W> {
        // Serialize the TOC into a buffer.
        let mut toc_buf = to_vec(&self.toc_entries)?;

        // Manually serialize the TOC length, so that it has a fixed size and
        // a fixed offset (relative to the end of the file).
        let toc_length: u64 = toc_buf.len().try_into().unwrap();
        toc_buf.write_u64::<BigEndian>(toc_length).unwrap();

        // Write the TOC.
        self.writer.write_all(&toc_buf)?;

        // TODO: Add a checksum.

        self.writer.flush()?;
        Ok(self.writer)
    }
}

/// A chapter index.
pub struct ChapterIndex(pub usize);

/// An interface for reading a Bookfile.
///
#[derive(Debug)]
pub struct Book<R> {
    reader: R,
    header: FileHeader,
    toc_entries: Vec<TocEntry>,
}

impl<R> Book<R>
where
    R: Read + Seek,
{
    /// Create a new Book from a stream
    ///
    /// This call will attempt to read the file header and table of contents.
    /// It may fail due to IO errors while reading, or invalid file data.
    ///
    /// The stream must impl the `Read` and `Seek` traits (e.g. a `File`).
    ///
    pub fn new(mut reader: R) -> Result<Self> {
        // Read the header from the beginning of the file.
        let mut header_buf = [0u8; HEADER_SIZE];
        reader.seek(SeekFrom::Start(0))?;
        reader.read_exact(&mut header_buf)?;
        let mut buf_reader = &header_buf[..];
        let deser = serde_cbor::Deserializer::from_reader(&mut buf_reader);
        // FIXME: this is a terrible hack, because serde_cbor always fails
        // if there is trailing data. Maybe replace this with pre-header that
        // contains magic numbers and header size?
        // FIXME: get rid of .unwrap()
        let header: FileHeader = deser.into_iter().next().unwrap()?;

        // Verify magic numbers
        if header.bookwriter_magic != BOOK_V1_MAGIC {
            return Err(BookError::Serializer);
        }

        // Read the TOC length. For v1 it is the last 8 bytes of the file.
        reader.seek(SeekFrom::End(-8))?;
        let toc_len = reader.read_u64::<BigEndian>()?;
        if toc_len > MAX_TOC_SIZE {
            return Err(BookError::Serializer);
        }
        let toc_len: i64 = toc_len.try_into().map_err(|_| BookError::Serializer)?;
        // Because we already checked MAX_TOC_SIZE this math cannot overflow.
        reader.seek(SeekFrom::End(-8 - toc_len))?;

        // Deserialize the TOC.
        // FIXME: from_reader seems like a better approach, but it seems
        // to expect that the data ends at EOF, otherwise it throws
        // "trailing data" errors, which seems really odd.
        // FIXME: build a Read adapter than is bounded by a certain span?
        let mut toc_buf = vec![0u8; toc_len.try_into().unwrap()];
        reader.read_exact(&mut toc_buf)?;
        let toc_entries: Vec<TocEntry> = from_slice(&toc_buf)?;

        Ok(Book {
            reader,
            header,
            toc_entries,
        })
    }

    /// Look up a chapter.
    ///
    /// For now, we assume chapter ids are unique. That's dumb,
    /// and will be fixed in a future version.
    pub fn find_chapter(&self, id: u64) -> Option<ChapterIndex> {
        for (index, entry) in self.toc_entries.iter().enumerate() {
            if entry.id == id {
                return Some(ChapterIndex(index));
            }
        }
        None
    }

    /// Read a chapter by index.
    pub fn read_chapter(&mut self, index: ChapterIndex) -> Result<Vec<u8>> {
        let toc_entry = self.toc_entries.get(index.0).ok_or(BookError::NoChapter)?;
        match &toc_entry.span {
            None => {
                // If the span is empty, no IO is necessary; just return
                // an empty Vec.
                Ok(vec![])
            }
            Some(span) => {
                self.reader.seek(SeekFrom::Start(span.offset))?;
                let mut buf = vec![0u8; span.length_usize()];
                self.reader.read_exact(&mut buf)?;
                Ok(buf)
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use std::io::Cursor;

    #[test]
    fn empty_book() {
        let magic = 0x1234;
        let mut cursor = Cursor::new(Vec::<u8>::new());
        {
            let book = BookWriter::new(&mut cursor, magic).unwrap();
            book.close().unwrap();
        }

        // This file contains only a header, an empty TOC, and a TOC-length.
        assert_eq!(cursor.get_ref().len(), 4096 + 1 + 8);

        // If this succeeds then the header and TOC were parsed correctly.
        let _ = Book::new(cursor).unwrap();
    }

    #[test]
    fn simple_book() {
        let magic = 0x1234;
        let buffer = {
            let buffer = Cursor::new(Vec::<u8>::new());
            let mut book = BookWriter::new(buffer, magic).unwrap();
            let chapter = book.new_chapter(11);
            chapter.close().unwrap();
            let mut chapter = book.new_chapter(22);
            chapter.write_all(b"This is chapter 22").unwrap();
            chapter.close().unwrap();
            book.close().unwrap()
        };
        let mut book = Book::new(buffer).unwrap();
        let n = book.find_chapter(11).unwrap();
        let ch1 = book.read_chapter(n).unwrap();
        assert!(ch1.is_empty());

        assert!(book.find_chapter(1).is_none());

        let n = book.find_chapter(22).unwrap();
        let ch2 = book.read_chapter(n).unwrap();
        assert_eq!(ch2, b"This is chapter 22");
    }
}
