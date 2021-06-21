use crate::Result;
use byteorder::{BigEndian, WriteBytesExt};
use serde::{Deserialize, Serialize};
use serde_cbor::to_vec;
use std::convert::TryInto;
use std::io::{self, Write};
use std::num::NonZeroU64;
use std::thread::panicking;
use versioned::Versioned;

/// The version of BookWriter being used
const BOOK_V1_MAGIC: u32 = 0xFF33_0001;

/// The fixed size of a header block
const HEADER_SIZE: usize = 4096;

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
//
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
    pub fn close(mut self) -> Result<()> {
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
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use std::io::Cursor;

    #[test]
    fn empty_book() {
        let magic = 0x1234;
        let buffer = Cursor::new(Vec::<u8>::new());
        let book = BookWriter::new(buffer, magic).unwrap();
        book.close().unwrap();
    }

    #[test]
    fn simple_book() {
        let magic = 0x1234;
        let buffer = Cursor::new(Vec::<u8>::new());
        let mut book = BookWriter::new(buffer, magic).unwrap();
        let chapter = book.new_chapter(1);
        chapter.close().unwrap();
        let chapter = book.new_chapter(2);
        chapter.close().unwrap();
        book.close().unwrap();
    }
}
