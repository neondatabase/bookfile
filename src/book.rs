use crate::read::BoundedReader;
use crate::{BookError, Result};
use aversion::group::{DataSink, DataSourceExt};
use aversion::util::cbor::CborData;
use aversion::{assign_message_ids, FromVersion, UpgradeLatest, Versioned};
use byteorder::{BigEndian, ReadBytesExt, WriteBytesExt};
use serde::{Deserialize, Serialize};
use std::convert::TryInto;
use std::io::{self, Cursor, Read, Seek, SeekFrom, Write};
use std::num::NonZeroU64;
use std::thread::panicking;

/// The version of BookWriter being used
const BOOK_V1_MAGIC: u32 = 0xFF33_0001;

/// The fixed size of a header block
const HEADER_SIZE: usize = 4096;

/// The maximum TOC size we will attempt to read
const MAX_TOC_SIZE: u64 = 0x400_0000; // 64MB

/// The `Book` file header struct.
///
/// This is used to communicate that this file is in `Book`
/// format, and what type of data it contains.
#[derive(Debug, Versioned, UpgradeLatest, Serialize, Deserialize)]
pub struct FileHeaderV1 {
    bookwriter_magic: u32,
    pub user_magic: u32,
}

/// A type alias; this will always point to the latest version `FileHeader`.
pub type FileHeader = FileHeaderV1;

/// A `FileSpan` stores the byte offset and length of some range of a file.
///
/// The `FileSpan` deliberately cannot store a zero-length span, because it
/// can be confusing if code attempts to read a zero-sized span. Use
/// `Option<FileSpan` to represent a zero-sized span.
///
#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct FileSpanV1 {
    pub offset: u64,
    pub length: NonZeroU64,
}

impl FileSpanV1 {
    /// Create a `FileSpan` from offset and length.
    ///
    /// If `length` is 0, `None` will be returned.
    pub fn from_offset_length(offset: usize, length: usize) -> Option<Self> {
        let offset = offset as u64;
        let length = length as u64;
        // Try to create a NonZeroU64 length; if that returns Some(l)
        // then return Some(FileSpan{..}) else None.
        NonZeroU64::new(length).map(|length| FileSpanV1 { offset, length })
    }
}

// A type alias, to make code a little easier to read.
type FileSpan = FileSpanV1;

/// A Table-of-contents entry.
///
/// This contains an identifying number, and a file span that
/// tells us what chunk of the file contains this chapter.
#[derive(Debug, Serialize, Deserialize)]
struct TocEntryV1 {
    id: u64,
    span: Option<FileSpanV1>,
}

/// A Table-of-contents entry.
///
/// This contains an identifying number, and a file span that
/// tells us what chunk of the file contains this chapter.
#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct TocEntryV2 {
    pub id: Box<[u8]>,
    pub span: Option<FileSpanV1>,
}

// A type alias, to make code a little easier to read.
type TocEntry = TocEntryV2;

/// A Table-of-contents.
///
/// This contains multiple `TocEntry` values, one for each chapter.
#[derive(Debug, Default, Serialize, Deserialize, Versioned)]
struct TocV1(Vec<TocEntryV1>);

/// A Table-of-contents.
///
/// This contains multiple `TocEntry` values, one for each chapter.
#[derive(Debug, Default, Serialize, Deserialize, Versioned, UpgradeLatest)]
pub struct TocV2(Vec<TocEntryV2>);

impl FromVersion<TocV1> for TocV2 {
    fn from_version(v1: TocV1) -> Self {
        let entries =
            v1.0.into_iter()
                .map(|v1_entry| TocEntryV2 {
                    id: Box::new(v1_entry.id.to_be_bytes()),
                    span: v1_entry.span,
                })
                .collect();
        TocV2(entries)
    }
}

// A type alias, used by the Versioned trait.
type Toc = TocV2;

impl Toc {
    fn add(&mut self, entry: TocEntry) {
        self.0.push(entry);
    }

    fn iter(&self) -> impl Iterator<Item = &TocEntry> {
        self.0.iter()
    }

    fn get_chapter<Id>(&self, id: Id) -> Result<&TocEntry>
    where
        Id: Into<ChapterId>,
    {
        let id: ChapterId = id.into();
        let entry = self.iter().find(|entry| entry.id == id.0);
        entry.ok_or(BookError::NoChapter)
    }
}

assign_message_ids! {
    FileHeader: 1,
    Toc: 2,
}

/// A chapter identifier.
///
/// This is internally a byte array. Any type may be used as a chapter
/// identifier, as long as it implements `Into<ChapterId>`.
pub struct ChapterId(pub Box<[u8]>);

impl From<&[u8]> for ChapterId {
    fn from(slice: &[u8]) -> Self {
        Self(slice.into())
    }
}

impl From<Box<[u8]>> for ChapterId {
    fn from(boxed: Box<[u8]>) -> Self {
        Self(boxed)
    }
}

impl From<&str> for ChapterId {
    fn from(s: &str) -> Self {
        String::from(s).into()
    }
}

impl From<String> for ChapterId {
    fn from(s: String) -> Self {
        Self(s.into_bytes().into_boxed_slice())
    }
}

impl From<u64> for ChapterId {
    fn from(n: u64) -> Self {
        Self(Box::new(n.to_be_bytes()))
    }
}

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
pub struct ChapterWriter<W> {
    book: Option<BookWriter<W>>,
    id: Box<[u8]>,
    offset: usize,
    length: usize,
}

impl<W> ChapterWriter<W>
where
    W: Write,
{
    /// Create a new `ChapterWriter`.
    fn new<Id>(book: BookWriter<W>, id: Id) -> Self
    where
        Id: Into<ChapterId>,
    {
        let id: ChapterId = id.into();
        let offset = book.current_offset;
        ChapterWriter {
            book: Some(book),
            id: id.0,
            offset,
            length: 0,
        }
    }

    /// Complete the chapter.
    ///
    /// This will return the original BookWriter after updating its TOC.
    ///
    /// `Chapter` instances should not be dropped; they must be consumed
    /// by calling `close`. This allows us to detect any final IO errors
    /// and update the TOC.
    pub fn close(mut self) -> Result<BookWriter<W>> {
        self.flush()?;

        let toc_entry = TocEntry {
            id: self.id.clone(),
            span: FileSpan::from_offset_length(self.offset, self.length),
        };

        // It should never be possible to panic here, because self.book
        // is set to Some during construction, and it's not possible to
        // reach the ChapterWriter after close().
        let mut book = self.book.take().unwrap();

        book.toc.add(toc_entry);
        book.current_offset += self.length;

        Ok(book)
    }
}

impl<W> Drop for ChapterWriter<W> {
    fn drop(&mut self) {
        // A `Chapter` must not be dropped if it has contents,
        // because we want the owner to call [`close`] and handle
        // any IO errors.
        if self.book.is_some() {
            // We don't want to panic if the Chapter is being dropped
            // while unwinding.
            if !panicking() {
                panic!("ChapterWriter was dropped without calling close()");
            }
        }
    }
}

impl<W> Write for ChapterWriter<W>
where
    W: Write,
{
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        // It should never be possible to panic here, because self.book
        // is set to Some during construction, and it's not possible to
        // reach the ChapterWriter after close().
        let book = self.book.as_mut().unwrap();
        let bytes_written = book.writer.write(buf)?;
        self.length += bytes_written;
        Ok(bytes_written)
    }

    // Note `close` will call `flush` automatically.
    fn flush(&mut self) -> io::Result<()> {
        // It should never be possible to panic here, because self.book
        // is set to Some during construction, and it's not possible to
        // reach the ChapterWriter after close().
        let book = self.book.as_mut().unwrap();
        book.writer.flush()
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
pub struct BookWriter<W> {
    writer: W,
    current_offset: usize,
    header: FileHeader,
    toc: Toc,
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
            toc: Toc::default(),
        };
        this.write_header()?;
        Ok(this)
    }

    fn write_header(&mut self) -> Result<()> {
        // Serialize the header into a buffer.
        let header_buf = Cursor::new(Vec::<u8>::new());
        let mut header_writer = CborData::new(header_buf);
        header_writer.write_message(&self.header)?;

        let mut header_buf = header_writer.into_inner().into_inner();
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
    /// used to later locate a chapter. It may be any type that
    /// implements [`Into<ChapterId>`][ChapterId].
    ///
    pub fn new_chapter<Id>(self, id: Id) -> ChapterWriter<W>
    where
        Id: Into<ChapterId>,
    {
        ChapterWriter::new(self, id)
    }

    /// Finish writing the `Book` file.
    ///
    /// On success, this returns the original writer stream.
    /// It is normal to discard it, except in unit tests.
    pub fn close(mut self) -> Result<W> {
        // Serialize the TOC into a buffer.
        let toc_buf = Cursor::new(Vec::<u8>::new());
        let mut toc_writer = CborData::new(toc_buf);
        toc_writer.write_message(&self.toc)?;
        let mut toc_buf = toc_writer.into_inner().into_inner();

        // Manually serialize the TOC length, so that it has a fixed size and
        // a fixed offset (relative to the end of the file).
        let toc_length = toc_buf.len() as u64;
        toc_buf.write_u64::<BigEndian>(toc_length).unwrap();

        // Write the TOC.
        self.writer.write_all(&toc_buf)?;

        // TODO: Add a checksum.

        self.writer.flush()?;
        Ok(self.writer)
    }
}

/// An interface for reading a Bookfile.
///
/// The `Book` type represents a read-only Bookfile. Invividual chapters can
/// be read in their entirety, or incrementally using the [`Read`] interface.
/// [`Seek`] and [`read_at`]/[`read_exact_at`]
/// are also provided, and work within the context of that chapter: the seek
/// offset is the offset within the chapter, and a read at the end of the
/// chapter will return EOF.
///
/// [`Read`]: std::io::Read
/// [`Seek`]: std::io::Seek
/// [`read_at`]: crate::BoundedReader::read_at
/// [`read_exact_at`]: crate::BoundedReader::read_exact_at

#[derive(Debug)]
pub struct Book<R> {
    reader: R,
    header: FileHeader,
    toc: Toc,
}

impl<R> Book<R> {
    /// Return the file's magic number.
    ///
    /// Each BookWriter specifies a magic number, used to identify this file format.
    /// This method returns the value found in the file.
    pub fn magic(&self) -> u32 {
        self.header.user_magic
    }
}

#[cfg(target_family = "unix")]
impl<R> Book<R>
where
    R: std::os::unix::fs::FileExt,
{
    /// Create a shared reader object.
    ///
    /// This returns a BoundedReader that does not implement `Seek` or `Read`, only
    /// [`read_at`] and [`read_exact_at`]
    /// This means it can be used via a shared reference.
    ///
    /// If the `Seek` and `Read` traits are required, use [`exclusive_chapter_reader`] instead.
    ///
    /// [`read_at`]: crate::BoundedReader::read_at
    /// [`read_exact_at`]: crate::BoundedReader::read_exact_at
    /// [`exclusive_chapter_reader`]: Self::exclusive_chapter_reader
    ///
    pub fn chapter_reader<Id>(&self, index: Id) -> Result<BoundedReader<&R>>
    where
        Id: Into<ChapterId>,
    {
        let toc_entry = self.toc.get_chapter(index)?;
        match &toc_entry.span {
            None => {
                // If the span is empty, no IO is necessary; just return
                // an empty Vec.
                Ok(BoundedReader::empty(&self.reader))
            }
            Some(span) => Ok(BoundedReader::new(
                &self.reader,
                span.offset,
                span.length.into(),
            )),
        }
    }

    /// Read all bytes in a chapter.
    ///
    /// This is the same thing as calling [`chapter_reader`] followed by
    /// [`read_exact_at`].
    ///
    /// [`chapter_reader`]: Self::chapter_reader
    /// [`read_exact_at`]: crate::BoundedReader::read_exact_at
    pub fn read_chapter<Id>(&self, index: Id) -> Result<Box<[u8]>>
    where
        Id: Into<ChapterId>,
    {
        let reader = self.chapter_reader(index)?;
        let chapter_len: usize = reader.len().try_into().unwrap();
        let mut buf = vec![0u8; chapter_len];
        reader.read_exact_at(&mut buf, 0)?;
        Ok(buf.into_boxed_slice())
    }
}

impl<R> Book<R>
where
    R: Read + Seek,
{
    /// Create a new Book from a stream.
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
        let buf_reader = &header_buf[..];

        let mut data_src = CborData::new(buf_reader);
        let header: FileHeader = data_src.expect_message()?;

        // Verify magic numbers
        if header.bookwriter_magic != BOOK_V1_MAGIC {
            return Err(BookError::Serializer);
        }

        // Read the TOC length. For v1 it is the last 8 bytes of the file.
        let toc_end = reader.seek(SeekFrom::End(-8))?;
        let toc_len = reader.read_u64::<BigEndian>()?;
        if toc_len > MAX_TOC_SIZE {
            return Err(BookError::Serializer);
        }

        // Deserialize the TOC.
        let toc_offset = toc_end - toc_len;
        let toc_reader = BoundedReader::new(&mut reader, toc_offset, toc_len);
        let mut data_src = CborData::new(toc_reader);
        let toc: Toc = data_src.expect_message()?;

        Ok(Book {
            reader,
            header,
            toc,
        })
    }

    /// Check whether a chapter exists.
    ///
    /// For now, we assume chapter ids are unique. That's dumb,
    /// and will be fixed in a future version.
    pub fn has_chapter<Id>(&self, id: Id) -> bool
    where
        Id: Into<ChapterId>,
    {
        self.toc.get_chapter(id).is_ok()
    }

    /// Read a chapter, with seeking.
    ///
    /// This returns a `BoundedReader` that can read and seek within the chapter
    /// (assuming the underlying Book implements `Read + Seek`).
    /// The `Seek` and `Read` traits require exclusive access. For a shared reader,
    /// use [`chapter_reader`] instead.
    ///
    /// [`chapter_reader`]: Self::chapter_reader
    pub fn exclusive_chapter_reader<Id>(&mut self, id: Id) -> Result<BoundedReader<&mut R>>
    where
        Id: Into<ChapterId>,
    {
        let toc_entry = self.toc.get_chapter(id)?;
        match &toc_entry.span {
            None => {
                // If the span is empty, no IO is necessary; just return
                // an empty Vec.
                Ok(BoundedReader::empty(&mut self.reader))
            }
            Some(span) => {
                self.reader.seek(SeekFrom::Start(span.offset))?;
                Ok(BoundedReader::new(
                    &mut self.reader,
                    span.offset,
                    span.length.into(),
                ))
            }
        }
    }

    /// Read all bytes in a chapter.
    ///
    /// This is the same thing as calling [`exclusive_chapter_reader`]
    /// followed by [`read_to_end`]. It can be used on anything that implements
    /// `Read + Seek`, but as a result it requires exclusive access via a
    /// mutable reference.
    ///
    /// [`exclusive_chapter_reader`]: Self::exclusive_chapter_reader
    ///[`read_to_end`]: std::io::Read::read_to_end
    ///
    pub fn exclusive_read_chapter<Id>(&mut self, index: Id) -> Result<Box<[u8]>>
    where
        Id: Into<ChapterId>,
    {
        let mut buf = vec![];
        let mut reader = self.exclusive_chapter_reader(index)?;
        reader.read_to_end(&mut buf)?;
        Ok(buf.into_boxed_slice())
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
        assert_eq!(cursor.get_ref().len(), 4096 + 9 + 8);

        // If this succeeds then the header and TOC were parsed correctly.
        let _ = Book::new(cursor).unwrap();
    }

    #[test]
    fn truncated_book() {
        let magic = 0x1234;
        let mut cursor = Cursor::new(Vec::<u8>::new());
        {
            let _book = BookWriter::new(&mut cursor, magic).unwrap();
            // We drop the BookWriter without calling close().
        }

        // This file contains only a header (yes, this is invalid).
        assert_eq!(cursor.get_ref().len(), 4096);

        // This should fail, because we are unable to parse the chapter index.
        Book::new(cursor).unwrap_err();
    }

    #[test]
    fn simple_book() {
        let magic = 0x1234;
        let buffer = {
            let buffer = Cursor::new(Vec::<u8>::new());
            let book = BookWriter::new(buffer, magic).unwrap();
            let chapter = book.new_chapter(11);
            let book = chapter.close().unwrap();
            let mut chapter = book.new_chapter(22);
            chapter.write_all(b"This is chapter 22").unwrap();
            let book = chapter.close().unwrap();
            let mut chapter = book.new_chapter("🦀");
            chapter.write_all(b"This is chapter 33").unwrap();
            let book = chapter.close().unwrap();
            book.close().unwrap()
        };
        let mut book = Book::new(buffer).unwrap();
        let ch1 = book.exclusive_read_chapter(11).unwrap();
        assert!(ch1.is_empty());

        assert!(!book.has_chapter(1));

        let ch2 = book.exclusive_read_chapter(22).unwrap();
        assert_eq!(ch2.as_ref(), b"This is chapter 22");

        let ch2 = book.exclusive_read_chapter("🦀").unwrap();
        assert_eq!(ch2.as_ref(), b"This is chapter 33");
    }

    #[test]
    fn book_file_shared() {
        let temp = tempfile::tempfile().unwrap();

        let magic = 0x1234;
        let file = {
            let book = BookWriter::new(temp, magic).unwrap();
            let chapter = book.new_chapter(11);
            let book = chapter.close().unwrap();
            let mut chapter = book.new_chapter(22);
            chapter.write_all(b"This is chapter 22").unwrap();
            let book = chapter.close().unwrap();
            let mut chapter = book.new_chapter("🦀");
            chapter.write_all(b"This is chapter 33").unwrap();
            let book = chapter.close().unwrap();
            book.close().unwrap()
        };
        let book = Book::new(file).unwrap();
        let ch1 = book.read_chapter(11).unwrap();
        assert!(ch1.is_empty());

        assert!(!book.has_chapter(1));

        let ch2 = book.read_chapter(22).unwrap();
        assert_eq!(ch2.as_ref(), b"This is chapter 22");

        let ch2 = book.read_chapter("🦀").unwrap();
        assert_eq!(ch2.as_ref(), b"This is chapter 33");
    }

    #[test]
    fn toc_compat() {
        let mut toc = Vec::new();
        toc.push(TocEntryV1 {
            id: 1234,
            span: Some(FileSpanV1 {
                length: 33.try_into().unwrap(),
                offset: 44,
            }),
        });
        let toc = TocV1(toc);
        let toc = TocV2::from_version(toc);
        assert_eq!(toc.0.len(), 1);
        assert_eq!(
            toc.0[0],
            TocEntryV2 {
                id: Box::new(1234u64.to_be_bytes()),
                span: Some(FileSpanV1 {
                    length: 33.try_into().unwrap(),
                    offset: 44,
                }),
            }
        )
    }
}
