//! ## Bookfile: an immutable container file format
//!
//! **This crate is still under development.**
//!
//! Bookfile allows creating a file in `Book` format, by writing sequential
//! chapters. A bookfile can be created in streaming mode, making it possible
//! to create a Bookfile while writing it into a network socket or other
//! streaming-only device. Any target supporting `std::io::Write` will work.
//!
//! Each `Chapter` contains a `[u8]` payload.
//!
//! The [`Book`] type represents a read-only Bookfile. Invividual chapters can
//! be read using the `std::io::Read` interface. `Seek` and `read_at` are
//! also provided, and work within the context of that chapter: the seek offset
//! is the offset within the chapter, and a read at the end of the chapter will
//! return EOF.
//!
//! A chapter's offset, length, and id number are all kept in a *Table of Contents*
//! stored at the end of the file. The TOC will be read when a Book is opened,
//! but no chapters will be read until requested.

#![warn(missing_docs)]
#![forbid(unsafe_code)]
#![warn(clippy::cast_possible_truncation)]

use aversion::util::cbor::CborDataError;
use std::io;
use thiserror::Error;

mod book;
#[doc(inline)]
pub use book::{Book, BookWriter, ChapterIndex, ChapterWriter};

mod read;

/// Book error type
#[derive(Debug, Error)]
pub enum BookError {
    /// A `std::io::Error` occurred while reading or writing data.
    #[error("IO Error")]
    Io(Option<io::Error>),
    /// An EOF happened while attempting to read data.
    #[error("Premature EOF")]
    Eof,
    /// An error occurred while serializing or deserializing data.
    #[error("Serialize/Deserialize Error")]
    Serializer,
    /// The requested chapter was not found.
    #[error("Chapter not found")]
    NoChapter,
}

impl From<CborDataError> for BookError {
    fn from(e: CborDataError) -> Self {
        match e {
            CborDataError::Io(opt) => BookError::Io(opt),
            CborDataError::Serializer => BookError::Serializer,
            CborDataError::Eof => BookError::Eof,
        }
    }
}

impl From<io::Error> for BookError {
    fn from(e: io::Error) -> Self {
        BookError::Io(Some(e))
    }
}

/// A Result type for things that may return [`BookError`].
pub type Result<T> = std::result::Result<T, BookError>;
