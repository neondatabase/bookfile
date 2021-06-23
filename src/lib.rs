//! Bookfile: an immutable container file format
//!
//! Bookfile allows creating a file in `Book` format, by writing sequential chapters.
//! A bookfile can be created in streaming mode, making it possible to
//! Create a Bookfile while writing it into a network socket or other
//! streaming-only device. Any target supporting `std::io::Write` will work.
//!
//! Each `Chapter` contains a `[u8]` payload.
//!
//! The `Book` type represents a read-only Bookfile. It can read individual chapters
//! by seeking to their offset, and reads will end where the chapter ends.
//!
//! A chapter's offset, length, and id number are all kept in a *Table of Contents*
//! stored at the end of the file. The TOC will be read when a Book is opened,
//! but no chapters will be read until requested.

use std::io;
use thiserror::Error;

mod book;
#[doc(inline)]
pub use book::{Book, BookWriter, ChapterWriter};

mod read;

/// Book error type
#[derive(Debug, Error)]
pub enum BookError {
    #[error("IO Error")]
    Io(Option<io::Error>),
    #[error("Premature EOF")]
    Eof,
    #[error("Serialize/Deserialize Error")]
    Serializer,
    #[error("Chapter not found")]
    NoChapter,
}

impl From<serde_cbor::Error> for BookError {
    fn from(e: serde_cbor::Error) -> Self {
        use serde_cbor::error::Category;

        match e.classify() {
            Category::Io => BookError::Io(None),
            Category::Syntax => BookError::Serializer,
            Category::Data => BookError::Serializer,
            Category::Eof => BookError::Eof,
        }
    }
}

impl From<io::Error> for BookError {
    fn from(e: io::Error) -> Self {
        BookError::Io(Some(e))
    }
}

// A Result type for things that may return [`BookError`].
pub type Result<T> = std::result::Result<T, BookError>;
