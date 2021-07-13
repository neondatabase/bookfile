# bookfile

### Bookfile: an immutable container file format

**This crate is still under development.**

Bookfile allows creating a file in `Book` format, by writing sequential
chapters. A bookfile can be created in streaming mode, making it possible
to create a Bookfile while writing it into a network socket or other
streaming-only device. Any target supporting `std::io::Write` will work.

Each chapter contains a `[u8]` payload and is read independently.

The [`Book`] type represents a read-only Bookfile. Invividual chapters can
be read using the `std::io::Read` interface. `Seek` and `read_at` are
also provided, and work within the context of that chapter: the seek offset
is the offset within the chapter, and a read at the end of the chapter will
return EOF.

A chapter's offset, length, and id number are all kept in a *Table of Contents*
stored at the end of the file. The TOC will be read when a Book is opened,
but no chapters will be read until requested.

License: Apache-2.0
