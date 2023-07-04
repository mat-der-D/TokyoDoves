use crate::prelude::{Board, BoardBuilder};
use std::io::{BufReader, Read};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Fragment {
    Head(u32),
    Tail(u32),
    Delimiter,
}

#[derive(Debug)]
pub struct FragmentIter<R>
where
    R: Read,
{
    reader: BufReader<R>,
    next_is_head: bool,
}

impl<R> FragmentIter<R>
where
    R: Read,
{
    pub fn new(raw_reader: R) -> Self {
        Self {
            reader: BufReader::new(raw_reader),
            next_is_head: true,
        }
    }

    pub fn try_next(&mut self) -> std::io::Result<Option<Fragment>> {
        let mut buf = [0u8; 4];
        let num_read = self.reader.read(&mut buf)?;
        if num_read != 4 {
            return Ok(None);
        }

        let n = u32::from_be_bytes(buf);
        if n == u32::MAX {
            self.next_is_head = true;
            return Ok(Some(Fragment::Delimiter));
        }

        let ret = if self.next_is_head {
            Fragment::Head(n)
        } else {
            Fragment::Tail(n)
        };
        self.next_is_head = false;
        Ok(Some(ret))
    }
}

impl<R> Iterator for FragmentIter<R>
where
    R: Read,
{
    type Item = Fragment;
    fn next(&mut self) -> Option<Self::Item> {
        self.try_next().unwrap()
    }
}

// ***********************************************************************
//  LazyLoader for Board
// ***********************************************************************
#[derive(Debug)]
pub struct LazyBoardLoader<R>
where
    R: Read,
{
    raw: LazyRawBoardLoader<R>,
}

impl<R> From<LazyRawBoardLoader<R>> for LazyBoardLoader<R>
where
    R: Read,
{
    fn from(raw: LazyRawBoardLoader<R>) -> Self {
        Self { raw }
    }
}

impl<R> LazyBoardLoader<R>
where
    R: Read,
{
    pub fn new(raw_reader: R) -> Self {
        Self {
            raw: LazyRawBoardLoader::new(raw_reader),
        }
    }

    pub fn raw(&self) -> &LazyRawBoardLoader<R> {
        &self.raw
    }

    pub fn raw_mut(&mut self) -> &mut LazyRawBoardLoader<R> {
        &mut self.raw
    }

    pub fn into_raw(self) -> LazyRawBoardLoader<R> {
        self.raw
    }

    pub fn try_next(&mut self) -> std::io::Result<Option<Board>> {
        self.raw
            .try_next()
            .map(|x| x.map(|h| BoardBuilder::from(h).build_unchecked()))
    }
}

impl<R> Iterator for LazyBoardLoader<R>
where
    R: Read,
{
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.try_next().unwrap()
    }
}

// ***********************************************************************
//  LazyLoader for u64
// ***********************************************************************
#[derive(Debug)]
pub struct LazyRawBoardLoader<R>
where
    R: Read,
{
    fragment_iter: FragmentIter<R>,
    head: u64,
}

impl<R> LazyRawBoardLoader<R>
where
    R: Read,
{
    pub fn new(raw_reader: R) -> Self {
        Self {
            fragment_iter: FragmentIter::new(raw_reader),
            head: 0,
        }
    }

    pub fn try_next(&mut self) -> std::io::Result<Option<u64>> {
        let Some(next) = self.fragment_iter.try_next()? else {
            return Ok(None);
        };

        use Fragment::*;
        match next {
            Delimiter => self.try_next(),
            Head(head) => {
                self.head = (head as u64) << 32;
                self.try_next()
            }
            Tail(tail) => Ok(Some(self.head | (tail as u64))),
        }
    }
}

impl<R> Iterator for LazyRawBoardLoader<R>
where
    R: Read,
{
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        self.try_next().unwrap()
    }
}
