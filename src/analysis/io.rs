use crate::prelude::{Board, BoardBuilder};
use std::{
    collections::HashSet,
    io::{BufReader, Read},
};

use super::board_set::RawBoardSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Fragment {
    Top(u32),
    Bottom(u32),
    Delimiter,
}

#[derive(Debug)]
pub(crate) struct FragmentIter<R>
where
    R: Read,
{
    reader: BufReader<R>,
    next_is_top: bool,
}

impl<R> FragmentIter<R>
where
    R: Read,
{
    pub fn new(reader: R) -> Self {
        Self {
            reader: BufReader::new(reader),
            next_is_top: true,
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
            self.next_is_top = true;
            return Ok(Some(Fragment::Delimiter));
        }

        let ret = if self.next_is_top {
            Fragment::Top(n)
        } else {
            Fragment::Bottom(n)
        };
        self.next_is_top = false;
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
    pub fn new(reader: R) -> Self {
        Self {
            raw: LazyRawBoardLoader::new(reader),
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
    top: u64,
}

impl<R> From<LazyBoardLoader<R>> for LazyRawBoardLoader<R>
where
    R: Read,
{
    fn from(value: LazyBoardLoader<R>) -> Self {
        value.into_raw()
    }
}

impl<R> LazyRawBoardLoader<R>
where
    R: Read,
{
    pub fn new(reader: R) -> Self {
        Self {
            fragment_iter: FragmentIter::new(reader),
            top: 0,
        }
    }

    pub fn try_next(&mut self) -> std::io::Result<Option<u64>> {
        let Some(next) = self.fragment_iter.try_next()? else {
            return Ok(None);
        };

        use Fragment::*;
        match next {
            Delimiter => self.try_next(),
            Top(top) => {
                self.top = (top as u64) << 32;
                self.try_next()
            }
            Bottom(bottom) => Ok(Some(self.top | (bottom as u64))),
        }
    }

    pub fn contains(self, board: u64) -> std::io::Result<bool> {
        let boards = RawBoardSet::from_iter([board]);
        self.contains_all(boards)
    }

    pub fn contains_all(mut self, mut boards: RawBoardSet) -> std::io::Result<bool> {
        if boards.is_empty() {
            return Ok(true);
        }

        let mut dummy_set = HashSet::new();
        let mut set = &mut dummy_set;
        let dummy_top = 0;
        let mut top_considering = dummy_top;

        loop {
            let Some(next_fragment) = self.fragment_iter.try_next()? else {
                return Ok(boards.is_empty());
            };

            use Fragment::*;
            match next_fragment {
                Delimiter => {
                    if !set.is_empty() {
                        return Ok(false);
                    }
                    if boards.is_empty() {
                        return Ok(true);
                    }
                    set = &mut dummy_set;
                    top_considering = dummy_top;
                }
                Top(top) => {
                    set = &mut dummy_set;
                    if boards.top2bottoms.contains_key(&top) {
                        top_considering = top;
                        set = boards.top2bottoms.get_mut(&top).unwrap();
                    }
                }
                Bottom(bottom) => {
                    if top_considering != dummy_top {
                        set.remove(&bottom);
                        if set.is_empty() {
                            set = &mut dummy_set;
                            top_considering = dummy_top;
                            if boards.is_empty() {
                                return Ok(true);
                            }
                        }
                    }
                }
            }
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
