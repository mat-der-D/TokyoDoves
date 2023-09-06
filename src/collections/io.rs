use crate::{
    collections::board_set::{BoardSet, RawBoardSet},
    prelude::{Board, BoardBuilder},
};
use std::{
    collections::HashSet,
    io::{BufReader, Read},
};

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
/// A utility to load [`Board`]s in a lazy way from the binary file
/// saved by the [`save`](`BoardSet::save`) method of [`BoardSet`].
///
/// This struct has an internal [`LazyRawBoardLoader`],
/// which is an iterator of `u64`s.
/// The relation between two structs are similar to the one
/// between [`BoardSet`] and [`RawBoardSet`].
///
/// It panics on iteration if some io error occurs in the process.
/// To handle those errors,
/// call the [`try_next`](`LazyBoardLoader::try_next`) method in a loop block.
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
    /// Creates an lazy loader.
    ///
    /// # Examples
    /// ``` ignore
    /// use std::fs::File;
    /// use tokyodoves::collections::LazyBoardLoader;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let path = "/some/path.tdl";
    /// for board in LazyBoardLoader::new(File::open(path)?) {
    ///     println!("{board}");
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub fn new(reader: R) -> Self {
        Self {
            raw: LazyRawBoardLoader::new(reader),
        }
    }

    /// Returns a reference to the internal [`LazyRawBoardLoader`].
    ///
    /// # Examples
    /// ``` ignore
    /// use std::fs::File;
    /// use tokyodoves::collections::LazyBoardLoader;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let path = "/some/path.tdl";
    /// let lazy_loader = LazyBoardLoader::new(File::open(path)?);
    /// let raw_loader = lazy_loader.raw();
    /// # Ok(())
    /// # }
    /// ```
    pub fn raw(&self) -> &LazyRawBoardLoader<R> {
        &self.raw
    }

    /// Returns a reference to the internal [`LazyRawBoardLoader`].
    ///
    /// # Examples
    /// ``` ignore
    /// use std::fs::File;
    /// use tokyodoves::collections::LazyBoardLoader;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let path = "/some/path.tdl";
    /// let lazy_loader = LazyBoardLoader::new(File::open(path)?);
    /// for hash in lazy_loader.raw_mut() {
    ///     println!("{hash}");
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub fn raw_mut(&mut self) -> &mut LazyRawBoardLoader<R> {
        &mut self.raw
    }

    /// Returns the internal [`LazyRawBoardLoader`].
    ///
    /// # Examples
    /// ``` ignore
    /// use std::fs::File;
    /// use tokyodoves::collections::LazyBoardLoader;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let path = "/some/path.tdl";
    /// let lazy_loader = LazyBoardLoader::new(File::open(path)?);
    /// for hash in lazy_loader.into_raw() {
    ///     println!("{hash}");
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub fn into_raw(self) -> LazyRawBoardLoader<R> {
        self.raw
    }

    /// Returns the next item on iteration.
    ///
    /// # Errors
    /// It returns `Err` if some io error occurs.
    ///
    /// # Examples
    /// ``` ignore
    /// use std::fs::File;
    /// use tokyodoves::collections::LazyBoardLoader;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let path = "/some/path.tdl";
    /// let mut lazy_loader = LazyBoardLoader::new(File::open(path)?);
    /// let next_item = lazy_loader.try_next();
    /// # Ok(())
    /// # }
    /// ```
    pub fn try_next(&mut self) -> std::io::Result<Option<Board>> {
        self.raw
            .try_next()
            .map(|x| x.map(|h| BoardBuilder::from(h).build_unchecked()))
    }

    /// Checks if the specified board is contained in a lazy way.
    ///
    /// This method consumes `self`.
    ///
    /// # Example
    /// ``` ignore
    /// use std::fs::File;
    /// use tokyodoves::Board;
    /// use tokyodoves::collections::LazyBoardLoader;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let path = "/some/path.tdl";
    /// let lazy_loader = LazyBoardLoader::new(File::open(path)?);
    /// println!("{:?}", lazy_loader.contains(Board::new()));
    /// # Ok(())
    /// # }
    /// ```
    pub fn contains(self, board: Board) -> std::io::Result<bool> {
        self.into_raw().contains(board.to_u64())
    }

    /// Checks if all boards in the set are contained in a lazy way.
    ///
    /// This method consumes `self`.
    ///
    /// # Errors
    /// It returns `Err` if some io error occurs.
    ///
    /// # Example
    /// ``` ignore
    /// use std::fs::File;
    /// use tokyodoves::Board;
    /// use tokyodoves::collections::{LazyBoardLoader, BoardSet};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let path = "/some/path.tdl";
    /// let lazy_loader = LazyBoardLoader::new(File::open(path)?);
    /// let mut set = BoardSet::new();
    /// set.insert(Board::new());
    /// println!("{:?}", lazy_loader.contains_all(&set));
    /// # Ok(())
    /// # }
    /// ```
    pub fn contains_all(self, set: &BoardSet) -> std::io::Result<bool> {
        self.into_raw().contains_all(set.raw())
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
/// A struct almost the same as [`LazyBoardLoader`],
/// except that it loads `u64` expressions of [`Board`]s instead.
///
/// It panics on iteration if some io error occurs in the process.
/// To handle those errors,
/// call the [`try_next`](`LazyRawBoardLoader::try_next`) method in a loop block.
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
    /// Creates an lazy loader.
    ///
    /// # Examples
    /// ``` ignore
    /// use std::fs::File;
    /// use tokyodoves::collections::LazyRawBoardLoader;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let path = "/some/path.tdl";
    /// for hash in LazyRawBoardLoader::new(File::open(path)?) {
    ///     println!("{hash}");
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub fn new(reader: R) -> Self {
        Self {
            fragment_iter: FragmentIter::new(reader),
            top: 0,
        }
    }

    /// Returns the next item on iteration.
    ///
    /// # Errors
    /// It returns `Err` if some io error occurs.
    ///
    /// # Examples
    /// ``` ignore
    /// use std::fs::File;
    /// use tokyodoves::collections::LazyRawBoardLoader;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let path = "/some/path.tdl";
    /// let mut lazy_loader = LazyRawBoardLoader::new(File::open(path)?);
    /// let next_item = lazy_loader.try_next();
    /// # Ok(())
    /// # }
    /// ```
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

    /// Checks if the specified `u64` is contained in a lazy way.
    ///
    /// This method consumes `self`.
    ///
    /// # Example
    /// ``` ignore
    /// use std::fs::File;
    /// use tokyodoves::Board;
    /// use tokyodoves::collections::LazyBoardLoader;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let path = "/some/path.tdl";
    /// let lazy_loader = LazyRawBoardLoader::new(File::open(path)?);
    /// println!("{:?}", lazy_loader.contains(Board::new().to_u64()));
    /// # Ok(())
    /// # }
    /// ```
    pub fn contains(self, hash: u64) -> std::io::Result<bool> {
        let boards = RawBoardSet::from_iter([hash]);
        self.contains_all(&boards)
    }

    /// Checks if all `u64`s in the set are contained in a lazy way.
    ///
    /// This method consumes `self`.
    ///
    /// # Errors
    /// It returns `Err` if some io error occurs.
    ///
    /// # Example
    /// ``` ignore
    /// use std::fs::File;
    /// use tokyodoves::Board;
    /// use tokyodoves::collections::{LazyRawBoardLoader, RawBoardSet};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let path = "/some/path.tdl";
    /// let lazy_loader = LazyRawBoardLoader::new(File::open(path)?);
    /// let mut set = RawBoardSet::new();
    /// set.insert(Board::new().to_u64());
    /// println!("{:?}", lazy_loader.contains_all(&set));
    /// # Ok(())
    /// # }
    /// ```
    pub fn contains_all(mut self, set: &RawBoardSet) -> std::io::Result<bool> {
        if set.is_empty() {
            return Ok(true);
        }

        let mut dummy_set = HashSet::new();
        let mut bottoms_considering = &mut dummy_set;
        let dummy_top = 0;
        let mut top_considering = dummy_top;

        loop {
            let Some(next_fragment) = self.fragment_iter.try_next()? else {
                return Ok(set.is_empty());
            };

            use Fragment::*;
            match next_fragment {
                Delimiter => {
                    if !bottoms_considering.is_empty() {
                        return Ok(false);
                    }
                    bottoms_considering = &mut dummy_set;
                    top_considering = dummy_top;
                }
                Top(top) => {
                    top_considering = dummy_top;
                    bottoms_considering = &mut dummy_set;

                    if set.top2bottoms.contains_key(&top) {
                        let set = set.top2bottoms.get_mut(&top).unwrap();
                        if !set.is_empty() {
                            bottoms_considering = set;
                            top_considering = top;
                        }
                    }
                }
                Bottom(bottom) => {
                    if top_considering == dummy_top {
                        continue;
                    }
                    bottoms_considering.remove(&bottom);
                    if !bottoms_considering.is_empty() {
                        continue;
                    }
                    bottoms_considering = &mut dummy_set;
                    top_considering = dummy_top;
                    if set.is_empty() {
                        return Ok(true);
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
