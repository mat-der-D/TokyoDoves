use std::str::FromStr;

use strum::IntoEnumIterator;

use crate::prelude::{
    board::{
        main::Board,
        mask::MaskViewer,
        position::{ColorDovePositions, DovePositions},
    },
    pieces::{color_to_index, dove_to_index, try_char_to_color_dove, Color, Dove},
};
use crate::{error, try_index_to_color};

/// A builder of [`Board`].
///
/// This struct provides a variety of ways to construct [`Board`].
/// It creates [`Board`] in two steps:
/// 1. Create a [`BoardBuilder`] object. Edit it if necessary.
/// 2. Call a method to build [`Board`].
///
/// In the first step, all information required to create [`Board`]
/// has to be prepared. The following methods to create [`BoardBuilder`]
/// are supported:
/// - [`new`](`Self::new`)<br>
///     ... creates the builder for the board at the begnining
/// - [`empty`](`Self::empty`)<br>
///     ... creates the builder for the board without any doves (edit needed after construction!)
/// - [`from_str`](`Self::from_str`)<br>
///     ... creates the builder based on string expression.
/// - [`try_from_4x4_matrix`](`Self::try_from_4x4_matrix`)<br>
///     ... creates the builder based on 4x4 matrix (array of array)
/// - [`from_u16_bits`](`Self::from_u16_bits`)<br>
///     ... creates the builder based on `u16` values representing positions of doves
/// - [`from_u64_bits`](`Self::from_u64_bits`)<br>
///     ... creates the builder based on `u64` values representing positions of doves
///
/// The following methods are for editing [`BoardBuilder`]:
/// - [`put_dove`](`Self::put_dove`)<br>
///     ... puts a dove on a position
/// - [`remove_dove`](`Self::remove_dove`)<br>
///     ... removes a dove at a position
/// - [`trim_outside_4x4`](`Self::trim_outside_4x4`)<br>
///     ... removes all doves outside 4x4 region
///
/// In the second step, [`BoardBuilder`] creates [`Board`] by one of the following methods:
/// - [`build`](`Self::build`)<br>
///     ... creates [`Board`] with checking the board to be created are legal.
///     It needs unwrapping to extract [`Board`].
/// - [`build_unchecked`](`Self::build_unchecked`)<br>
///     ... creates [`Board`] without legality check.
///
/// See documentations and examples given to each method for more instructions.
#[derive(Debug, Clone, Copy)]
pub struct BoardBuilder {
    positions: [[u64; 6]; 2],
}

impl Default for BoardBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl BoardBuilder {
    /// Creates the builder to build the board at the beginning of the game.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, BoardBuilder};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board0 = Board::new();
    /// let board1 = BoardBuilder::new().build()?;
    /// let board2 = BoardBuilder::default().build()?;
    /// assert_eq!(board0, board1);
    /// assert_eq!(board0, board2);
    /// # Ok(())
    /// # }
    /// ```
    pub fn new() -> Self {
        Self::from_u64_bits([[1 << 8, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]])
    }

    /// Creates the builder to build the empty board.
    ///
    /// It fails to build unless the status is editted.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, BoardBuilder, Color, Dove};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut builder = BoardBuilder::empty();
    /// assert!(builder.build().is_err());
    /// builder
    ///     .put_dove(0, 0, Color::Green, Dove::B)
    ///     .put_dove(1, 0, Color::Red, Dove::B);
    /// let board = builder.build()?;
    /// assert_eq!(board, Board::new());
    /// # Ok(())
    /// # }
    /// ```
    pub fn empty() -> Self {
        Self::from_u64_bits([[0; 6]; 2])
    }

    /// Creates `BoardBuilder` by indicating positions of doves by one-hot values of `u64`.
    ///
    /// It is faster than the method [`from_u16_bits`](`Self::from_u16_bits`)
    /// because `u64` is more direct expression for internal implementation.
    /// It does not, however, ensure that all doves are included in the 4x4 region.
    ///
    /// Each of elements of `position` indicates the position of each dove.
    /// The below shows which value represents the position of what kinds of dove.
    /// ```text
    /// positions = [
    ///     ['B', 'A', 'Y', 'M', 'T', 'H'],
    ///     ['b', 'a', 'y', 'm', 't', 'h']
    /// ]
    /// ```
    /// Each position is expressed by a one-hot value,
    /// i.e., the value in binary that contains only one "1" bit.
    /// The diagram below shows what value should be used.
    /// ```text
    /// +------+------+------+------+
    /// | 1<<0 | 1<<1 | 1<<2 | 1<<3 |
    /// +------+------+------+------+
    /// | 1<<8 | 1<<9 | 1<<10| 1<<11|
    /// +------+------+------+------+
    /// | 1<<16| 1<<17| 1<<18| 1<<19|
    /// +------+------+------+------+
    /// | 1<<24| 1<<25| 1<<26| 1<<27|
    /// +------+------+------+------+
    /// ```
    /// Values not shown in the above are outside the 4x4 region.
    /// If the dove is not on the board, set 0.
    ///
    /// Note that it does NOT panic even if some element of `position` is not one-hot
    /// or out of the 4x4 region.
    /// Instead, the [`build`](`BoardBuilder::build`) method will return `Err`
    /// without any treatment.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, BoardBuilder};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let bits = [[1 << 8, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]];
    /// let builder = BoardBuilder::from_u64_bits(bits);
    /// // Equivalent:
    /// // let builder = BoardBuilder::from(bits);
    /// let board = builder.build()?;
    /// assert_eq!(board, Board::new());
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_u64_bits(positions: [[u64; 6]; 2]) -> Self {
        Self::from(positions)
    }

    /// Creates `BoardBuilder` by indicating positions of doves by one-hot values of `u16`.
    ///
    /// This method is similar to the [`from_u64_bits`](`Self::from_u64_bits`) method.
    /// This method ensures that all doves are included in the 4x4 region,
    /// in the cost of conversion from `u16` to `u64`.
    ///
    /// Each of elements of `position` indicates the position of each dove.
    /// The below shows which value represents the position of what kinds of dove.
    /// ```text
    /// positions = [
    ///     ['B', 'A', 'Y', 'M', 'T', 'H'],
    ///     ['b', 'a', 'y', 'm', 't', 'h']
    /// ]
    /// ```
    /// Each position is expressed by a one-hot value,
    /// i.e., the value in binary that contains only one "1" bit.
    /// The diagram below shows what value should be used.
    /// ```text
    /// +------+------+------+------+
    /// | 1<<0 | 1<<1 | 1<<2 | 1<<3 |
    /// +------+------+------+------+
    /// | 1<<4 | 1<<5 | 1<<6 | 1<<7 |
    /// +------+------+------+------+
    /// | 1<<8 | 1<<9 | 1<<10| 1<<11|
    /// +------+------+------+------+
    /// | 1<<12| 1<<13| 1<<14| 1<<15|
    /// +------+------+------+------+
    /// ```
    /// If the dove is not on the board, set 0.
    ///
    /// Note that it does NOT panic even if some element of `position` is not one-hot.
    /// Instead, the [`build`](`BoardBuilder::build`) method
    /// will return `Err` without any treatment.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, BoardBuilder};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let bits = [[1 << 4, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]];
    /// let builder = BoardBuilder::from_u16_bits(bits);
    /// // Equivalent:
    /// // let builder = BoardBuilder::from(bits);
    /// let board = builder.build()?;
    /// assert_eq!(board, Board::new());
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_u16_bits(positions: [[u16; 6]; 2]) -> Self {
        Self::from(positions)
    }

    /// Creates `BoardBuilder` from 4x4 matrix of doves, i.e., `[[Option<(Color, Dove)>; 4]; 4]`.
    ///
    /// # Errors
    /// It returns `Err` if the same dove with the same color is included in the matrix.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, BoardBuilder, Color, Dove};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let matrix = [
    ///     [Some((Color::Green, Dove::B)), None, None, None],
    ///     [Some((Color::Red, Dove::B)), None, None, None],
    ///     [None, None, None, None],
    ///     [None, None, None, None],
    /// ];
    /// let builder = BoardBuilder::try_from_4x4_matrix(matrix)?;
    /// // Equivalent:
    /// // let builder = BoardBuilder::try_from(matrix)?;
    /// let board = builder.build()?;
    /// assert_eq!(board, Board::new());
    /// # Ok(())
    /// # }
    /// ```
    pub fn try_from_4x4_matrix(
        matrix: [[Option<(Color, Dove)>; 4]; 4],
    ) -> Result<Self, error::Error> {
        Self::try_from(matrix)
    }

    /// Creates `BoardBuilder` from `u64` expression of [`Board`].
    ///
    /// See the documentation of the method [`to_u64`](`Board::to_u64`) on [`Board`]
    /// for the definition of `u64` expression.
    /// ```rust
    /// use tokyodoves::{Board, BoardBuilder};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let hash = 864761497199312896u64; // Board at the begining
    /// let builder = BoardBuilder::from_u64(hash);
    /// // Equivalent:
    /// // let builder = BoardBuilder::from(hash);
    /// let board = builder.build()?;
    /// assert_eq!(board, Board::new());
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_u64(hash: u64) -> Self {
        Self::from(hash)
    }

    fn position(&self, color: Color, dove: Dove) -> &u64 {
        let icolor = color_to_index(color);
        let idove = dove_to_index(dove);
        // safety is guaranteed because icolor is in 0..2 and idove is in 0..6
        unsafe { self.positions.get_unchecked(icolor).get_unchecked(idove) }
    }

    /// Puts `dove` of the player in `color` on the specified position.
    ///
    /// A position is specified by two arguments `pos_v` and `pos_h`.
    /// The following diagram shows how the square is identified by two values.
    /// ```text
    ///   h 0   1   2   3
    /// v +---+---+---+---+
    /// 0 |   |   |   |   |
    ///   +---+---+---+---+
    /// 1 |   |   | * |   |
    ///   +---+---+---+---+
    /// 2 |   |   |   |   |
    ///   +---+---+---+---+
    /// 3 |   |   |   |   |
    ///   +---+---+---+---+
    /// ```
    /// For example, the square `*` is specified by `pos_v`=1 and `pos_h`=2.
    ///
    /// If both values of `pos_v` and `pos_h` are from 0 to 3,
    /// `color`'s `dove` is put on that position.
    /// If the dove has already exist on the board, it moves to the specified position.
    /// If either of `pos_v` or `pos_h` is greater than 3, nothing is changed.
    ///
    /// This method ignores rules of the game, i.e., for example,
    /// you can put a dove on an isolated position by this method.
    /// The [`build`](`BoardBuilder::build`) method, however, will return `Err`
    /// if the board to be built is illegal.
    ///
    /// # Examples
    /// ```rust
    /// use std::str::FromStr;
    /// use tokyodoves::{Board, BoardBuilder, Color, Dove};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut builder = BoardBuilder::new();
    /// builder.put_dove(2, 1, Color::Red, Dove::A);
    /// // +---+---+---+---+    +---+---+---+---+
    /// // | b |   |   |   |    | b |   |   |   |
    /// // +---+---+---+---+    +---+---+---+---+
    /// // | B |   |   |   |    | B |   |   |   |
    /// // +---+---+---+---+ => +---+---+---+---+
    /// // |   |   |   |   |    |   | A |   |   |
    /// // +---+---+---+---+    +---+---+---+---+
    /// // |   |   |   |   |    |   |   |   |   |
    /// // +---+---+---+---+    +---+---+---+---+
    /// let board = builder.build()?;
    /// let ans = BoardBuilder::from_str("b;B; A")?.build()?;
    /// assert_eq!(board, ans);
    /// # Ok(())
    /// # }
    /// ```
    pub fn put_dove(&mut self, pos_v: usize, pos_h: usize, color: Color, dove: Dove) -> &mut Self {
        if pos_v < 4 && pos_h < 4 {
            let pos = 1 << (pos_h + 8 * pos_v);
            let icolor = color_to_index(color);
            let idove = dove_to_index(dove);
            // safety is guaranteed because icolor is in 0..2 and idove is in 0..6
            unsafe {
                *self
                    .positions
                    .get_unchecked_mut(icolor)
                    .get_unchecked_mut(idove) = pos;
            }
        }
        self
    }

    /// Removes `dove` of the player in `color`.
    ///
    /// This method ignores rules of the game, i.e., for example,
    /// you can remove a boss by this method.
    /// The [`build`](`BoardBuilder::build`) method, however, will return `Err`
    /// if the board to be built is illegal.
    ///
    /// # Examples
    /// ```rust
    /// use std::str::FromStr;
    /// use tokyodoves::{Board, BoardBuilder, Color, Dove};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut builder = BoardBuilder::from_str("bT;B")?;
    /// builder.remove_dove(Color::Red, Dove::T);
    /// let board = builder.build()?;
    /// assert_eq!(board, Board::new());
    /// # Ok(())
    /// # }
    /// ```
    pub fn remove_dove(&mut self, color: Color, dove: Dove) -> &mut Self {
        let icolor = color_to_index(color);
        let idove = dove_to_index(dove);
        // safety is guaranteed because icolor is in 0..2 and idove is in 0..6
        unsafe {
            *self
                .positions
                .get_unchecked_mut(icolor)
                .get_unchecked_mut(idove) = 0;
        }
        self
    }

    /// Removes doves outside 4x4 field.
    ///
    /// # Examples
    /// ```rust
    /// use std::str::FromStr;
    /// use tokyodoves::{Board, BoardBuilder};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let bits = [[1 << 8, 1 << 4, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]];
    /// let mut builder = BoardBuilder::from_u64_bits(bits);
    /// // The above builder corresponds to the below:
    /// // +---+---+---+---+
    /// // | b |   |   |   | A
    /// // +---+---+---+---+
    /// // | B |   |   |   |
    /// // +---+---+---+---+
    /// // |   |   |   |   |
    /// // +---+---+---+---+
    /// // |   |   |   |   |
    /// // +---+---+---+---+
    /// // "A" is outside of the 4x4 field.
    /// assert!(builder.build().is_err());
    /// builder.trim_outside_4x4(); // "A" is trimmed (removed)
    /// let board = builder.build()?;
    /// assert_eq!(board, Board::new());
    /// # Ok(())
    /// # }
    /// ```
    pub fn trim_outside_4x4(&mut self) -> &mut Self {
        let core = 0x0f0f0f0f;
        for icolor in 0..2 {
            for idove in 0..6 {
                // safety is guaranteed because icolor is in 0..2 and idove is in 0..6
                unsafe {
                    *self
                        .positions
                        .get_unchecked_mut(icolor)
                        .get_unchecked_mut(idove) &= core;
                }
            }
        }
        self
    }

    /// Builds [`Board`] based on settings the builder knows without checking.
    ///
    /// It skips all checks the [`build`](`BoardBuilder::build`) method does.
    /// Note that the resulting board may be strange state,
    /// for example, some dove is out of 4x4 region, some dove is isolated or
    /// some boss is not on the field.
    /// This method is more suitable than the [`build`](`BoardBuilder::build`) method
    /// when the validity of the builder is guaranteed by other means
    /// and you want to make the calculation time as short as possible.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, BoardBuilder};
    ///
    /// let builder = BoardBuilder::new();
    /// assert_eq!(builder.build_unchecked(), Board::new());
    /// ```
    pub fn build_unchecked(&self) -> Board {
        let viewer = MaskViewer::new();
        let positions = ColorDovePositions::new([
            DovePositions::new(self.positions[0]),
            DovePositions::new(self.positions[1]),
        ]);
        Board::from_components(viewer, positions)
    }

    /// Builds [`Board`] based on settings the builder knows.
    ///
    /// It checks the following points:
    /// - All positions are single bit or zero
    /// - Both bosses are on the field
    /// - Multiple doves are not in one position
    /// - All doves are in 4x4 region
    /// - No dove is isolated from others
    ///
    /// # Errors
    /// It returns [`Err`] if one of the checks above fails.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, BoardBuilder};
    ///
    /// let builder = BoardBuilder::new();
    /// assert!(matches!(builder.build(), Ok(board) if board == Board::new()));
    /// ```
    pub fn build(&self) -> Result<Board, error::Error> {
        use error::BoardCreateErrorKind::*;

        for icolor in 0..2 {
            if self.positions[icolor][0] == 0 {
                let color = try_index_to_color(icolor).unwrap();
                return Err(BossNotFound(color).into());
            }
        }
        let core = 0x0f0f0f0f;
        let mut bit_sum = 0;
        for colored_positions in self.positions {
            for bit in colored_positions {
                if !matches!(bit.count_ones(), 0 | 1) {
                    return Err(BitNeitherSingleNorZero(self.positions, bit).into());
                }
                if bit & bit_sum != 0 {
                    return Err(PositionDuplicated.into());
                }
                if bit & core != bit {
                    return Err(PositionOutOfRange.into());
                }
                bit_sum |= bit;
            }
        }
        let board = self.build_unchecked();
        if board.positions.isolated() {
            return Err(DoveIsolated.into());
        }
        Ok(board)
    }
}

impl From<[[u64; 6]; 2]> for BoardBuilder {
    /// See the documentation of the [`from_u64_bits`](`Self::from_u64_bits`) method.
    fn from(bits: [[u64; 6]; 2]) -> Self {
        Self { positions: bits }
    }
}

impl From<[[u16; 6]; 2]> for BoardBuilder {
    /// See the documentation of the [`from_u16_bits`](`Self::from_u16_bits`) method.
    fn from(bits: [[u16; 6]; 2]) -> Self {
        fn extend_u16_to_u64(x: u16) -> u64 {
            let mut x_u64 = 0;
            x_u64 |= (x & 0xf) as u64;
            x_u64 |= ((x & 0xf0) as u64) << 4;
            x_u64 |= ((x & 0xf00) as u64) << 8;
            x_u64 |= ((x & 0xf000) as u64) << 12;
            x_u64
        }

        let mut bits_u64 = [[0; 6]; 2];
        for icolor in 0..2 {
            for idove in 0..6 {
                bits_u64[icolor][idove] = extend_u16_to_u64(bits[icolor][idove]);
            }
        }
        Self::from(bits_u64)
    }
}

impl TryFrom<[[Option<(Color, Dove)>; 4]; 4]> for BoardBuilder {
    type Error = error::Error;
    /// See the documentation of the [`try_from_4x4_matrix`](`Self::try_from_4x4_matrix`) method.
    fn try_from(matrix: [[Option<(Color, Dove)>; 4]; 4]) -> Result<Self, Self::Error> {
        use error::BoardCreateErrorKind::*;

        let mut builder = BoardBuilder::empty();
        for (iv, line) in matrix.iter().enumerate() {
            for (ih, elem) in line.iter().enumerate() {
                if let Some((c, d)) = elem {
                    let pos = builder.position(*c, *d);
                    if *pos != 0 {
                        return Err(DoveDuplicated(*c, *d).into());
                    }
                    builder.put_dove(iv, ih, *c, *d);
                }
            }
        }
        Ok(builder)
    }
}

impl From<u64> for BoardBuilder {
    /// See the documentation of the [`from_u64`](`Self::from_u64`) method.
    fn from(hash: u64) -> Self {
        let mut builder = BoardBuilder::empty();
        let mut onoff_mask = 1_u64 << 59;
        let mut pos_mask = 0xf_u64 << 44;

        for d in Dove::iter() {
            let id = dove_to_index(d);
            for c in Color::iter() {
                let ic = color_to_index(c);
                let ishift = 11 - (2 * id + ic);
                if onoff_mask & hash != 0 {
                    let ipos = ((hash & pos_mask) >> (4 * ishift)) as usize;
                    let pos_v = ipos / 4;
                    let pos_h = ipos % 4;
                    builder.put_dove(pos_v, pos_h, c, d);
                }
                onoff_mask >>= 1;
                pos_mask >>= 4;
            }
        }

        builder
    }
}

impl FromStr for BoardBuilder {
    type Err = error::Error;
    /// Creates `BoardBuilder` from a string expression.
    ///
    /// It requires `use std::str::FromStr` to be called.
    ///
    /// # Errors
    /// It returns `Err` if the same dove in the same color is included in the matrix.
    ///
    /// # Examples
    /// The initial board
    /// ```text
    /// +---+---+---+---+
    /// | b |   |   |   |
    /// +---+---+---+---+
    /// | B |   |   |   |
    /// +---+---+---+---+
    /// |   |   |   |   |
    /// +---+---+---+---+
    /// |   |   |   |   |
    /// +---+---+---+---+
    /// ```
    /// can be expressed, for example, as the following.
    /// - `"b   ;B   ;    ;    "`
    /// - `"b---;B---;----;----"`
    /// - `"b-.*;B~/^;_0@z;(=!?"`
    /// - `"b;B"`
    ///
    /// The rules of the string expression:
    /// - Use one character for each dove.
    ///     See the table in the documentation of [`crate::color_dove_to_char`]
    ///     to identify what character is suitable
    /// - Use ";" to separate each row.
    /// - Use some character except those represent some dove or ";"
    ///     to express vacant square.
    ///     (For readability, " " or "-" would be most suitable
    ///     although this method accepts other characters.)
    /// - You can omit the vacant squares between doves and ";" and extra rows.
    ///
    /// Doves outside the 4x4 region are simply ignored.
    ///
    /// ```rust
    /// use std::str::FromStr;
    /// use tokyodoves::{Board, BoardBuilder};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board_strs = [
    ///     "b   ;B   ;    ;    ",
    ///     "b---;B---;----;----",
    ///     "b-.*;B~/^;_0@z;(=!?",
    ///     "b;B",
    ///     "b---;B---T;----;----", // "T" will be ignored because it is outside the 4x4 region
    /// ];
    /// for board_str in board_strs {
    ///     let board = BoardBuilder::from_str(board_str)?.build()?;
    ///     assert_eq!(board, Board::new());
    /// }
    /// # Ok(())
    /// # }
    /// ```
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use error::BoardCreateErrorKind::*;

        let mut builder = BoardBuilder::empty();
        let mut pos_v = 0;
        let mut pos_h = 0;

        let delimiter = ';';
        for c in s.chars() {
            if c == delimiter {
                pos_h = 0;
                pos_v += 1;
                continue;
            }

            if let Some((color, dove)) = try_char_to_color_dove(c) {
                if *builder.position(color, dove) != 0 {
                    return Err(DoveDuplicated(color, dove).into());
                }

                builder.put_dove(pos_v, pos_h, color, dove);
            }
            pos_h += 1;
        }
        Ok(builder)
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test_single_bit() {
        let positions = [[256, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0]];
        let builder = BoardBuilder::from_u64_bits(positions);
        let result = builder.build();
        assert!(result.is_err());
        use error::BoardCreateErrorKind::*;
        use error::BoardError::*;
        assert!(matches!(
            result.unwrap_err().as_board_error().unwrap(),
            BoardCreateError {
                kind: BitNeitherSingleNorZero(_, _),
            }
        ));
    }
}
