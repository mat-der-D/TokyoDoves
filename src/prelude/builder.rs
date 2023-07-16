use std::str::FromStr;

use strum::IntoEnumIterator;

use crate::error;
use crate::prelude::{
    board::{
        main::Board,
        mask::MaskViewer,
        position::{ColorDovePositions, DovePositions},
    },
    pieces::{color_to_index, dove_to_index, try_char_to_color_dove, Color, Dove},
};

/// A builder of [`Board`]
///
/// # Examples
/// ```ignore
/// use tokyodoves::BoardBuilder;
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let board = BoardBuilder::new().build()?;
/// # Ok(())
/// # }
/// ```
///
/// ```ignore
/// use tokyodoves::{BoardBuilder, Color, Dove};
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use Color::*;
/// use Dove::*;
/// let matrix = [
///     [Some((Green, B)), None, None, None],
///     [Some((Red, B)), None, None, None],
///     [None, Some((Red, A)), Some((Green, H)), None],
///     [None, None, None, None],
/// ];
/// let board = BoardBuilder::try_from(matrix)?.build()?;
/// # Ok(())
/// # }
/// ```
///
/// ```ignore
/// use tokyodoves::BoardBuilder;
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let hash = 864761497199312896u64; // Board at the begining
/// let board = BoardBuilder::from(hash).build()?;
/// # Ok(())
/// # }
/// ```
///
/// ```ignore
/// use std::str::FromStr;
/// use tokyodoves::BoardBuilder;
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let board_str = "b   ;B   ; Ah ;    ";
/// // Short-cut version:
/// // let board_str = "b;B; Ah";
/// let board = BoardBuilder::from_str(board_str)?.build()?;
/// # Ok(())
/// # }
/// ```
///
/// ```ignore
/// use tokyodoves::BoardBuilder;
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let board = BoardBuilder::new().build_unchecked();
/// # Ok(())
/// # }
/// ```
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
    pub fn new() -> Self {
        Self::from_u64_bits([[1 << 8, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]])
    }

    pub fn empty() -> Self {
        Self::from_u64_bits([[0; 6]; 2])
    }

    /// Create `BoardBuilder` by indicating positions of doves in `u64` directly.
    ///
    /// It is faster than [`from_u16_bits`](`Self::from_u16_bits`),
    /// but it does not ensure that all doves are included in the 4x4 region.
    pub fn from_u64_bits(positions: [[u64; 6]; 2]) -> Self {
        Self::from(positions)
    }

    /// Create `BoardBuilder` by indicating positions of doves in `u16` directly.
    ///
    /// It ensures that all doves are included in the 4x4 region,
    /// in the cost of conversion from `u16` to `u64`.
    pub fn from_u16_bits(positions: [[u16; 6]; 2]) -> Self {
        Self::from(positions)
    }

    /// Alias of [`try_from::<..>`](`Self::try_from`)
    pub fn try_from_4x4_matrix(
        matrix: [[Option<(Color, Dove)>; 4]; 4],
    ) -> Result<Self, error::Error> {
        Self::try_from(matrix)
    }

    /// Alias of [`from::<u64>`](`Self::from`)
    pub fn from_u64(hash: u64) -> Self {
        Self::from(hash)
    }

    fn position(&self, color: Color, dove: Dove) -> &u64 {
        let icolor = color_to_index(color);
        let idove = dove_to_index(dove);
        // safety is guaranteed because icolor is in 0..2 and idove is in 0..6
        unsafe { self.positions.get_unchecked(icolor).get_unchecked(idove) }
    }

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

    pub fn prune_outside_4x4(&mut self) -> &mut Self {
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

    pub fn build_unchecked(&self) -> Board {
        let viewer = MaskViewer::new();
        let positions = ColorDovePositions::new([
            DovePositions::new(self.positions[0]),
            DovePositions::new(self.positions[1]),
        ]);
        Board::new(viewer, positions)
    }

    pub fn build(&self) -> Result<Board, error::Error> {
        use error::BoardCreateErrorKind::*;

        if self.positions[0][0] == 0 || self.positions[1][0] == 0 {
            return Err(BossNotFound.into());
        }
        let core = 0x0f0f0f0f;
        let mut bit_sum = 0;
        for colored_positions in self.positions {
            for bit in colored_positions {
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
    fn from(bits: [[u64; 6]; 2]) -> Self {
        Self { positions: bits }
    }
}

impl From<[[u16; 6]; 2]> for BoardBuilder {
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
    fn try_from(matrix: [[Option<(Color, Dove)>; 4]; 4]) -> Result<Self, Self::Error> {
        use error::BoardCreateErrorKind::*;

        let mut builder = BoardBuilder::empty();
        for (iv, line) in matrix.iter().enumerate() {
            for (ih, elem) in line.iter().enumerate() {
                if let Some((c, d)) = elem {
                    let pos = builder.position(*c, *d);
                    if *pos != 0 {
                        return Err(DoveDuplicated.into());
                    }
                    builder.put_dove(iv, ih, *c, *d);
                }
            }
        }
        Ok(builder)
    }
}

impl From<u64> for BoardBuilder {
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
                    return Err(DoveDuplicated.into());
                }

                builder.put_dove(pos_v, pos_h, color, dove);
            }
            pos_h += 1;
        }
        Ok(builder)
    }
}
