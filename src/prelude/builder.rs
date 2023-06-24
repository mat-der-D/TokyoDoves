use std::str::FromStr;

use strum::IntoEnumIterator;

use super::board::{mask::*, position::*, Board};
use super::error;
use crate::prelude::{Color, Dove};

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
/// let board = BoardBuilder::new().build_unchecked();
/// ```
#[derive(Debug, Clone, Copy)]
pub struct BoardBuilder {
    positions: [[u64; 6]; 2],
}

impl BoardBuilder {
    fn color_to_index(color: Color) -> usize {
        match color {
            Color::Red => 0,
            Color::Green => 1,
        }
    }

    fn dove_to_index(dove: Dove) -> usize {
        use Dove::*;
        match dove {
            B => 0,
            A => 1,
            Y => 2,
            M => 3,
            T => 4,
            H => 5,
        }
    }

    pub fn new() -> Self {
        Self::manual_bits([[1 << 8, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]])
    }

    pub fn empty() -> Self {
        Self::manual_bits([[0; 6]; 2])
    }

    pub fn manual_bits(positions: [[u64; 6]; 2]) -> Self {
        Self { positions }
    }

    /// Alias of [`try_from::<..>`](`Self::try_from`)
    pub fn try_from_4x4_matrix(
        matrix: [[Option<(Color, Dove)>; 4]; 4],
    ) -> Result<Self, error::BoardError> {
        Self::try_from(matrix)
    }

    /// Alias of [`from::<u64>`](`Self::from`)
    pub fn from_hash(hash: u64) -> Self {
        Self::from(hash)
    }

    fn position(&self, color: Color, dove: Dove) -> &u64 {
        let icolor = Self::color_to_index(color);
        let idove = Self::dove_to_index(dove);
        &self.positions[icolor][idove]
    }

    pub fn put_dove(&mut self, pos_v: usize, pos_h: usize, color: Color, dove: Dove) -> &mut Self {
        if pos_v < 4 && pos_h < 4 {
            let pos = 1 << (pos_h + 8 * pos_v);
            let icolor = Self::color_to_index(color);
            let idove = Self::dove_to_index(dove);
            self.positions[icolor][idove] = pos;
        }
        self
    }

    pub fn remove_dove(&mut self, color: Color, dove: Dove) -> &mut Self {
        let icolor = Self::color_to_index(color);
        let idove = Self::dove_to_index(dove);
        self.positions[icolor][idove] = 0;
        self
    }

    pub fn build_unchecked(&self) -> Board {
        let viewer = MaskViewer::new();
        let positions = ColorDovePositions::new([
            DovePositions::new(self.positions[0]),
            DovePositions::new(self.positions[1]),
        ]);
        let board = Board::new(viewer, positions);
        board
    }

    pub fn build(&self) -> Result<Board, error::BoardError> {
        use error::BoardCreateErrorType::*;
        use error::BoardError::*;
        if self.positions[0][0] == 0 || self.positions[1][0] == 0 {
            return Err(BoardCreateError {
                error_type: BossNotFound,
            });
        }
        let mut bit_sum = 0;
        for colored_positions in self.positions {
            for bit in colored_positions {
                if bit & bit_sum != 0 {
                    return Err(BoardCreateError {
                        error_type: PositionDuplicated,
                    });
                }
                bit_sum |= bit;
            }
        }
        let board = self.build_unchecked();
        if board.positions.isolated() {
            return Err(BoardCreateError {
                error_type: DoveIsolated,
            });
        }
        Ok(board)
    }
}

impl TryFrom<[[Option<(Color, Dove)>; 4]; 4]> for BoardBuilder {
    type Error = error::BoardError;
    fn try_from(matrix: [[Option<(Color, Dove)>; 4]; 4]) -> Result<Self, Self::Error> {
        use error::BoardCreateErrorType::*;
        use error::BoardError::*;

        let mut builder = BoardBuilder::empty();
        for (iv, line) in matrix.iter().enumerate() {
            for (ih, elem) in line.iter().enumerate() {
                if let Some((c, d)) = elem {
                    let pos = builder.position(*c, *d);
                    if *pos != 0 {
                        return Err(BoardCreateError {
                            error_type: DoveDuplicated,
                        });
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

        for (id, d) in Dove::iter().enumerate() {
            for (ic, c) in Color::iter().enumerate() {
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
    type Err = error::BoardError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use error::BoardCreateErrorType::*;
        use error::BoardError::*;

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

            if let Ok(dove) = Dove::from_str(&c.to_string()) {
                let color = if c.is_ascii_uppercase() {
                    Color::Red
                } else {
                    Color::Green
                };

                if *builder.position(color, dove) != 0 {
                    return Err(BoardCreateError {
                        error_type: DoveDuplicated,
                    });
                }

                builder.put_dove(pos_v, pos_h, color, dove);
            }
            pos_h += 1;
        }
        Ok(builder)
    }
}
