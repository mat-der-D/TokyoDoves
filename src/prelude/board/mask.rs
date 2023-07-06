//! Bit-mask utility [`BitMask`] and viewer to it [`MaskViewer`].
//!
//! This module consists of [`BitMask`] and [`MaskViewer`].
//! More explanations are needed.
use array_macro::array;
use strum_macros::EnumIter;

use crate::prelude::{error, macros};

const MASKS: [BitMask; 64] = {
    let mask0 = BitMask::new();
    array![n => mask0.rotate_left_all(n as u32); 64]
};

/// Constant masks used by many kinds of bit-wise manupulation.
#[derive(Debug, Clone)]
pub struct BitMask {
    /// Represents 4x4 main region.
    ///
    /// # Examples
    ///
    /// ```text
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// ```
    pub core: u64,
    /// Outside of the union of main region and 1-bit margin.
    ///
    /// # Examples
    ///
    /// ```text
    /// 1 1 1 1 1 1 1 1
    /// 1 0 0 0 0 0 0 1
    /// 1 0 0 0 0 0 0 1
    /// 1 0 0 0 0 0 0 1
    /// 1 0 0 0 0 0 0 1
    /// 1 0 0 0 0 0 0 1
    /// 1 0 0 0 0 0 0 1
    /// 1 1 1 1 1 1 1 1
    /// ```
    pub outfield: u64,
    /// Masks used to examine the direction exerted by a bit on the margin.
    ///
    /// For details, see the implementation of
    /// the method [`target_bit_to_direction`](`BitMask::target_bit_to_direction`).
    ///
    /// # Examples
    ///
    /// ```text
    /// [0] W + NE + N + NW
    /// 0 0 0 0 0 0 0 0
    /// 0 1 1 1 1 1 1 0
    /// 0 1 0 0 0 0 0 0
    /// 0 1 0 0 0 0 0 0
    /// 0 1 0 0 0 0 0 0
    /// 0 1 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    ///
    /// [1] SW + E + N + NW
    /// 0 0 0 0 0 0 0 0
    /// 0 1 1 1 1 1 0 0
    /// 0 0 0 0 0 0 1 0
    /// 0 0 0 0 0 0 1 0
    /// 0 0 0 0 0 0 1 0
    /// 0 0 0 0 0 0 1 0
    /// 0 1 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    ///
    /// [2] S + E + NE + NW
    /// 0 0 0 0 0 0 0 0
    /// 0 1 0 0 0 0 1 0
    /// 0 0 0 0 0 0 1 0
    /// 0 0 0 0 0 0 1 0
    /// 0 0 0 0 0 0 1 0
    /// 0 0 0 0 0 0 1 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 0 0 0 0 0 0
    /// ```
    pieces: [u64; 3],
    /// Masks used to determine if there are walls.
    ///
    /// For details, see the implementation of the method [`BitMask::calc_wall_bits`].
    ///
    /// # Examples
    ///
    /// ```text
    /// [0]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    ///
    /// [1]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 1 0 0
    /// 0 0 0 0 0 1 0 0
    /// 0 0 0 0 0 1 0 0
    /// 0 0 0 0 0 1 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    ///
    /// [2]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 0 0 0 0 0
    /// 0 0 1 0 0 0 0 0
    /// 0 0 1 0 0 0 0 0
    /// 0 0 1 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    ///
    /// [3]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// ```
    edges: [u64; 4], // n, e, w, s
    /// Masks used to create walls.
    ///
    /// For details, see the implementation of the method [`calc_wall_bits`](`BitMask::calc_wall_bits`).
    ///
    /// # Examples
    ///
    /// ```text
    /// [0]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 0 0 0 0 0 0
    ///
    /// [1]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 1 0 0 0 0 1 0
    /// 0 1 0 0 0 0 1 0
    /// 0 1 0 0 0 0 1 0
    /// 0 1 0 0 0 0 1 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// ```
    walls: [u64; 2], // ns, ew
    /// # Examples
    ///
    /// ```text
    /// [0]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 1
    /// 1 1 1 0 0 0 0 1
    /// 1 1 1 0 0 0 0 1
    /// 1 1 1 0 0 0 0 1
    /// 1 1 1 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    ///
    /// [1]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 1 1 1 1 0 0 0 0
    /// 1 1 1 1 0 0 0 0
    /// 1 1 1 1 0 0 0 0
    /// 1 1 1 1 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    ///
    /// [2]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 1 1 1 1 0 0 0
    /// 0 1 1 1 1 0 0 0
    /// 0 1 1 1 1 0 0 0
    /// 0 1 1 1 1 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// ```
    for_hmin: [u64; 3],
    /// # Examples
    ///
    /// ```text
    /// [0]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 1 1 1
    /// 1 0 0 0 0 1 1 1
    /// 1 0 0 0 0 1 1 1
    /// 1 0 0 0 0 1 1 1
    /// 1 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    ///
    /// [1]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 1 1 1 1
    /// 0 0 0 0 1 1 1 1
    /// 0 0 0 0 1 1 1 1
    /// 0 0 0 0 1 1 1 1
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    ///
    /// [2]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 1 1 1 1 0
    /// 0 0 0 1 1 1 1 0
    /// 0 0 0 1 1 1 1 0
    /// 0 0 0 1 1 1 1 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// ```
    for_hmax: [u64; 3],
    /// # Examples
    ///
    /// ```text
    /// [0]
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 1 1 1 0 0
    ///
    /// [1]
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    ///
    /// [2]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// ```
    for_vmin: [u64; 3],
    /// # Examples
    ///
    /// ```text
    /// [0]
    /// 0 0 1 1 1 1 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    ///
    /// [1]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    ///
    /// [2]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 0 0 0 0 0 0
    /// ```
    for_vmax: [u64; 3],
    /// # Examples
    ///
    /// ```text
    /// [0]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    ///
    /// [1]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 1 1 1 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    ///
    /// [2]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 1 0 0 0 0
    /// 0 0 1 1 0 0 0 0
    /// 0 0 1 1 0 0 0 0
    /// 0 0 1 1 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    ///
    /// [3]
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 1 0 1 0 0 0
    /// 0 0 1 0 1 0 0 0
    /// 0 0 1 0 1 0 0 0
    /// 0 0 1 0 1 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// 0 0 0 0 0 0 0 0
    /// ```
    for_idx: [u64; 4],
}

impl BitMask {
    const fn new() -> Self {
        let core = 0x000000000f0f0f0f_u64;
        let outfield = 0x607fffe060606060_u64;
        let pieces = [
            0x0000001f90101010_u64,
            0x9000001f00808080_u64,
            0x8f00001080808080_u64,
        ];
        let edges = [
            0x000000000f000000_u64, // n
            0x0000000001010101_u64, // e
            0x0000000008080808_u64, // w
            0x000000000000000f_u64, // s
        ];
        let walls = [
            0x0f00000f00000000_u64, // ns
            0x8000000010909090_u64, // ew
        ];

        let for_hmin = array![n => core.rotate_left(3 - n as u32); 3];
        let for_hmax = array![n => core.rotate_right(3 - n as u32); 3];
        let for_vmin = array![n => core.rotate_left(8 * (3 - n) as u32); 3];
        let for_vmax = array![n => core.rotate_right(8 * (3 - n) as u32); 3];

        let for_idx = [
            0x0f0f0000_u64,
            0x0f000f00_u64,
            0x0c0c0c0c_u64,
            0x0a0a0a0a_u64,
        ];

        Self {
            core,
            outfield,
            pieces,
            edges,
            walls,
            for_hmin,
            for_hmax,
            for_vmin,
            for_vmax,
            for_idx,
        }
    }

    /// Returns [`BitMask`] created by applying [`u64::rotate_left`] to all bit-masks of `self`.
    const fn rotate_left_all(&self, n: u32) -> Self {
        const fn _make_rotated<const N: usize>(base: &[u64; N], n: u32) -> [u64; N] {
            let mut ret = [0; N];
            macros::for_loop!(let mut i = 0; i < N; i += 1 => {
                ret[i] = base[i].rotate_left(n);
            });
            ret
        }

        macro_rules! define_rotated {
            ($($field:ident),*) => {
                $(let $field = _make_rotated(&self.$field, n);)*
            };
        }

        let core = self.core.rotate_left(n);
        let outfield = self.outfield.rotate_left(n);
        define_rotated!(pieces, edges, walls, for_hmin, for_hmax, for_vmin, for_vmax, for_idx);

        Self {
            core,
            outfield,
            pieces,
            edges,
            walls,
            for_hmin,
            for_hmax,
            for_vmin,
            for_vmax,
            for_idx,
        }
    }

    /// Returns `bit`'s index value, which is assigned to each square
    /// in 4x4 main region.
    ///
    /// Index values are as below:
    /// ```text
    /// +----+----+----+----+
    /// | 15 | 14 | 13 | 12 |
    /// +----+----+----+----+
    /// | 11 | 10 |  9 |  8 |
    /// +----+----+----+----+
    /// |  7 |  6 |  5 |  4 |
    /// +----+----+----+----+
    /// |  3 |  2 |  1 |  0 |
    /// +----+----+----+----+
    /// ```
    /// If `bit` is out of main region, it returns `None`.
    pub fn field_idx(&self, bit: u64) -> Option<usize> {
        if bit & self.core != bit {
            return None;
        }
        let mut idx = 0_usize;
        for mask in self.for_idx.into_iter() {
            idx <<= 1;
            if bit & mask == bit {
                idx += 1;
            }
        }
        Some(idx)
    }

    /// Infer the direction on which the [`MaskViewer`] has to shift
    /// based on the bit of next position. If viewer should not shift,
    /// it returns `Ok(None)`.
    ///
    /// The structure of elements of `pieces` of [`BitMask`] is as follows:
    /// ```text
    /// [0] W + NE + N + NW
    /// [1] SW + E + N + NW
    /// [2] S + E + NE + NW
    /// ```
    /// The information that the specified `bit` intersects with which element
    /// determines which direction `bit` belongs to.
    /// Specifically, the association below works:
    /// ```text
    ///         [0][1][2]
    /// SE -> 0b 0  0  0
    /// S  -> 0b 0  0  1
    /// SW -> 0b 0  1  0
    /// E  -> 0b 0  1  1
    /// W  -> 0b 1  0  0
    /// NE -> 0b 1  0  1
    /// N  -> 0b 1  1  0
    /// NW -> 0b 1  1  1
    /// ```
    fn target_bit_to_direction(
        &self,
        target_bit: u64,
    ) -> Result<Option<Direction>, error::DirectionError> {
        if target_bit & self.core == target_bit {
            return Ok(None);
        }
        if target_bit & self.outfield == target_bit {
            return Err(error::DirectionError::BitOutOfField(target_bit));
        }

        let mut idx = 0_usize;
        for piece in self.pieces.into_iter() {
            idx <<= 1;
            if target_bit & piece == target_bit {
                idx += 1;
            }
        }

        let direction = Direction::try_from(idx)?;
        Ok(Some(direction))
    }

    /// Calculates bits of walls based on `bits`.
    pub fn calc_wall_bits(&self, bits: u64) -> u64 {
        let mut wall_bits = 0;

        // H-wall
        if (bits & self.edges[0] != 0) && (bits & self.edges[3] != 0) {
            wall_bits |= self.walls[0];
        }

        // V-wall
        if (bits & self.edges[1] != 0) && (bits & self.edges[2] != 0) {
            wall_bits |= self.walls[1];
        }

        wall_bits
    }

    /// Calculates the minimum rectangle that contains `bits`.
    ///
    /// See the documents given to [`super::Board::minimum_rectangle`].
    pub fn minimum_rectangle(&self, bits: u64) -> Rectangle {
        macro_rules! calc_edge {
            ($field:ident, $default:expr, $i:ident, $eval:expr) => {{
                let mut val = $default;
                for ($i, m) in self.$field.into_iter().enumerate() {
                    if bits & m == bits {
                        val = $eval;
                        break;
                    }
                }
                val
            }};
        }

        let hmin = calc_edge!(for_hmin, 0, i, 3 - i);
        let hmax = calc_edge!(for_hmax, 3, i, i);
        let vmin = calc_edge!(for_vmin, 0, i, 3 - i);
        let vmax = calc_edge!(for_vmax, 3, i, i);

        Rectangle {
            hmin,
            hmax,
            vmin,
            vmax,
        }
    }
}

/// Rectangle with edges of [`usize`] coordinates.
///
/// This struct is used to describe the minimum rectangle
/// that contains all doves on the field.
/// Fields stand for coordinates of edges of the rectangle.
/// # Examples
/// Case 1
/// ```text
///     0   1   2   3
///   +---+---+---+---+
/// 0 | b |   | T |   |
///   +---+---+---+---+
/// 1 |   | B | a |   |
///   +---+---+---+---+
/// 2 |   |   |   |   |
///   +---+---+---+---+
/// 3 |   |   |   |   |
///   +---+---+---+---+
/// -> hmin=0, hmax=2, vmin=0, vmax=1
/// ```
/// Case 2
/// ```text
///     0   1   2   3
///   +---+---+---+---+
/// 0 |   |   |   |   |
///   +---+---+---+---+
/// 1 |   | b |   |   |
///   +---+---+---+---+
/// 2 | a |   | H | B |
///   +---+---+---+---+
/// 3 |   |   |   |   |
///   +---+---+---+---+
/// -> hmin=0, hmax=3, vmin=1, vmax=2
/// ```
/// Case 3
/// ```text
///     0   1   2   3
///   +---+---+---+---+
/// 0 |   |   |   |   |
///   +---+---+---+---+
/// 1 |   |   |   |   |
///   +---+---+---+---+
/// 2 |   |   |   |   |
///   +---+---+---+---+
/// 3 | h | B | b | Y |
///   +---+---+---+---+
/// -> hmin=0, hmax=3, vmin=3, vmax=3
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Rectangle {
    /// The minimum coordinate in horizontal direction
    pub hmin: usize,
    /// The maximum coordinate in horizontal direction
    pub hmax: usize,
    /// The minimum coordinate in vertical direction
    pub vmin: usize,
    /// The maximum coordinate in vertical direction
    pub vmax: usize,
}

/// A struct to represent the lengths of edges of [`Rectangle`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RectangleSize {
    /// The length of the horizontal edge
    pub hsize: usize,
    /// The length of the vertical edge
    pub vsize: usize,
}

impl Rectangle {
    /// Calculates the lengths of horizontal and vertical edges.
    pub fn size(&self) -> RectangleSize {
        let hsize = self.hmax - self.hmin + 1;
        let vsize = self.vmax - self.vmin + 1;
        RectangleSize { hsize, vsize }
    }
}

#[derive(Debug, Clone, Copy, EnumIter)]
pub(crate) enum Direction {
    /// South-East
    SE,
    /// South
    S,
    /// South-West
    SW,
    /// East
    E,
    /// West
    W,
    /// North-East
    NE,
    /// North
    N,
    /// North-West
    NW,
}

impl TryFrom<usize> for Direction {
    type Error = error::DirectionError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        use Direction::*;
        let direction = match value {
            0 => SE,
            1 => S,
            2 => SW,
            3 => E,
            4 => W,
            5 => NE,
            6 => N,
            7 => NW,
            _ => return Err(error::DirectionError::IndexOutOfRange(value)),
        };
        Ok(direction)
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct MaskViewer {
    status: usize,
}

impl MaskViewer {
    pub fn new() -> Self {
        Self { status: 0 }
    }

    pub fn view_mask(&self) -> &BitMask {
        // safety is guaranteed because self.status can be changed only via do_shift
        unsafe { MASKS.get_unchecked(self.status) }
    }

    pub(crate) fn view_next_mask(&self, d: Direction) -> &BitMask {
        // safety is guaranteed because the turned value of Self::shift_status ranges from 0 to 63
        let next_status = Self::shift_status(self.status, d);
        unsafe { MASKS.get_unchecked(next_status) }
    }

    /// Get a (reference to) [`BitMask`] that contains `bit`
    /// without changing internal index (differently from [`shift_toward`](`Self::shift_toward`)).
    pub(crate) fn view_mask_at(&self, bit: u64) -> Result<&BitMask, error::DirectionError> {
        match self.view_mask().target_bit_to_direction(bit)? {
            Some(d) => Ok(self.view_next_mask(d)),
            None => Ok(self.view_mask()),
        }
    }

    /// Changes the reference to constant [`BitMask`] so that
    /// the `core` of new [`BitMask`] contains the specified `bit`.
    pub(crate) fn shift_toward(&mut self, bit: u64) -> Result<(), error::DirectionError> {
        if let Some(d) = self.view_mask().target_bit_to_direction(bit)? {
            self.do_shift(d);
        }
        Ok(())
    }

    fn do_shift(&mut self, d: Direction) {
        self.status = Self::shift_status(self.status, d);
    }

    fn shift_status(status: usize, d: Direction) -> usize {
        use Direction::*;
        let x = match d {
            SE => 55,
            S => 56,
            SW => 57,
            E => 63,
            W => 1,
            NE => 7,
            N => 8,
            NW => 9,
        };
        (status + x) % 64
    }
}
