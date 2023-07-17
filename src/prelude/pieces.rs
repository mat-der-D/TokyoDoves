use strum_macros::EnumIter;

/// Two colors of players.
///
/// It is just like black and white in chess.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, EnumIter)]
pub enum Color {
    Red,
    Green,
}

impl std::fmt::Display for Color {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::ops::Not for Color {
    type Output = Color;
    fn not(self) -> Self::Output {
        use Color::*;
        match self {
            Red => Green,
            Green => Red,
        }
    }
}

/// Six types of doves.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, EnumIter)]
pub enum Dove {
    /// Represents **B**oss-hato,
    /// which can move to adjacent squares in all eight directions,
    /// just like the King in chess.
    /// A player loses when their boss-hato is completely surrounded.
    /// ```text
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// |   | * | * | * |   |
    /// +---+---+---+---+---+
    /// |   | * | B | * |   |
    /// +---+---+---+---+---+
    /// |   | * | * | * |   |
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// ```
    B,
    /// Represents **A**niki-hato,
    /// which can move to adjacent squares in all eight directions,
    /// just like the King in chess.
    /// ```text
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// |   | * | * | * |   |
    /// +---+---+---+---+---+
    /// |   | * | A | * |   |
    /// +---+---+---+---+---+
    /// |   | * | * | * |   |
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// ```
    A,
    /// Represents **Y**aibato,
    /// which can move to four adjacent squares,
    /// forward, backward or sideways,
    /// just like '+'.
    /// ```text
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// |   |   | * |   |   |
    /// +---+---+---+---+---+
    /// |   | * | Y | * |   |
    /// +---+---+---+---+---+
    /// |   |   | * |   |   |
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// ```
    Y,
    /// Represents **M**amedeppo-bato,
    /// which can move to four diagonally adjacent squares,
    /// just like 'x'.
    /// ```text
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// |   | * |   | * |   |
    /// +---+---+---+---+---+
    /// |   |   | M |   |   |
    /// +---+---+---+---+---+
    /// |   | * |   | * |   |
    /// +---+---+---+---+---+
    /// |   |   |   |   |   |
    /// +---+---+---+---+---+
    /// ```
    M,
    /// Represents **T**otsu-hato,
    /// which can move forward, backward or sideways,
    /// through any number of squares,
    /// just like the Rook in chess.
    /// ```text
    /// +---+---+---+---+---+
    /// |   |   | * |   |   |
    /// +---+---+---+---+---+
    /// |   |   | * |   |   |
    /// +---+---+---+---+---+
    /// | * | * | T | * | * |
    /// +---+---+---+---+---+
    /// |   |   | * |   |   |
    /// +---+---+---+---+---+
    /// |   |   | * |   |   |
    /// +---+---+---+---+---+
    /// ```
    T,
    /// Represents **H**ajike-hato,
    /// which can move (or jump) like the Knight in chess.
    /// ```text
    /// +---+---+---+---+---+
    /// |   | * |   | * |   |
    /// +---+---+---+---+---+
    /// | * |   |   |   | * |
    /// +---+---+---+---+---+
    /// |   |   | H |   |   |
    /// +---+---+---+---+---+
    /// | * |   |   |   | * |
    /// +---+---+---+---+---+
    /// |   | * |   | * |   |
    /// +---+---+---+---+---+
    /// ```
    H,
}

#[inline]
pub(crate) fn color_to_index(color: Color) -> usize {
    use Color::*;
    match color {
        Red => 0,
        Green => 1,
    }
}

#[inline]
pub(crate) fn dove_to_index(dove: Dove) -> usize {
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

#[inline]
pub(crate) fn try_index_to_dove(index: usize) -> Option<Dove> {
    use Dove::*;
    let dove = match index {
        0 => B,
        1 => A,
        2 => Y,
        3 => M,
        4 => T,
        5 => H,
        _ => return None,
    };
    Some(dove)
}

/// Converts a pair of [`Color`] and [`Dove`] to [`char`].
///
/// The mapping rule is shown in the table below:
///
/// | `Dove` \ `Color` | `Red` | `Green` |
/// | :-:              | :-:   | :-:     |
/// | `B`              | 'B'   | 'b'     |
/// | `A`              | 'A'   | 'a'     |
/// | `Y`              | 'Y'   | 'y'     |
/// | `M`              | 'M'   | 'm'     |
/// | `T`              | 'T'   | 't'     |
/// | `H`              | 'H'   | 'h'     |
#[inline]
pub fn color_dove_to_char(color: Color, dove: Dove) -> char {
    use Color::*;
    use Dove::*;
    match (color, dove) {
        (Red, B) => 'B',
        (Green, B) => 'b',
        (Red, A) => 'A',
        (Green, A) => 'a',
        (Red, Y) => 'Y',
        (Green, Y) => 'y',
        (Red, M) => 'M',
        (Green, M) => 'm',
        (Red, T) => 'T',
        (Green, T) => 't',
        (Red, H) => 'H',
        (Green, H) => 'h',
    }
}

/// Converts [`char`] to a pair of [`Color`] and [`Dove`].
///
/// The mapping rule is shown in the table below:
///
/// | `Dove` \ `Color` | `Red` | `Green` |
/// | :-:              | :-:   | :-:     |
/// | `B`              | 'B'   | 'b'     |
/// | `A`              | 'A'   | 'a'     |
/// | `Y`              | 'Y'   | 'y'     |
/// | `M`              | 'M'   | 'm'     |
/// | `T`              | 'T'   | 't'     |
/// | `H`              | 'H'   | 'h'     |
///
/// It returns `Some((Color, Dove))` when an appropreate pair is found,
/// otherwise returns `None`.
#[inline]
pub fn try_char_to_color_dove(c: char) -> Option<(Color, Dove)> {
    use Color::*;
    use Dove::*;
    let color_dove = match c {
        'B' => (Red, B),
        'b' => (Green, B),
        'A' => (Red, A),
        'a' => (Green, A),
        'Y' => (Red, Y),
        'y' => (Green, Y),
        'M' => (Red, M),
        'm' => (Green, M),
        'T' => (Red, T),
        't' => (Green, T),
        'H' => (Red, H),
        'h' => (Green, H),
        _ => return None,
    };
    Some(color_dove)
}

#[cfg(test)]
mod tests {
    use crate::strum::IntoEnumIterator;
    use crate::*;

    #[test]
    fn test_color_dove_char() {
        for color in Color::iter() {
            for dove in Dove::iter() {
                let ch = color_dove_to_char(color, dove);
                assert_eq!(Some((color, dove)), try_char_to_color_dove(ch));
            }
        }
    }

    #[test]
    fn test_color_dove_char_irregular() {
        for ch in 'a'..='Z' {
            let Some((color, dove)) = try_char_to_color_dove(ch) else {
                continue;
            };
            assert_eq!(ch, color_dove_to_char(color, dove));
        }
    }

    #[test]
    fn test_dove_index() {
        for dove in Dove::iter() {
            let idx = dove_to_index(dove);
            assert_eq!(Some(dove), try_index_to_dove(idx));
        }
    }

    #[test]
    fn test_dove_index_irregular() {
        for idx in 0..1_000_000 {
            let Some(dove) = try_index_to_dove(idx) else {
                continue;
            };
            assert_eq!(idx, dove_to_index(dove));
        }
    }
}
