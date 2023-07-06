mod actions;
pub(crate) mod board;
mod builder;
mod game;
mod macros;
mod pieces;

pub mod error;
pub use actions::*;
pub use board::*;
pub use builder::*;
pub use game::*;
pub use pieces::*;

/// Difference between two squares.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Shift {
    /// Horizontal shift. Positive (or negative) direction is on right (or left).
    pub dh: i8,
    /// Vertical shift. Positive (or negative) direction is on downwards (or upwards).
    pub dv: i8,
}

impl std::ops::Add for Shift {
    type Output = Shift;
    fn add(self, rhs: Self) -> Self::Output {
        Shift {
            dh: self.dh + rhs.dh,
            dv: self.dv + rhs.dv,
        }
    }
}

impl std::ops::Neg for Shift {
    type Output = Shift;
    fn neg(self) -> Self::Output {
        Shift {
            dh: -self.dh,
            dv: -self.dv,
        }
    }
}

impl std::ops::Sub for Shift {
    type Output = Shift;
    fn sub(self, rhs: Self) -> Self::Output {
        Shift {
            dh: self.dh - rhs.dh,
            dv: self.dv - rhs.dv,
        }
    }
}
