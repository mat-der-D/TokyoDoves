/// Difference between two squares.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Shift {
    /// Horizontal shift. Positive (or negative) direction is on right (or left).
    pub(crate) dh: i8,
    /// Vertical shift. Positive (or negative) direction is on downwards (or upwards).
    pub(crate) dv: i8,
}

impl Shift {
    /// Constructs [`Shift`].
    pub fn new(dv: i8, dh: i8) -> Self {
        Self { dh, dv }
    }

    /// Returns a reference to vertical difference of coordinates.
    pub fn dh(&self) -> &i8 {
        &self.dh
    }

    /// Returns a reference to horizontal difference of coordinates.
    pub fn dv(&self) -> &i8 {
        &self.dv
    }

    /// Returns a mutable reference to vertical difference of coordinates.
    pub fn dh_mut(&mut self) -> &mut i8 {
        &mut self.dh
    }

    /// Returns a mutable reference to horizontal difference of coordinates.
    pub fn dv_mut(&mut self) -> &mut i8 {
        &mut self.dv
    }
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
