//! Move rules of each dove

use array_macro::array;

use super::bitutil;
use crate::prelude::{macros, Dove, Shift};

const BIT_ROUTE_SHIFTS: [TargetBitRouteShift; 64] = {
    array![
        n => TargetBitRouteShift::create_from_origin(1 << n); 64
    ]
};

pub fn bit_route_shift(bit: u64, dove: Dove) -> &'static [(u64, u64, (i8, i8))] {
    let idx = bit.trailing_zeros() as usize;
    BIT_ROUTE_SHIFTS[idx].bit_route_shift(dove)
}

#[derive(Debug, Clone, Copy)]
struct TargetBitRouteShift {
    b: [(u64, u64, (i8, i8)); 8],
    a: [(u64, u64, (i8, i8)); 8],
    y: [(u64, u64, (i8, i8)); 4],
    m: [(u64, u64, (i8, i8)); 4],
    t: [(u64, u64, (i8, i8)); 16],
    h: [(u64, u64, (i8, i8)); 8],
}

impl TargetBitRouteShift {
    const fn create_from_origin(origin_bit: u64) -> Self {
        let ba_shifts = [
            (-1, -1),
            (0, -1),
            (1, -1),
            (-1, 0),
            (1, 0),
            (-1, 1),
            (0, 1),
            (1, 1),
        ];
        let b = Self::make_bits_from_shifts(origin_bit, ba_shifts);
        let a = Self::make_bits_from_shifts(origin_bit, ba_shifts);

        let y_shifts = [(0, -1), (-1, 0), (1, 0), (0, 1)];
        let y = Self::make_bits_from_shifts(origin_bit, y_shifts);

        let m_shifts = [(-1, -1), (1, -1), (-1, 1), (1, 1)];
        let m = Self::make_bits_from_shifts(origin_bit, m_shifts);

        let t = Self::make_bits_t(origin_bit);

        let h_shifts = [
            (-1, -2),
            (1, -2),
            (-2, -1),
            (2, -1),
            (-2, 1),
            (2, 1),
            (-1, 2),
            (1, 2),
        ];
        let h = Self::make_bits_from_shifts(origin_bit, h_shifts);

        Self { b, a, y, m, t, h }
    }

    fn bit_route_shift(&self, dove_type: Dove) -> &[(u64, u64, (i8, i8))] {
        use Dove::*;
        match dove_type {
            B => &self.b,
            A => &self.a,
            Y => &self.y,
            M => &self.m,
            T => &self.t,
            H => &self.h,
        }
    }

    const fn make_bits_from_shifts<const N: usize>(
        origin_bit: u64,
        shifts: [(i8, i8); N],
    ) -> [(u64, u64, (i8, i8)); N] {
        let bits = array![
            n => {
                let shift = Shift { dh: shifts[n].0, dv: shifts[n].1 };
                let bit = bitutil::apply_shift(origin_bit, shift);
                (bit, bit, shifts[n])
            }; N
        ];
        bits
    }

    const fn make_bits_t(origin_bit: u64) -> [(u64, u64, (i8, i8)); 16] {
        // Note: the order of contents affects pack_moves
        let mut t = [(0, 0, (0, 0)); 16];

        let mut route = 0;
        macros::for_loop!(let mut i = 0; i < 4; i += 1 => {
            let shift = Shift {
                dh: 0,
                dv: -(i + 1),
            };
            let bit = bitutil::apply_shift(origin_bit, shift);
            route |= bit;
            t[i as usize] = (bit, route, (0, -(i + 1)));
        });

        route = 0;
        macros::for_loop!(let mut i = 0; i < 4; i += 1 => {
            let shift = Shift {
                dh: -(i + 1),
                dv: 0,
            };
            let bit = bitutil::apply_shift(origin_bit, shift);
            route |= bit;
            t[(i + 4) as usize] = (bit, route, (-(i + 1), 0));
        });

        route = 0;
        macros::for_loop!(let mut i = 0; i < 4; i += 1 => {
            let shift = Shift { dh: i + 1, dv: 0 };
            let bit = bitutil::apply_shift(origin_bit, shift);
            route |= bit;
            t[(i + 8) as usize] = (bit, route, (i + 1, 0));
        });

        route = 0;
        macros::for_loop!(let mut i = 0; i < 4; i += 1 => {
            let shift = Shift { dh: 0, dv: i + 1 };
            let bit = bitutil::apply_shift(origin_bit, shift);
            route |= bit;
            t[(i + 12) as usize] = (bit, route, (0, i + 1));
        });

        t
    }
}
