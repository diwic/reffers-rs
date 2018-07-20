use rc::State;
use std::{ops, cmp};

/// The first returned value from BitMask::bits is number of bits for Ref. 
pub const BM_REF: usize = 0;
/// The second returned value from BitMask::bits is number of bits for Strong. 
pub const BM_STRONG: usize = 1;
/// The third returned value from BitMask::bits is number of bits for Weak. 
pub const BM_WEAK: usize = 2;

// Always points to the lowest two bits.
// pub const BM_STATE: usize = 3;


/// The BitMask trait configures the memory overhead and the number of bits for Ref, Strong and Weak references.
///
/// If you like to make your own, use the `rc_bit_mask!` macro.
pub unsafe trait BitMask: Copy + Default {
    /// The internal primitive type, usually u8, u16, u32 or u64.
    type Num: Copy + Default + ops::BitAnd<Output=Self::Num> + cmp::PartialEq +
       ops::Add<Output=Self::Num> + ops::Sub<Output=Self::Num> + From<u8> + ops::Not<Output=Self::Num>;

    /// All zero bits, except for the first bit 
    const SHIFTED: [Self::Num; 4];

    /// Transforms bits into masks.
    const MASKS: [Self::Num; 4];

    /// Gets the bitmask
    fn get_inner(&self) -> Self::Num;

    /// Sets the bitmask to the specified value.
    fn set_inner(&mut self, v: Self::Num);

    /// Gets the two lowest bits.
    fn get_state(&self) -> u8;

    /// Sets the two lowest bits.
    fn set_state(&mut self, v: u8);
}

#[doc(hidden)]
#[macro_export]
macro_rules! rc_bit_mask_internal {
    (masks, $t: ty, $r:expr, $s: expr, $w: expr) => {
        const SHIFTED: [$t; 4] = [1 << 2, 1 << (2 + $r), 1 << (2 + $r + $s), 1];

        const MASKS: [$t; 4] = [
            Self::SHIFTED[0] * ((1 << $r) - 1),
            Self::SHIFTED[1] * ((1 << $s) - 1),
            Self::SHIFTED[2] * ((1 << $w) - 1),
            3,
        ];
    };

    (primitive, $t: ty, $r:expr, $s: expr, $w: expr) => {
        unsafe impl $crate::rc::BitMask for $t {
            type Num = $t;

            rc_bit_mask_internal!(masks, $t, $r, $s, $w);

            #[inline]
            fn get_state(&self) -> u8 { (*self & 3) as u8 }

            #[inline]
            fn set_state(&mut self, v: u8) { *self = (*self & !3) | ((v & 3) as $t); }

            #[inline]
            fn get_inner(&self) -> Self::Num { *self }

            #[inline]
            fn set_inner(&mut self, v: Self::Num) { *self = v }
        }
    };
}


/// If you need your own rc with custom overhead, you can invoke this macro for your own type
/// (which is normally a newtype around an integer).
///
/// # Example
/// ```
/// #[macro_use]
/// extern crate reffers;
/// use reffers::rc::Ref;
///
/// #[derive(Debug, Copy, Clone, Default)]
/// struct ManyWeak(u32);
///
/// // We want 16 Refs, no Strongs, and as many Weaks as possible
/// // for the 32 bits of overhead that we are willing to accept.
/// // In total, this must add up to max 30 bits (32 bits minus 2 for status).
/// rc_bit_mask!(ManyWeak, u32, 4, 0, 26);
///
/// fn main() {
///     let r: Ref<str, ManyWeak> = Ref::new_str("Hi!");
///     // We can create weaks
///     let w = r.get_weak();
///     // ...but no strongs
///     assert!(w.try_get_strong().is_err());
/// }
/// ```
#[macro_export]
macro_rules! rc_bit_mask {
    ($t: ty, $t_int: ty, $r:expr, $s: expr, $w: expr) => {
        unsafe impl $crate::rc::BitMask for $t {
            type Num = $t_int;

            rc_bit_mask_internal!(masks, $t_int, $r, $s, $w);

            #[inline]
            fn get_state(&self) -> u8 { (self.0 & 3) as u8 }

            #[inline]
            fn set_state(&mut self, v: u8) { self.0 = (self.0 & !3) | ((v & 3) as $t_int); }

            #[inline]
            fn get_inner(&self) -> Self::Num { self.0 }

            #[inline]
            fn set_inner(&mut self, v: Self::Num) { self.0 = v }
        }
    };
}

pub (crate) trait BitMaskOps {
    fn inc(&mut self, idx: usize) -> Result<(), State>;
    fn is_zero(&self, idx: usize) -> bool;
    fn dec(&mut self, idx: usize);
    fn is_alive(&self) -> bool;
}


const IDX_TO_STATE: [State; 3] = [State::NotEnoughRefs, State::NotEnoughStrongs, State::NotEnoughWeaks];

impl<M: BitMask> BitMaskOps for M {
    #[inline]
    fn inc(&mut self, idx: usize) -> Result<(), State> {
        let mmask = Self::MASKS[idx];
        let morig = self.get_inner();
        if (mmask & morig) == mmask { return Err(IDX_TO_STATE[idx]); }
        let m = morig + Self::SHIFTED[idx];
        self.set_inner(m);
        Ok(())
    }

    #[inline]
    fn is_zero(&self, idx: usize) -> bool {
        let mmask = Self::MASKS[idx];
        let morig = self.get_inner();
        let zero: M::Num = Default::default();
        zero == morig & mmask        
    }

    /// Decrements reference count of a certain type,
    /// might panic on underflow.
    #[inline]
    fn dec(&mut self, idx: usize) {
        let morig = self.get_inner();
        debug_assert!(!self.is_zero(idx));
        let m = morig - Self::SHIFTED[idx];
        self.set_inner(m);
    }

    #[inline]
    fn is_alive(&self) -> bool {
        if self.get_state() == State::BorrowedMut as u8 { return true; }
        let mmask = Self::MASKS[BM_STRONG] + Self::MASKS[BM_REF];
        let morig = self.get_inner();
        let zero: M::Num = Default::default();
        !(zero == morig & mmask)
    }
}


/// Using u8 will allow for a maximum of four Ref, four Strong and four Weak.
///
/// That's not much, maybe you want to implement your own wrapper type instead. 
rc_bit_mask_internal!(primitive, u8, 2, 2, 2);

/// Using u16 will allow for a maximum of 32 Ref, 16 Strong and 32 Weak.
rc_bit_mask_internal!(primitive, u16, 5, 4, 5);

/// Using u32 will allow for a maximum of 1024 Ref, 1024 Strong and 1024 Weak.
rc_bit_mask_internal!(primitive, u32, 10, 10, 10);

/// Usize defaults to same as u32.
rc_bit_mask_internal!(primitive, usize, 10, 10, 10);

/// Using u64 will allow for a maximum of 2097152 Ref, 1048576 Strong and 2097152 Weak.
rc_bit_mask_internal!(primitive, u64, 21, 20, 21);

/// Using u128 will give you 42 bits of Ref, Strong and Weak.
rc_bit_mask_internal!(primitive, u128, 42, 42, 42);



#[test]
fn bitmask() {
    assert_eq!(u32::SHIFTED[BM_REF],    0x00000004);
    assert_eq!(u32::MASKS[BM_REF],      0x00000ffc);
    assert_eq!(u32::SHIFTED[BM_STRONG], 0x00001000);
    assert_eq!(u32::MASKS[BM_STRONG],   0x003ff000);
    assert_eq!(u32::SHIFTED[BM_WEAK],   0x00400000);
    assert_eq!(u32::MASKS[BM_WEAK],     0xffc00000);
    let mut m = 0u32;
    m.inc(BM_WEAK).unwrap();
    assert_eq!(m, 0x00400000);
    m = 0xffc00000;
    assert!(m.inc(BM_WEAK).is_err());

    assert_eq!(u64::MASKS[BM_WEAK], 0xffff_f800_0000_0000);
    assert_eq!(u128::MASKS[BM_WEAK], 0xffff_ffff_ffc0_0000_0000_0000_0000_0000);
}


