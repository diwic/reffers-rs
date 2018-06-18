use rc::State;
use std::{ops, cmp};

/// The first returned value from BitMask::bits is number of bits for Ref. 
pub const BM_REF: usize = 0;
/// The second returned value from BitMask::bits is number of bits for Strong. 
pub const BM_STRONG: usize = 1;
/// The third returned value from BitMask::bits is number of bits for Weak. 
pub const BM_WEAK: usize = 2;
/// Always points to the lowest two bits.
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
        if self.get_state() == State::BorrowedMut as u8 { return false; }
        let mmask = Self::MASKS[BM_STRONG] + Self::MASKS[BM_REF];
        let morig = self.get_inner();
        let zero: M::Num = Default::default();
        zero == morig & mmask
    }
}

