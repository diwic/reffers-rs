//! An alternative to `Rc<RefCell<T>>`, with less memory overhead and poisoning support.
//!
//! * Configurable overhead (compared to a fixed 24 or 12 for `Rc<RefCell<T>>`)
//!
//! * E g, 4 bytes gives you max 1024 immutable references, 1024 strong references
//! and 1024 weak references, but this can easily be tweaked with the `rc_bit_mask` macro.
//!
//! * Poisoning support - after a panic with an active mutable reference,
//! trying to get mutable or immutable references will return an error.
//! This can be reverted by calling unpoison(). 
//!
//! * Supports reference counted `str` and `[T]`. It's represented as a single pointer
//! (unlike e g `Box<str>`, which is a fat pointer).
//!
//! * Lacks CoerceUnsized optimisation support (because it is still unstable in libstd).
//!
//! * Last but not least, just writing `.get()` is less characters than `.upgrade().unwrap().borrow()`
//! that you would do with a `Weak<RefCell<T>>`.
//!
//! # Four structs
//!
//! * `Strong` - A strong reference to the inner value, keeping it from being dropped.
//!   To access the inner value, use `.get()` or `.get_mut()` to create `Ref` and `RefMut` structs.
//!
//! * `Ref` - A strong reference to the inner value, with immutable access to the inner value.
//!
//! * `RefMut` - A strong reference to the inner value, with mutable access to the inner value.
//!   There can only be one RefMut reference; and when Ref references exist, there can be no RefMut references.
//!
//! * `Weak` - A weak reference, the inner value will be dropped when no other types of references exist.
//!   This can be helpful w r t breaking up cycles of Strong references.
//!   There is no need to "upgrade" a weak reference to a strong reference just to access the inner value -
//!   just call `.get()` or `.get_mut()` on the weak reference directly.
//!
//! Where applicable, there are `.get_strong()` and `.get_weak()` functions that create new Strong and
//! Weak references. There are also `.try_get()`, `.try_get_mut()` etc functions that return an error instead
//! of panicking in case the reference is in an incorrect state. 
//!
//! # Using only as `Rc` or only as `RefCell`
//!
//! If you want to do this like `Rc` and never want to mutate the interior, just use `Ref` like an ordinary rc pointer. 
//! Combine with `Weak` for weak pointers, if you wish.
//!
//! If you want to use the `RefCell` part (e g, for the poisoning) but without reference counting, you can use `RCell` for that.
//!
//! # Example
//! ```
//! use reffers::rc::State;
//! use reffers::rc4::Strong;
//!
//! // Create a strong reference
//! let strong = Strong::new(5i32);
//!
//! // And a weak one
//! let weak = strong.get_weak();
//!
//! // Change the inner value
//! *weak.get_mut() = 7i32;
//!
//! // Inspect the change
//! {
//!     let r = strong.get();
//!     assert_eq!(*r, 7i32);
//!
//!     // We cannot change the value from the other reference
//!     // now. It is still borrowed...
//!     assert_eq!(weak.try_get_mut().unwrap_err(), State::Borrowed);
//! }
//!
//! // But now we can.
//! assert_eq!(strong.state(), State::Available);
//! *strong.get_mut() = 9i32;
//!
//! // Drop the strong reference, this drops the inner value as well
//! drop(strong);
//!
//! // We can't access the inner value, it has been dropped.
//! assert_eq!(weak.try_get().unwrap_err(), State::Dropped);
//! ```

use std::cell::{Cell, UnsafeCell};
use std::{fmt, mem, ptr, error, ops, borrow, convert, slice, hash, cmp};
use std::ptr::NonNull;
use std::marker::PhantomData;

/// The first returned value from BitMask::bits is number of bits for Ref. 
pub const BM_REF: usize = 0;
/// The second returned value from BitMask::bits is number of bits for Strong. 
pub const BM_STRONG: usize = 1;
/// The third returned value from BitMask::bits is number of bits for Weak. 
pub const BM_WEAK: usize = 2;

const IDX_TO_STATE: [State; 3] = [State::NotEnoughRefs, State::NotEnoughStrongs, State::NotEnoughWeaks];

pub unsafe trait BitMask: Copy + Default {
    /// The internal primitive type, usually u8, u16, u32 or u64.
    type Num: Copy + ops::BitAnd<Output=Self::Num> + cmp::PartialEq +
       ops::Add<Output=Self::Num> + ops::Sub<Output=Self::Num> + From<u8> + ops::Not<Output=Self::Num>;

    /// A triple of bits reserved for Ref, Strong and Weak -
    /// in that order. The first two (least significant) bits are reserved for state.
    ///
    /// Bits may not overflow. You need at least one bit that's either Ref or Strong.
    const BITS: [u8; 3];

    /// A triple of shifts.
    ///
    /// Must evaluate to: [2, 2 + BITS[0], 2 + BITS[0] + BITS[1]];
    // const SHIFTS: [u8; 3];

    const THREE: Self::Num;

    const SHIFTED: [Self::Num; 3];

    /// Transforms bits into masks.
    const MASKS: [Self::Num; 3];

    /// Gets the bitmask
    fn get_inner(&self) -> Self::Num;

    /// Sets the bitmask to the specified value.
    fn set_inner(&mut self, v: Self::Num);

    fn get_state(&self) -> u8;


    /// Changes reference count of a certain type,
    /// returns error on overflow.
    ///
    /// You probably don't want to implement this; implement the "bits" function instead.
    #[inline]
    fn inc(&mut self, idx: usize) -> Result<(), State> {
        let mmask = Self::MASKS[idx];
        let morig: Self::Num = self.get_inner();
        if (mmask & morig) == mmask { return Err(IDX_TO_STATE[idx]); }
        let m = morig + Self::SHIFTED[idx];
        self.set_inner(m);
        Ok(())
    }

    #[inline]
    fn is_zero(&self, idx: usize) -> bool {
        let mmask = Self::MASKS[idx];
        let morig: Self::Num = self.get_inner();
        let zero: Self::Num = unsafe { mem::zeroed() };
        zero == morig & mmask        
    }

    /// Decrements reference count of a certain type,
    /// panics on underflow.
    ///
    /// You probably don't want to implement this; implement the "bits" function instead.
    #[inline]
    fn dec(&mut self, idx: usize) {
        let morig: Self::Num = self.get_inner();
        debug_assert!(!self.is_zero(idx));
        let m = morig - Self::SHIFTED[idx];
        self.set_inner(m);
    }

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
    (masks, $t: ty, $r:expr, $s: expr, $w: expr) => {

        const BITS: [u8; 3] = [$r, $s, $w];

        const THREE: Self::Num = 3;

        // const SHIFTS: [u8; 3] = [2, 2+($r), 2+($r)+($s)];

        const SHIFTED: [$t; 3] = [1 << 2, 1 << (2 + $r), 1 << (2 + $r + $s)];

        const MASKS: [$t; 3] = [
            Self::SHIFTED[0] * ((1 << $r) - 1),
            Self::SHIFTED[1] * ((1 << $s) - 1),
            Self::SHIFTED[2] * ((1 << $w) - 1),
        ];
    };

    (primitive, $t: ty, $r:expr, $s: expr, $w: expr) => {
        unsafe impl $crate::rc::BitMask for $t {
            type Num = $t;

            rc_bit_mask!(masks, $t, $r, $s, $w);

            #[inline]
            fn get_state(&self) -> u8 { (*self & 3) as u8 }

            #[inline]
            fn get_inner(&self) -> Self::Num { *self }

            #[inline]
            fn set_inner(&mut self, v: Self::Num) { *self = v }
        }
    };

    ($t: ty, $t_int: ty, $r:expr, $s: expr, $w: expr) => {
        unsafe impl $crate::rc::BitMask for $t {
            type Num = $t_int;

            rc_bit_mask!(masks, $t_int, $r, $s, $w);

            #[inline]
            fn get_state(&self) -> u8 { (self.0 & 3) as u8 }

            #[inline]
            fn get_inner(&self) -> Self::Num { self.0 }

            #[inline]
            fn set_inner(&mut self, v: Self::Num) { self.0 = v }
        }
    };
}

/// Using u8 will allow for a maximum of four Ref, four Strong and four Weak.
///
/// That's not much, maybe you want to implement your own wrapper type instead. 
rc_bit_mask!(primitive, u8, 2, 2, 2);

/// Using u16 will allow for a maximum of 32 Ref, 16 Strong and 32 Weak.
rc_bit_mask!(primitive, u16, 5, 4, 5);

/// Using u32 will allow for a maximum of 1024 Ref, 1024 Strong and 1024 Weak.
rc_bit_mask!(primitive, u32, 10, 10, 10);

/// Using u64 will allow for a maximum of 2097152 Ref, 1048576 Strong and 2097152 Weak.
rc_bit_mask!(primitive, u64, 21, 20, 21);

/// Using u128 will give you 42 bits of Ref, Strong and Weak.
rc_bit_mask!(primitive, u128, 42, 42, 42);



#[test]
fn bitmask() {
    assert_eq!(u32::SHIFTED[BM_REF],    0x00000004);
    assert_eq!(u32::MASKS[BM_REF],      0x00000ffc);
    assert_eq!(u32::SHIFTED[BM_STRONG], 0x00001000);
    assert_eq!(u32::MASKS[BM_STRONG],   0x003ff000);
    assert_eq!(u32::SHIFTED[BM_WEAK],   0x00400000);
    assert_eq!(u32::MASKS[BM_WEAK],     0xffc00000);
    assert_eq!(u32::THREE, 3);
    let mut m = 0u32;
    m.inc(BM_WEAK).unwrap();
    assert_eq!(m, 0x00400000);
    m = 0xffc00000;
    assert!(m.inc(BM_WEAK).is_err());

    assert_eq!(u64::MASKS[BM_WEAK], 0xffff_f800_0000_0000);
    assert_eq!(u128::MASKS[BM_WEAK], 0xffff_ffff_ffc0_0000_0000_0000_0000_0000);
}


/// Current state of the Rc.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum State {
    /// No RefMut nor Ref currently exist - this Rc can be borrowed freely 
    Available = 0,
    /// Mutable borrowed by an RefMut.
    BorrowedMut = 1,
    /// The thread panicked while an RefMut could access the value. The inner value cannot
    /// be accessed before the unpoison function has been called.
    Poisoned = 2,
    /// Only Weak references exist, so the value has been dropped. It can not be recovered.
    Dropped = 3,
    /// Immutably borrowed by one or more Ref.
    Borrowed = 4,
    /// Returned as error from try_get in case no more immutable references are available
    NotEnoughRefs = 5,
    /// Returned as error from try_get_strong in case no more Strong references are available
    NotEnoughStrongs = 6,
    /// Returned as error from try_get_weak in case no more Weak references are available
    NotEnoughWeaks = 7,
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", (self as &error::Error).description())
    }
}

impl error::Error for State {
    fn description(&self) -> &str {
        match *self {
            State::Available => "Rc/cell is available",
            State::Borrowed => "Rc/cell is immutably borrowed",
            State::BorrowedMut => "Rc/cell is mutably borrowed",
            State::Poisoned => "Rc/cell is poisoned",
            State::Dropped => "Rc/cell is dropped",
            State::NotEnoughRefs => "Immutable reference count overflow (no more Refs available)", 
            State::NotEnoughStrongs => "Strong reference count overflow (no more Strongs available)",
            State::NotEnoughWeaks => "Weak reference count overflow (no more Weaks available)"
        }
    }
}

/// This is the "Cell" part of the Rc, which can be used separately
/// if you just need a Cell without the reference counting part.
///
/// This is very much like a RefCell, but with poisoning support
/// and customisable overhead.
#[derive(Debug)]
pub struct RCell<T: ?Sized, M: BitMask = u8> {
    mask: Cell<M>,
    inner: UnsafeCell<T>,
}

impl<T, M: BitMask> RCell<T, M> {
    #[inline]
    pub fn new(t: T) -> Self {
        use std::default::Default; 
        RCell { mask: Cell::new(Default::default()),
            inner: UnsafeCell::new(t) }
    }
}


impl<T: ?Sized, M: BitMask> RCell<T, M> {
    pub fn state(&self) -> State {
        let m2 = self.mask.get();
        let m = m2.get_state();
        match m {
            0 => {
                if m2.is_zero(BM_REF) { State::Available } else { State::Borrowed }
            },
            1 => State::BorrowedMut,
            2 => State::Poisoned,
            3 => State::Dropped,
            _ => unreachable!(),
        }
    }

    #[inline]
    fn set_state(&self, s: State) {
        let s = s as u8;
        debug_assert!(s <= 3);
        let mut m2 = self.mask.get(); 
        let mut m = m2.get_inner();
        m = m & (!M::THREE);
        m = m + s.into();
        m2.set_inner(m);
        self.mask.set(m2);
    }

    pub fn try_get<'a>(&'a self) -> Result<RCellRef<'a, T, M>, State> {
        let s = self.state();
        if s != State::Available && s != State::Borrowed { return Err(s); }

        let mut m = self.mask.get();
        try!(m.inc(BM_REF));
        self.mask.set(m);

        Ok(RCellRef(self))
    }

    pub fn try_get_mut<'a>(&'a self) -> Result<RCellRefMut<'a, T, M>, State> {
        let s = self.state();
        if s != State::Available { return Err(s); }
        self.set_state(State::BorrowedMut);
        Ok(RCellRefMut(self))
    }

    pub fn unpoison(&self) -> Result<(), State> {
        let s = self.state();
        if s != State::Poisoned { return Err(s); }
        self.set_state(State::Available);
        Ok(())
    }
}


/// Immutable borrow of an RCell.
pub struct RCellRef<'a, T: 'a + ?Sized, M: 'a + BitMask>(&'a RCell<T, M>);

impl<'a, T: 'a + ?Sized, M: 'a + BitMask> Drop for RCellRef<'a, T, M> {
    fn drop(&mut self) {
        debug_assert_eq!(self.0.state(), State::Borrowed);

        let mut m = self.0.mask.get();
        m.dec(BM_REF);
        self.0.mask.set(m);
    }
}

impl<'a, T: 'a + ?Sized, M: 'a + BitMask> ops::Deref for RCellRef<'a, T, M> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target { unsafe { &*self.0.inner.get() }}
}


/// Mutable borrow of an RCell.
pub struct RCellRefMut<'a, T: 'a + ?Sized, M: 'a + BitMask>(&'a RCell<T, M>);

impl<'a, T: 'a + ?Sized, M: 'a + BitMask> Drop for RCellRefMut<'a, T, M> {
    fn drop(&mut self) {
        use std::thread;
        debug_assert_eq!(self.0.state(), State::BorrowedMut);
        let s = if thread::panicking() { State::Poisoned } else { State::Available };
        self.0.set_state(s);
    }
}

impl<'a, T: 'a + ?Sized, M: 'a + BitMask> ops::Deref for RCellRefMut<'a, T, M> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target { unsafe { &*self.0.inner.get() }}
}

impl<'a, T: 'a + ?Sized, M: 'a + BitMask> ops::DerefMut for RCellRefMut<'a, T, M> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { &mut *self.0.inner.get() } }
}



#[doc(hidden)]
#[repr(C)]
#[derive(Debug)]
/// This is an implementation detail. Don't worry about it.
pub struct CSlice<T> {
    len: u32,
    data: [T; 0],
}

fn cslice_len_to_capacity<T, M: BitMask>(l: usize) -> usize {
    let self_size = mem::size_of::<UnsafeCell<RCell<CSlice<T>, M>>>();
    let t_size = mem::size_of::<T>();
    let data_bytes = l * t_size;
    let r = 1 + ((data_bytes + self_size - 1) / self_size);
    debug_assert!(self_size * (r - 1) >= l * t_size);
    r
}

/// This is an implementation detail. Please don't mess with it.
///
/// It's for abstracting over sized and unsized types.
#[doc(hidden)]
pub unsafe trait Repr {
    type Store;
    fn convert(*mut Self::Store) -> *mut Self;
    unsafe fn deallocate_mem<M: BitMask>(&mut UnsafeCell<RCell<Self::Store, M>>);
}

// Sized types, no problem here
unsafe impl<T> Repr for T {
    type Store = T;
    #[inline]
    fn convert(s: *mut T) -> *mut T { s }
    unsafe fn deallocate_mem<M: BitMask>(s: &mut UnsafeCell<RCell<Self::Store, M>>) { let _ = Vec::from_raw_parts(s, 0, 1); }
}

unsafe impl<T> Repr for [T] {
    type Store = CSlice<T>;
    #[inline]
    fn convert(s: *mut CSlice<T>) -> *mut [T] {
        unsafe { slice::from_raw_parts_mut((*s).data.as_mut_ptr(), (*s).len as usize) }
    }
    unsafe fn deallocate_mem<M: BitMask>(s: &mut UnsafeCell<RCell<Self::Store, M>>) {
        let _ = Vec::from_raw_parts(s, 0, cslice_len_to_capacity::<T, M>((*(*s.get()).inner.get()).len as usize));
    }
}

unsafe impl Repr for str {
    type Store = CSlice<u8>;
    #[inline]
    fn convert(s: *mut CSlice<u8>) -> *mut str { unsafe {
        let u: *mut [u8] = slice::from_raw_parts_mut((*s).data.as_mut_ptr(), (*s).len as usize);
        u as *mut str
    }}
    unsafe fn deallocate_mem<M: BitMask>(s: &mut UnsafeCell<RCell<Self::Store, M>>) { 
        let _ = Vec::from_raw_parts(s, 0, cslice_len_to_capacity::<u8, M>((*(*s.get()).inner.get()).len as usize));
    }
}


// Note: This would benefit from NonZero/Shared ptr support,
// as well as CoerceUnsized support 
//
// Note2: I'm not sure the UnsafeCell is needed. But otherwise we'd have to 
// cast the *const to a *mut instead and using UnsafeCell makes me more sure
// that this isn't UB

//#[derive(Debug)]
struct RCellPtr<T: ?Sized + Repr, M: BitMask>(NonNull<UnsafeCell<RCell<T::Store, M>>>, PhantomData<T>);

fn allocate<T, M: BitMask>(capacity: usize, data: T) -> NonNull<UnsafeCell<RCell<T,M>>> {
    // Allocate trick from https://github.com/rust-lang/rust/issues/27700
    debug_assert!(capacity > 0);
    let mut v = Vec::with_capacity(capacity);
    v.push(UnsafeCell::new(RCell::new(data)));
    let z = v.as_mut_ptr();
    mem::forget(v);
    debug_assert!(z != ptr::null_mut());
    unsafe { NonNull::new_unchecked(z) }
}

impl<M: BitMask> RCellPtr<str, M> {
    fn new_str(t: &str) -> Self {
        let len = t.len();
        assert!(len <= u32::max_value() as usize);
        let z = allocate(cslice_len_to_capacity::<u8, M>(len), CSlice { len: len as u32, data: [] });
        let r: Self = RCellPtr(z, PhantomData);
        unsafe { ptr::copy_nonoverlapping(t.as_ptr(), (*r.get().inner.get()).data.as_mut_ptr(), len) };
        r
    }
}


impl<T, M: BitMask> RCellPtr<[T], M> {
    fn new_slice<I: ExactSizeIterator<Item=T>>(iter: I) -> Self {
        let len = iter.len();
        assert!(len <= u32::max_value() as usize);
        let z = allocate(cslice_len_to_capacity::<T, M>(len), CSlice { len: len as u32, data: [] });
        let r: Self = RCellPtr(z, PhantomData);
        let p = unsafe { (*r.get().inner.get()).data.as_mut_ptr() };
        for (idx, item) in iter.enumerate() {
            unsafe { ptr::write(p.offset(idx as isize), item) }
        }
        r
    }
}

impl<T, M: BitMask> RCellPtr<T, M> {
    fn new(t: T) -> Self {
        let z = allocate(1, t);
        let r = RCellPtr(z, PhantomData);
        debug_assert_eq!(r.0.as_ptr() as *const (), r.get() as *const _ as *const ());
        r
    }
}


impl<T: ?Sized + Repr, M: BitMask> RCellPtr<T, M> {
    #[inline]
    fn get_refmut(&self) -> Result<RefMut<T, M>, State> {
        let e = self.state();
        if e == State::Available {
            self.get().set_state(State::BorrowedMut);
            Ok(RefMut(RCellPtr(self.0, PhantomData), PhantomData))
        }
        else { Err(e) }
    }

    #[inline]
    fn get_strong(&self) -> Result<Strong<T, M>, State> {
        let e = self.state();
        if e != State::Dropped {
            try!(self.inc(BM_STRONG));
            Ok(Strong(RCellPtr(self.0, PhantomData), PhantomData))
        }
        else { Err(e) }
    }

    #[inline]
    fn get_weak(&self) -> Result<Weak<T, M>, State> {
        try!(self.inc(BM_WEAK));
        Ok(Weak(RCellPtr(self.0, PhantomData)))
    }

    #[inline]
    fn check_drop(&mut self) {
        let m = self.get().mask.get();
        if m.get_state() == 1 { return; } // Existing RefMut
        if !m.is_zero(BM_REF) { return; } // Existing Ref
        if !m.is_zero(BM_STRONG) { return; } // Existing Strong
        self.do_drop();
    }

    fn do_drop(&mut self) {
        {
            let c = self.get();
            if c.state() != State::Dropped {
                // Prevent double free in case drop_in_place does weird things
                let used_ref = self.inc(BM_REF).is_ok();
                if !used_ref {
                    self.inc(BM_STRONG).unwrap();
                }
                c.set_state(State::Dropped);
                unsafe { ptr::drop_in_place(T::convert(c.inner.get())) };
                debug_assert_eq!(c.state(), State::Dropped);
                self.dec(if used_ref { BM_REF } else { BM_STRONG });
                debug_assert!(c.mask.get().is_zero(BM_REF));
                debug_assert!(c.mask.get().is_zero(BM_STRONG));
            }
            if !c.mask.get().is_zero(BM_WEAK) { return };
        }
        unsafe { T::deallocate_mem(self.0.as_mut()) };
    }

    #[inline]
    fn value_ptr(&self) -> *mut T { T::convert(self.get().inner.get()) }

    #[inline]
    fn get(&self) -> &RCell<T::Store, M> { unsafe { &*(self.0.as_ref()).get() }}

    #[inline]
    fn get_ref(&self) -> Result<Ref<T, M>, State> {
        let e = self.state();
        if e == State::Available || e == State::Borrowed {
            try!(self.inc(BM_REF));
            Ok(Ref(RCellPtr(self.0, PhantomData), PhantomData))
        }
        else { Err(e) }
    }

    #[inline]
    fn state(&self) -> State { self.get().state() }

    #[inline]
    fn inc(&self, idx: usize) -> Result<(), State> {
        let mut m = self.get().mask.get();
        try!(m.inc(idx));
        self.get().mask.set(m);
        Ok(())
    }

    #[inline]
    fn dec(&self, idx: usize) {
        let mut m = self.get().mask.get();
        m.dec(idx);
        self.get().mask.set(m);
    }
}


impl<T: ?Sized + Repr, M: BitMask + fmt::Debug> fmt::Debug for RCellPtr<T, M> 
    where T::Store: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.get())
    }
}

/// An Rc reference which has immutable access to the inner value.
///
/// It's like a strong reference, and a immutably borrowed interior,
/// in the same struct.
///
/// # Example
///
/// ```
/// use reffers::rc::Ref;
/// use std::collections::HashMap;
///
/// let mut z = HashMap::new();
/// z.insert(<Ref<_>>::new_str("Test"), 5);
/// assert_eq!(z.get("Test"), Some(&5));
/// ```

#[derive(Debug)]
pub struct Ref<T: ?Sized + Repr, M: BitMask = u32>(RCellPtr<T, M>, PhantomData<RCell<T::Store, M>>);

impl<T: ?Sized + Repr, M: BitMask> Ref<T, M> {
    impl_get_ref!();
    impl_ref_all!();
}

new_ref!(Ref, RCellPtr, get_ref, BitMask);

impl<T: ?Sized + Repr, M: BitMask> Drop for Ref<T, M> {
    fn drop(&mut self) {
        debug_assert_eq!(self.0.state(), State::Borrowed);
        self.0.dec(BM_REF);
        self.0.check_drop();
    }
}

impl<T: ?Sized + Repr, M: BitMask> ops::Deref for Ref<T, M> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target { unsafe { &*self.0.value_ptr() }}
}

impl<T: ?Sized + Repr + fmt::Display, M: BitMask> fmt::Display for Ref<T, M> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Display::fmt(&**self, f) }
}

impl<T: ?Sized + Repr, M: BitMask> borrow::Borrow<T> for Ref<T, M> {
    #[inline]
    fn borrow(&self) -> &T { &**self }
}

impl<T: ?Sized + Repr, M: BitMask> convert::AsRef<T> for Ref<T, M> {
    #[inline]
    fn as_ref(&self) -> &T { &**self }
}

impl<T: ?Sized + Repr + hash::Hash, M: BitMask> hash::Hash for Ref<T, M> {
    #[inline]
    fn hash<H>(&self, state: &mut H) where H: hash::Hasher { (**self).hash(state) }
}

impl<T: ?Sized + Repr + PartialEq, M: BitMask> PartialEq for Ref<T, M> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { **self == **other }
    #[inline]
    fn ne(&self, other: &Self) -> bool { **self != **other }
}

impl<T: ?Sized + Repr + Eq, M: BitMask> Eq for Ref<T, M> {}

impl<T: ?Sized + Repr + PartialOrd, M: BitMask> PartialOrd for Ref<T, M> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { (**self).partial_cmp(&**other) }
    #[inline]
    fn lt(&self, other: &Self) -> bool { **self < **other }
    #[inline]
    fn le(&self, other: &Self) -> bool { **self <= **other }
    #[inline]
    fn gt(&self, other: &Self) -> bool { **self > **other }
    #[inline]
    fn ge(&self, other: &Self) -> bool { **self >= **other }
}

impl<T: ?Sized + Repr + Ord, M: BitMask> Ord for Ref<T, M> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering { (**self).cmp(&**other) }
}

impl<T: ?Sized + Repr, M: BitMask> Clone for Ref<T, M> {
    #[inline]
    fn clone(&self) -> Self { self.get() }
}


/// An Rc which has mutable access to the inner value. Only
/// one RefMut can exist, and cannot coexist with any Ref.
#[derive(Debug)]
pub struct RefMut<T: ?Sized + Repr, M: BitMask = u32>(RCellPtr<T, M>, PhantomData<RCell<T::Store, M>>);

new_ref!(RefMut, RCellPtr, get_refmut, BitMask);

impl<T: ?Sized + Repr, M: BitMask> RefMut<T, M> {
    impl_ref_all!();
}

impl<T: ?Sized + Repr, M: BitMask> Drop for RefMut<T, M> {
    fn drop(&mut self) {
        use std::thread;
        debug_assert_eq!(self.0.state(), State::BorrowedMut);
        let s = if thread::panicking() { State::Poisoned } else { State::Available };
        self.0.get().set_state(s);
        self.0.check_drop();
    }
}

impl<T: ?Sized + Repr, M: BitMask> ops::Deref for RefMut<T, M> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target { unsafe { &*self.0.value_ptr() }}
}

impl<T: ?Sized + Repr, M: BitMask> ops::DerefMut for RefMut<T, M> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { &mut *self.0.value_ptr() }}
}


impl<T: ?Sized + Repr, M: BitMask> borrow::Borrow<T> for RefMut<T, M> {
    fn borrow(&self) -> &T { &**self }
}

impl<T: ?Sized + Repr, M: BitMask> convert::AsRef<T> for RefMut<T, M> {
    fn as_ref(&self) -> &T { &**self }
}

impl<T: ?Sized + Repr + fmt::Display, M: BitMask> fmt::Display for RefMut<T, M> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Display::fmt(&**self, f) }
}

impl<T: ?Sized + Repr + hash::Hash, M: BitMask> hash::Hash for RefMut<T, M> {
    #[inline]
    fn hash<H>(&self, state: &mut H) where H: hash::Hasher { (**self).hash(state) }
}

impl<T: ?Sized + Repr + PartialEq, M: BitMask> PartialEq for RefMut<T, M> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { **self == **other }
    #[inline]
    fn ne(&self, other: &Self) -> bool { **self != **other }
}

impl<T: ?Sized + Repr + Eq, M: BitMask> Eq for RefMut<T, M> {}

impl<T: ?Sized + Repr + PartialOrd, M: BitMask> PartialOrd for RefMut<T, M> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { (**self).partial_cmp(&**other) }
    #[inline]
    fn lt(&self, other: &Self) -> bool { **self < **other }
    #[inline]
    fn le(&self, other: &Self) -> bool { **self <= **other }
    #[inline]
    fn gt(&self, other: &Self) -> bool { **self > **other }
    #[inline]
    fn ge(&self, other: &Self) -> bool { **self >= **other }
}

impl<T: ?Sized + Repr + Ord, M: BitMask> Ord for RefMut<T, M> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering { (**self).cmp(&**other) }
}


/// A strong reference without access to the inner value.
///
/// To get immutable/mutable access, you need to use the 
/// get/get_mut functions to create Ref or RefMut references.
///
/// The inner value cannot be dropped while Strong, Ref or RefMut references exist.
#[derive(Debug)]
pub struct Strong<T: ?Sized + Repr, M: BitMask = u32>(RCellPtr<T, M>, PhantomData<RCell<T::Store, M>>);

new_ref!(Strong, RCellPtr, get_strong, BitMask);

impl<T: ?Sized + Repr, M: BitMask> Strong<T, M> {
    impl_get_refmut!();
    impl_get_ref!();
    impl_ref_all!();
}

impl<T: ?Sized + Repr, M: BitMask> Drop for Strong<T, M> {
    fn drop(&mut self) {
        self.0.dec(BM_STRONG);
        self.0.check_drop();
    }
}

impl<T: ?Sized + Repr, M: BitMask> Clone for Strong<T, M> {
    #[inline]
    fn clone(&self) -> Self { self.get_strong() }
}

/// A weak reference without access to the inner value.
///
/// To get immutable/mutable access, you need to use the 
/// get/get_mut functions to create Ref or RefMut references.
///
/// If only weak references exist to the inner value,
/// the inner value will be dropped, and can no longer be accessed.
//#[derive(Debug)]
pub struct Weak<T: ?Sized + Repr, M: BitMask = u32>(RCellPtr<T, M>);

impl<T: ?Sized + Repr, M: BitMask> Weak<T, M> {
    impl_get_refmut!();
    impl_get_ref!();
    impl_ref_all!();
}

impl<T: ?Sized + Repr, M: BitMask> Drop for Weak<T, M> {
    fn drop(&mut self) {
        self.0.dec(BM_WEAK);
        self.0.check_drop();
    }
}

impl<T: ?Sized + Repr, M: BitMask> Clone for Weak<T, M> {
    #[inline]
    fn clone(&self) -> Self { self.get_weak() }
}

#[test]
fn rc_basic() {
    let z = Strong::<_, u8>::new(5i32);
    assert_eq!(z.state(), State::Available);
    let z2 = z.clone();
    assert_eq!(z2.state(), State::Available);
    {
        let mut r = z2.get_mut();
        assert_eq!(z.state(), State::BorrowedMut);
        assert_eq!(*r, 5i32);
        *r = 6i32;
        assert!(z.try_get().is_err());
    }
    assert_eq!(z2.state(), State::Available);
    assert_eq!(*z.get(), 6i32);
    drop(z2);
    assert_eq!(*z.get(), 6i32);
}


#[test]
fn rc_drop() {
    struct Dummy<'a>(&'a Cell<i32>);
    impl<'a> Drop for Dummy<'a> { fn drop(&mut self) { self.0.set(73) }}

    let q = Cell::new(11i32);
    let z = <Strong<_>>::new(Dummy(&q));
    assert_eq!(z.state(), State::Available);
    let z2 = z.clone();
    drop(z);
    assert_eq!(z2.state(), State::Available);
    assert_eq!(q.get(), 11);
    drop(z2);
    assert_eq!(q.get(), 73);

    let q2 = Cell::new(12i32); 
    let z2 = <Strong<_>>::new_slice(vec![Dummy(&q2)].into_iter());
    drop(z2);
    assert_eq!(q2.get(), 73);
}

#[test]
fn rc_str() {
    let s = ::rc2::Ref::new_str("Hello world!");
    assert_eq!(&*s, "Hello world!");
    let _q = s.get_strong();
    let r = s.get_weak();
    drop(s);
    assert_eq!(&*r.get_mut(), "Hello world!");
}

#[test]
fn rc_slice() {
    let v = vec![String::from("abc"), String::from("def")];
    let mut s = RefMut::<[String]>::new_slice(v.into_iter());
    s[1] = String::from("ghi");
    assert_eq!(&*s[0], "abc");
    assert_eq!(&*s[1], "ghi");
}

#[test]
fn rc_hashmap() {
    use std::collections::HashMap;
    let mut z = HashMap::new();
    z.insert(<Ref<_>>::new_str("Short"), 5);
    z.insert(<Ref<_>>::new_str("This is a long string"), 25);
    assert_eq!(z.get("Short"), Some(&5));
    assert_eq!(z.get(""), None);
}
