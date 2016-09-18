//! An alternative to `Rc<RefCell<T>>`, with less memory overhead and poisoning support.
//!
//! * Configurable overhead (compared to a fixed 12 or 24 for `Rc<RefCell<T>>`)
//!
//! * The default of 4 bytes gives you max 64 immutable references, 4096 strong references
//! and 4096 weak references, but this can easily be tweaked with just a few lines of code.
//!
//! * Poisoning support - after a panic with an active mutable reference,
//! trying to get mutable or immutable references will return an error.
//! This can be reverted by calling unpoison(). 
//!
//! * Lacks CoerceUnsized and NonZero optimisation support (because it is still unstable in libstd).
//!
//! * Last but not least, just writing `.get()` is less characters than `.upgrade().unwrap().borrow()`
//! that you would do with a `Weak<RefCell<T>>`.
//!
//! # Example
//! ```
//! use reffers::rc::{Strong, State};
//!
//! // Create a strong reference
//! let strong = Strong::<_, u32>::new(5i32);
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
use std::{fmt, mem, ptr, error, ops};
use std::marker::PhantomData;

/// The first returned value from BitMask::bits is number of bits for Ref. 
pub const BM_REF: usize = 0;
/// The second returned value from BitMask::bits is number of bits for Strong. 
pub const BM_STRONG: usize = 1;
/// The third returned value from BitMask::bits is number of bits for Weak. 
pub const BM_WEAK: usize = 2;

const OVERFLOW_STR: [&'static str; 3] = 
["Immutable reference count overflow (no more Refs available)", 
"Strong reference count overflow (no more Strongs available)",
"Weak reference count overflow (no more Weaks available)"];

/// If you need your own custom Rc, you can implement this for your own type
/// (e g, a newtype around an integer or so).
///
/// Declaring these functions with #[inline] is recommended for performance.
/// You only need to implement bits (the actual config), get and set functions. 
pub unsafe trait BitMask: Copy + Default {
    /// Returns a triple of bits reserved for Ref, Strong and Weak -
    /// in that order. The first two (least significant) bits are reserved for state.
    ///
    /// Must, of course, always return the same values for the same type,
    /// and bits may not overflow. 
    fn bits() -> [u8; 3];
    /// Sets the bitmask to the specified value.
    fn set(&mut self, u64);
    /// Gets the bitmask as an u64.
    fn get(&self) -> u64;

    /// Transforms bits into shifts.
    ///
    /// You probably don't want to implement this; implement the "bits" function instead.
    #[inline]
    fn shifts() -> [u8; 3] {
        let b = Self::bits();
        [2, 2+b[BM_REF], 2+b[BM_STRONG]+b[BM_REF]]
    }

    /// Transforms bits into masks.
    ///
    /// You probably don't want to implement this; implement the "bits" function instead.
    #[inline]
    fn mask(idx: usize) -> u64 {
         let b = Self::bits()[idx];
         let s = Self::shifts()[idx];
         ((1u64 << b) - 1) << s
    }

    /// Changes reference count of a certain type,
    /// returns error on overflow.
    ///
    /// You probably don't want to implement this; implement the "bits" function instead.
    #[inline]
    fn inc(&mut self, idx: usize) -> Result<(), &'static str> {
        let shift = Self::shifts()[idx];
        let mmask = Self::mask(idx);
        let morig = self.get();
        let m = (morig & mmask) + (1 << shift);
        if (m & (!mmask)) != 0 { return Err(OVERFLOW_STR[idx]); }
        let m = m | (morig & (!mmask));
        self.set(m);
        Ok(())
    }

    /// Decrements reference count of a certain type,
    /// panics on underflow.
    ///
    /// You probably don't want to implement this; implement the "bits" function instead.
    #[inline]
    fn dec(&mut self, idx: usize) {
        let shift = Self::shifts()[idx];
        let mmask = Self::mask(idx);
        let morig = self.get();
        let m = (morig & mmask) - (1 << shift);
        if (m & (!mmask)) != 0 { panic!("Internal refcount error of type {}", idx); }
        let m = m | (morig & (!mmask));
        self.set(m);
    }

}

/// Using u8 will allow for a maximum of four Ref, four Strong and four Weak.
///
/// That's not much, maybe you want to implement your own wrapper type instead. 
unsafe impl BitMask for u8 {
    #[inline]
    fn bits() -> [u8; 3] { [2, 2, 2] }

    #[inline]
    fn set(&mut self, u: u64) { *self = u as u8 }

    #[inline]
    fn get(&self) -> u64 { *self as u64 }
}

/// Using u32 will allow for a maximum of 64 Ref, 4096 Strong and 4096 Weak.
unsafe impl BitMask for u32 {
    #[inline]
    fn bits() -> [u8; 3] { [6, 12, 12] }

    #[inline]
    fn set(&mut self, u: u64) { *self = u as Self }

    #[inline]
    fn get(&self) -> u64 { *self as u64 }
}

#[test]
fn bitmask() {
    assert_eq!(u32::mask(BM_REF), 0x000000fc);
    assert_eq!(u32::mask(BM_STRONG), 0x000fff00);
    assert_eq!(u32::mask(BM_WEAK), 0xfff00000);
    let mut m = 0u32;
    m.inc(BM_WEAK).unwrap();
    assert_eq!(m, 0x00100000);
    m = 0xfff00000;
    assert!(m.inc(BM_WEAK).is_err());
}

/// Using u64 will allow for a maximum of 16384 Ref, 2^24 (approx 16 million) Strong and 2^24 Weak.
unsafe impl BitMask for u64 {
    #[inline]
    fn bits() -> [u8; 3] { [14, 24, 24] }

    #[inline]
    fn set(&mut self, u: u64) { *self = u as Self }

    #[inline]
    fn get(&self) -> u64 { *self as u64 }
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
        let m = self.mask.get().get();
        match m & 3 {
            0 => {
                let mr = M::mask(BM_REF);
                if (m & mr) != 0 { State::Borrowed } else { State::Available }
            },
            1 => State::BorrowedMut,
            2 => State::Poisoned,
            3 => State::Dropped,
            _ => unreachable!(),
        }
    }

    #[inline]
    fn set_state(&self, s: State) { 
        debug_assert!(s != State::Borrowed);
        let mut m2 = self.mask.get(); 
        let mut m = m2.get();
        m &= !3;
        m += s as u64;
        m2.set(m);
        self.mask.set(m2);
    }
}

// Note: This would benefit from NonZero/Shared ptr support,
// as well as CoerceUnsized support 
//
// Note2: I'm not sure the UnsafeCell is needed. But otherwise we'd have to 
// cast the *const to a *mut instead and using UnsafeCell makes me more sure
// that this isn't UB

//#[derive(Debug)]
struct RCellPtr<T: ?Sized, M: BitMask>(*const UnsafeCell<RCell<T, M>>);

impl<T, M: BitMask> RCellPtr<T, M> {
    fn new(t: T) -> Self {
        // Allocate trick from https://github.com/rust-lang/rust/issues/27700
        let mut v = Vec::with_capacity(1);
        v.push(UnsafeCell::new(RCell::new(t)));
        let z = v.as_mut_ptr();
        mem::forget(v);
        let r = RCellPtr(z);
        debug_assert_eq!(r.0 as *const (), r.get() as *const _ as *const ());
        r
    }

    #[inline]
    fn state(&self) -> State { self.get().state() }

    #[inline]
    fn check_drop(&self) {
        let m = self.get().mask.get().get();
        if m & 3 == 1 { return; } // Existing RefMut
        if (m & (M::mask(BM_REF) + M::mask(BM_STRONG))) != 0 { return; } // Existing Ref or Strong
        self.do_drop();
    }

    fn do_drop(&self) {
        let c = self.get();
        if c.state() != State::Dropped {
            self.inc(BM_STRONG); // Prevent double free in case drop_in_place does weird things
            c.set_state(State::Dropped);
            unsafe { ptr::drop_in_place(c.inner.get()) };
            debug_assert_eq!(c.state(), State::Dropped);
            self.dec(BM_STRONG);
            debug_assert_eq!(c.mask.get().get() & (M::mask(BM_REF) + M::mask(BM_STRONG)), 0);
        }
        if c.mask.get().get() & M::mask(BM_WEAK) != 0 { return };
        let _ = unsafe { Vec::from_raw_parts((*self.0).get(), 0, 1) };
    }

    #[inline]
    fn get_ref(&self) -> Result<Ref<T, M>, State> {
        let e = self.state();
        if e == State::Available || e == State::Borrowed {
            self.inc(BM_REF);
            Ok(Ref(RCellPtr(self.0), PhantomData))
        }
        else { Err(e) }
    }

    #[inline]
    fn get_refmut(&self) -> Result<RefMut<T, M>, State> {
        let e = self.state();
        if e == State::Available {
            self.get().set_state(State::BorrowedMut);
            Ok(RefMut(RCellPtr(self.0), PhantomData))
        }
        else { Err(e) }
    }

    #[inline]
    fn get_strong(&self) -> Result<Strong<T, M>, State> {
        let e = self.state();
        if e != State::Dropped {
            self.inc(BM_STRONG); Ok(Strong(RCellPtr(self.0), PhantomData))
        }
        else { Err(e) }
    }

    #[inline]
    fn get_weak(&self) -> Weak<T, M> {
        self.inc(BM_WEAK);
        Weak(RCellPtr(self.0))
    }

}

impl<T: ?Sized, M: BitMask> RCellPtr<T, M> {
    #[inline]
    fn get(&self) -> &RCell<T, M> { unsafe { &*(*self.0).get() }}

    #[inline]
    fn inc(&self, idx: usize) {
        let mut m = self.get().mask.get();
        m.inc(idx).unwrap();
        self.get().mask.set(m);
    }

    #[inline]
    fn dec(&self, idx: usize) {
        let mut m = self.get().mask.get();
        m.dec(idx);
        self.get().mask.set(m);
    }
}


impl<T: ?Sized + fmt::Debug, M: BitMask + fmt::Debug> fmt::Debug for RCellPtr<T, M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.get())
    }
}

/// An Rc reference which has immutable access to the inner value.
///
/// It's like a strong reference, and a immutably borrowed interior,
/// in the same struct.
#[derive(Debug)]
pub struct Ref<T, M: BitMask = u32>(RCellPtr<T, M>, PhantomData<RCell<T, M>>);

impl<T, M: BitMask> Ref<T, M> {
    #[inline]
    pub fn new(t: T) -> Self { RCellPtr::new(t).get_ref().unwrap() }

    #[inline]
    pub fn get(&self) -> Ref<T, M> { self.0.get_ref().unwrap() }

    #[inline]
    pub fn get_strong(&self) -> Strong<T, M> { self.0.get_strong().unwrap() }

    #[inline]
    pub fn get_weak(&self) -> Weak<T, M> { self.0.get_weak() }
}

impl<T, M: BitMask> Drop for Ref<T, M> {
    fn drop(&mut self) {
        debug_assert_eq!(self.0.state(), State::Borrowed);
        self.0.dec(BM_REF);
        self.0.check_drop();
    }
}

impl<T, M: BitMask> ops::Deref for Ref<T, M> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target { unsafe { &*self.0.get().inner.get() }}
}


impl<T, M: BitMask> Clone for Ref<T, M> {
    #[inline]
    fn clone(&self) -> Self { self.get() }
}


/// An Rc which has mutable access to the inner value. Only
/// one RefMut can exist, and cannot coexist with any Ref.
#[derive(Debug)]
pub struct RefMut<T, M: BitMask = u32>(RCellPtr<T, M>, PhantomData<RCell<T, M>>);

impl<T, M: BitMask> RefMut<T, M> {
    #[inline]
    pub fn new(t: T) -> Self { RCellPtr::new(t).get_refmut().unwrap() }

    #[inline]
    pub fn get_strong(&self) -> Strong<T, M> { self.0.get_strong().unwrap() }

    #[inline]
    pub fn get_weak(&self) -> Weak<T, M> { self.0.get_weak() }
}

impl<T, M: BitMask> Drop for RefMut<T, M> {
    fn drop(&mut self) {
        use std::thread;
        debug_assert_eq!(self.0.state(), State::BorrowedMut);
        let s = if thread::panicking() { State::Poisoned } else { State::Available };
        self.0.get().set_state(s);
        self.0.check_drop();
    }
}

impl<T, M: BitMask> ops::Deref for RefMut<T, M> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target { unsafe { &*self.0.get().inner.get() }}
}

impl<T, M: BitMask> ops::DerefMut for RefMut<T, M> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { &mut *self.0.get().inner.get() } }
}


/// A strong reference without access to the inner value.
///
/// To get immutable/mutable access, you need to use the 
/// get/get_mut functions to create Ref or RefMut references.
///
/// The inner value cannot be dropped while Strong, Ref or RefMut references exist.
#[derive(Debug)]
pub struct Strong<T, M: BitMask = u32>(RCellPtr<T, M>, PhantomData<RCell<T, M>>);

impl<T, M: BitMask> Strong<T, M> {
    #[inline]
    pub fn new(t: T) -> Self { RCellPtr::new(t).get_strong().unwrap() }

    #[inline]
    pub fn state(&self) -> State { self.0.state() }

    #[inline]
    pub fn get(&self) -> Ref<T, M> { self.0.get_ref().unwrap() }

    #[inline]
    pub fn get_mut(&self) -> RefMut<T, M> { self.0.get_refmut().unwrap() }

    #[inline]
    pub fn get_strong(&self) -> Strong<T, M> { self.0.get_strong().unwrap() }

    #[inline]
    pub fn get_weak(&self) -> Weak<T, M> { self.0.get_weak() }

    #[inline]
    pub fn try_get(&self) -> Result<Ref<T, M>, State> { self.0.get_ref() }

    #[inline]
    pub fn try_get_mut(&self) -> Result<RefMut<T, M>, State> { self.0.get_refmut() }
}

impl<T, M: BitMask> Drop for Strong<T, M> {
    fn drop(&mut self) {
        self.0.dec(BM_STRONG);
        self.0.check_drop();
    }
}

impl<T, M: BitMask> Clone for Strong<T, M> {
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
#[derive(Debug)]
pub struct Weak<T, M: BitMask = u32>(RCellPtr<T, M>);

impl<T, M: BitMask> Weak<T, M> {
    #[inline]
    pub fn state(&self) -> State { self.0.state() }

    #[inline]
    pub fn get(&self) -> Ref<T, M> { self.0.get_ref().unwrap() }

    #[inline]
    pub fn get_mut(&self) -> RefMut<T, M> { self.0.get_refmut().unwrap() }

    #[inline]
    pub fn get_strong(&self) -> Strong<T, M> { self.0.get_strong().unwrap() }

    #[inline]
    pub fn get_weak(&self) -> Weak<T, M> { self.0.get_weak() }

    #[inline]
    pub fn try_get(&self) -> Result<Ref<T, M>, State> { self.0.get_ref() }

    #[inline]
    pub fn try_get_mut(&self) -> Result<RefMut<T, M>, State> { self.0.get_refmut() }

    #[inline]
    pub fn try_get_strong(&self) -> Result<Strong<T, M>, State> { self.0.get_strong() }
}

impl<T, M: BitMask> Drop for Weak<T, M> {
    fn drop(&mut self) {
        self.0.dec(BM_WEAK);
        self.0.check_drop();
    }
}

impl<T, M: BitMask> Clone for Weak<T, M> {
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
    let z = Strong::<_, u32>::new(Dummy(&q));
    assert_eq!(z.state(), State::Available);
    let z2 = z.clone();
    drop(z);
    assert_eq!(z2.state(), State::Available);
    assert_eq!(q.get(), 11);
    drop(z2);
    assert_eq!(q.get(), 73);
}

