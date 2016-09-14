use std::cell::{Cell, UnsafeCell};
use std::{thread, error, fmt, mem, ptr};
use std::ops::{Deref, DerefMut};
use std::marker::PhantomData;

/// A RefCell with poisoning and just one mutable reference, no immutable references.
///
/// Overhead is one byte.
#[derive(Debug)]
pub struct MCell<T> {
    inner: UnsafeCell<T>,
    mask: Cell<u8>,
}

pub struct MCellRef<'a, T: 'a>(&'a MCell<T>);

impl<'a, T: 'a> Drop for MCellRef<'a, T> {
    fn drop(&mut self) {
        let mut m = self.0.mask.get();
        debug_assert_eq!(m & 3, 1);
        m = m & !3;
        if thread::panicking() { m = m | 2 };
        self.0.mask.set(m); 
    }
}

impl<'a, T: 'a> Deref for MCellRef<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target { unsafe { & *self.0.inner.get() } }
}

impl<'a, T: 'a> DerefMut for MCellRef<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { &mut *self.0.inner.get() } }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum State {
    Available = 0,
    Borrowed = 1,
    Dropped = 2,
    Poisoned = 3,
}

impl From<u8> for State {
   fn from(q: u8) -> State {
        match q & 3 {
            0 => State::Available,
            1 => State::Borrowed,
            2 => State::Poisoned,
            3 => State::Dropped,
            _ => unreachable!()
        }
   }
}

impl From<u32> for State {
   fn from(q: u32) -> State { State::from(q as u8) }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", (self as &error::Error).description())
    }
}


impl error::Error for State {
    fn description(&self) -> &str {
        match *self {
            State::Available => "available",
            State::Borrowed => "borrowed",
            State::Poisoned => "poisoned",
            State::Dropped => "dropped",
        }
    }
}

impl<T> MCell<T> {
    pub fn new(t: T) -> Self {
        MCell { inner: UnsafeCell::new(t), mask: Cell::new(0) }
    }

    #[inline]
    pub fn get<'a>(&'a self) -> MCellRef<'a, T> { self.try_get().unwrap() }

    #[inline]
    pub fn try_get<'a>(&'a self) -> Result<MCellRef<'a, T>, State> {
        let m = self.mask.get();
        if m & 3 == 0 {
            self.mask.set(m | 1);
            Ok(MCellRef(self))
        } else {
            Err(State::from(m))
        } 
    }

    pub fn state(&self) -> State { State::from(self.mask.get()) }

    pub fn unpoison(&self) -> Result<&Self, State> {
        let m = self.mask.get();
        if m & 3 == 2 {
            self.mask.set(m & !3);
            Ok(self)
        } else {
            Err(State::from(m))
        }
    }
}



struct RCell<T> {
    inner: UnsafeCell<T>,
    mask: Cell<u32>,
}

const STATE_MASK: u32 = 0x3;
const STRONG_MASK: u32 = 0x1fffc;
const WEAK_MASK: u32 = 0xfffe0000;

impl<T> RCell<T> {
    #[inline]
    fn get_state(&self) -> State { State::from(self.mask.get() & STATE_MASK) }
    fn set_state(&self, s: State) { 
        let mm = (self.mask.get() & !STATE_MASK) + (s as u32);
        self.mask.set(mm);
    }
    #[inline]
    fn get_strong(&self) -> u32 { (self.mask.get() & STRONG_MASK) >> 2 }
    fn set_strong(&self, m: u32) {
        if m > 0x7fff { panic!("Strong Rcc count overflow") }
        let mm = (self.mask.get() & !STRONG_MASK) + (m << 2);
        self.mask.set(mm);
    }
    #[inline]
    fn get_weak(&self) -> u32 { (self.mask.get() & WEAK_MASK) >> 9 }
    fn set_weak(&self, m: u32) {
        if m > 0x7fff { panic!("Weak Rcc count overflow") }
        let mm = (self.mask.get() & !WEAK_MASK) + (m << 9);
        self.mask.set(mm);
    }

    fn check_drop(&self) {
        if self.get_strong() != 0 || self.get_state() == State::Borrowed { return; }
        if self.get_state() != State::Dropped {
            self.set_state(State::Dropped);
            unsafe { ptr::drop_in_place(self.inner.get()) };
            debug_assert_eq!(self.get_state(), State::Dropped);
            debug_assert_eq!(self.get_strong(), 0);
        }
        if self.get_weak() != 0 { return };
        let _ = unsafe { Vec::from_raw_parts(self as *const _ as *mut Self, 0, 1) };
    }
}

// If NonZero, Shared, etc were all stable, we'd use that instead,
// but now we use a &'static to get NonZero optimizations.

/// An alternative to `Rc<RefCell<T>>`, with less memory overhead.
///
/// * 4 bytes overhead (compared to 12 or 24 for `Rc<RefCell<T>>`)
///
/// * Max 32767 strong pointers and 32767 weak pointers.
///
/// * One mutable reference. (No multiple immutable references.)
///
/// * Poisoning support
///
/// * No CoerceUnsized support (might come later).
pub struct Rcc<'b, T: 'b>(&'b RCell<T>, PhantomData<T>);

impl<'b, T: 'b> Rcc<'b, T> {
    pub fn new(t: T) -> Self {
        // Allocate trick from https://github.com/rust-lang/rust/issues/27700
        let mut v = Vec::with_capacity(1);
        v.push(RCell { inner: UnsafeCell::new(t), mask: Cell::new(0) });
        v[0].set_strong(1);
        let z = v.as_mut_ptr();
        mem::forget(v);
        Rcc(unsafe { &*z }, PhantomData)
    }

    pub fn state(&self) -> State { self.0.get_state() }

    #[inline]
    pub fn get<'a>(&'a self) -> RcRef<'a, T> { self.try_get().unwrap() }

    #[inline]
    pub fn try_get<'a>(&'a self) -> Result<RcRef<'a, T>, State> {
        match self.0.get_state() {
            State::Available => {
                self.0.set_state(State::Borrowed);
                Ok(RcRef(self.0, PhantomData))
            },
            m @ _ => Err(m)
        }
    }
}

impl<'b, T: 'b> Clone for Rcc<'b, T> {
    fn clone(&self) -> Self { self.0.set_strong(self.0.get_strong() + 1); Rcc(self.0, PhantomData) }
}

impl<'b, T: 'b> Drop for Rcc<'b, T> {
    fn drop(&mut self) {
        self.0.set_strong(self.0.get_strong() - 1);
        self.0.check_drop();
    }
}

pub struct RcRef<'a, T: 'a>(&'a RCell<T>, PhantomData<T>);

impl<'a, T: 'a> Drop for RcRef<'a, T> {
    fn drop(&mut self) {
        debug_assert_eq!(self.0.get_state(), State::Borrowed);
        self.0.set_state(if thread::panicking() { State::Poisoned } else { State::Available });
        self.0.check_drop();
    }
}

impl<'a, T: 'a> Deref for RcRef<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target { unsafe { & *self.0.inner.get() } }
}

impl<'a, T: 'a> DerefMut for RcRef<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { &mut *self.0.inner.get() } }
}

