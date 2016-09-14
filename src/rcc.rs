use std::cell::{Cell, UnsafeCell};
use std::{thread, error, fmt, mem, ptr};
use std::ops::{Deref, DerefMut};
use std::marker::PhantomData;

// We don't use Rc, except for getting a !Send bound.
use std::rc::Rc;

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
    Poisoned = 2,
    Dropped = 3,
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



#[derive(Debug)]
struct RCell<T>(UnsafeCell<(UnsafeCell<T>, u32)>);

const STATE_MASK: u32 = 0x3;
const STRONG_MASK: u32 = 0x1fffc;
const WEAK_MASK: u32 = 0xfffe0000;

impl<T> RCell<T> {
    #[inline]
    fn inner(&self) -> &mut T { unsafe { &mut *(*self.0.get()).0.get() }}

    #[inline]
    fn get_mask(&self) -> u32 { unsafe { (*self.0.get()).1 }}

    #[inline]
    fn set_mask(&self, u: u32) { unsafe { (*self.0.get()).1 = u; }}

    #[inline]
    fn get_state(&self) -> State { State::from(self.get_mask() & STATE_MASK) }

    #[inline]
    fn set_state(&self, s: State) { 
        let mm = (self.get_mask() & !STATE_MASK) + (s as u32);
        self.set_mask(mm);
    }

    #[inline]
    fn get_strong(&self) -> u32 { (self.get_mask() & STRONG_MASK) >> 2 }

    #[inline]
    fn set_strong(&self, m: u32) {
        let mm = (self.get_mask() & !STRONG_MASK) + (m << 2);
        self.set_mask(mm);
    }

    #[inline]
    fn get_weak(&self) -> u32 { (self.get_mask() & WEAK_MASK) >> 17 }

    #[inline]
    fn set_weak(&self, m: u32) {
        if m > 0x7fff { panic!("Weak Rcc count overflow") }
        let mm = (self.get_mask() & !WEAK_MASK) + (m << 17);
        self.set_mask(mm);
    }

    #[inline]
    fn check_drop(&self) {
        if self.get_strong() != 0 || self.get_state() == State::Borrowed { return; }
        self.do_drop();
    }

    fn do_drop(&self) {
        if self.get_state() != State::Dropped {
            self.set_strong(1); // Prevent double free in case drop_in_place does weird things
            self.set_state(State::Dropped);
            unsafe { ptr::drop_in_place(self.inner()) };
            debug_assert_eq!(self.get_state(), State::Dropped);
            debug_assert_eq!(self.get_strong(), 1);
            self.set_strong(0);
        }
        if self.get_weak() != 0 { return };
        debug_assert_eq!(self.0.get() as *const _ as *const (), self as *const _ as *const ()); 
        let _ = unsafe { Vec::from_raw_parts(self.0.get(), 0, 1) };
    }

    fn new(t: T) -> Self { RCell(UnsafeCell::new((UnsafeCell::new(t), 0))) }

    fn try_get<'a>(&'a self) -> Result<RccRef<'a, T>, State> {
        match self.get_state() {
            State::Available => {
                self.set_state(State::Borrowed);
                Ok(RccRef(self, PhantomData))
            },
            m @ _ => Err(m)
        }
    }

    fn clone_strong<'a>(&'a self) -> Result<Rcc<'a, T>, State> {
        if self.get_state() == State::Dropped { return Err(State::Dropped) }
        let m = self.get_strong() + 1;
        if m > 0x7fff { panic!("Strong Rcc count overflow") }
        self.set_strong(m);
        Ok(Rcc(self, PhantomData))
    }

    fn clone_weak<'a>(&'a self) -> WRcc<'a, T> {
        let m = self.get_weak() + 1;
        if m > 0x7fff { panic!("Weak Rcc count overflow") }
        self.set_weak(m);
        WRcc(self, PhantomData)
    }
}


// If Shared or NonZero were stable, we'd use that instead,
// but now we use a reference to get NonZero optimizations anyway.

/// An alternative to `Rc<RefCell<T>>`, with less memory overhead, poisoning support, and no immutable references.
///
/// * 4 bytes overhead (compared to 12 or 24 for `Rc<RefCell<T>>`)
///
/// * Max 32767 strong pointers and 32767 weak pointers.
///
/// * One mutable reference, no multiple immutable references.
/// I e, if RefCell is a single-threaded RwLock, then this is a single-threaded Mutex.
///
/// * Poisoning support - after a panic during an active lock,
/// .get() will return an error. This can be reverted by calling unpoison(). 
///
/// * No CoerceUnsized support (might come later).
///
/// * Last but not least, just writing `.get()` is less characters than `.upgrade().unwrap().borrow_mut()`
/// that you would do with a `Weak<RefCell<T>>`.
///
/// # Example
/// ```
/// use reffers::rcc::{Rcc, State};
///
/// // Create a strong reference
/// let strong = Rcc::new(5i32);
///
/// // And a weak one
/// let weak = strong.clone_weak();
///
/// // Change the inner value
/// *weak.get() = 7i32;
///
/// // Inspect the change
/// {
///     let r = strong.get();
///     assert_eq!(*r, 7i32);
///
/// // We cannot change the value from the other reference
/// // now. It is still borrowed...
///     assert_eq!(weak.try_get().unwrap_err(), State::Borrowed);
/// }
///
/// // But now we can.
/// assert_eq!(strong.state(), State::Available);
/// assert_eq!(*strong.get(), 7i32);
///
/// // Drop the strong reference, this drops the inner value as well
/// drop(strong);
///
/// // We can't access the inner value, it has been dropped.
/// assert_eq!(weak.try_get().unwrap_err(), State::Dropped);
/// ```
#[derive(Debug)]
pub struct Rcc<'b, T: 'b>(&'b RCell<T>, PhantomData<Rc<T>>);

impl<'b, T: 'b> Rcc<'b, T> {
    pub fn new(t: T) -> Self {
        // Allocate trick from https://github.com/rust-lang/rust/issues/27700
        let mut v = Vec::with_capacity(1);
        v.push(RCell::new(t));
        v[0].set_strong(1);
        let z = v.as_mut_ptr();
        mem::forget(v);
        let zz = unsafe { &*z };
        debug_assert_eq!(zz as *const _, zz.0.get() as *const _);
        Rcc(zz, PhantomData)
    }

    #[inline]
    pub fn state(&self) -> State { self.0.get_state() }

    #[inline]
    /// Returns a reference to the inner value, or panics if the Rcc is unavailable.
    pub fn get<'a>(&'a self) -> RccRef<'a, T> { self.try_get().unwrap() }

    #[inline]
    /// Returns a reference to the inner value, or returns an error if the Rcc is unavailable.
    pub fn try_get<'a>(&'a self) -> Result<RccRef<'a, T>, State> { self.0.try_get() }

    /// If the Rcc is currently poisoned, this function can be used to return
    /// the Rcc to the "Available" state.
    pub fn unpoison(&self) -> Result<(), State> {
        let m = self.0.get_state();
        if m == State::Poisoned { self.0.set_state(State::Available); Ok(()) }
        else { Err(m) }
    }

    #[inline]
    pub fn clone_weak(&self) -> WRcc<'b, T> { self.0.clone_weak() }
}

impl<'b, T: 'b> Clone for Rcc<'b, T> {
    fn clone(&self) -> Self { self.0.clone_strong().unwrap() }
}

impl<'b, T: 'b> Drop for Rcc<'b, T> {
    fn drop(&mut self) {
        self.0.set_strong(self.0.get_strong() - 1);
        self.0.check_drop();
    }
}

/// Weak version of Rcc.
///
/// When no strong references or active borrows exist,
/// the inner value will be dropped (i e, its destructor will run).
/// After that, trying to get the inner value will not work.
/// All memory will not be released until all the weak references are gone too, though.
#[derive(Debug)]
pub struct WRcc<'b, T: 'b>(&'b RCell<T>, PhantomData<Rc<T>>);

impl<'b, T: 'b> WRcc<'b, T> {

    #[inline]
    pub fn state(&self) -> State { self.0.get_state() }

    #[inline]
    /// Returns a reference to the inner value, or panics if the Rcc is unavailable.
    pub fn get<'a>(&'a self) -> RccRef<'a, T> { self.try_get().unwrap() }

    #[inline]
    /// Returns a reference to the inner value, or returns an error if the Rcc is unavailable.
    pub fn try_get<'a>(&'a self) -> Result<RccRef<'a, T>, State> { self.0.try_get() }

    /// Creates a new strong reference from a weak one.
    ///
    /// Will return an error in case the inner value has already been dropped.
    #[inline]
    pub fn clone_strong(&self) -> Result<Rcc<'b, T>, State> { self.0.clone_strong() }
}

impl<'b, T: 'b> Clone for WRcc<'b, T> {
    fn clone(&self) -> Self { self.0.clone_weak() }
}

impl<'b, T: 'b> Drop for WRcc<'b, T> {
    fn drop(&mut self) {
        self.0.set_weak(self.0.get_weak() - 1);
        self.0.check_drop();
    }
}


/// Contains an active lock on the Rcc.
///
/// When dropped, the lock will be released. If dropped during a panic,
/// the Rcc will be poisoned.
#[derive(Debug)]
pub struct RccRef<'a, T: 'a>(&'a RCell<T>, PhantomData<Rc<T>>);

impl<'a, T: 'a> Drop for RccRef<'a, T> {
    fn drop(&mut self) {
        debug_assert_eq!(self.0.get_state(), State::Borrowed);
        self.0.set_state(if thread::panicking() { State::Poisoned } else { State::Available });
        self.0.check_drop();
    }
}

impl<'a, T: 'a> Deref for RccRef<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target { self.0.inner() }
}

impl<'a, T: 'a> DerefMut for RccRef<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target { self.0.inner() }
}


#[test]
fn rcc_basic() {
    let z = Rcc::new(5i32);
    assert_eq!(z.state(), State::Available);
    let z2 = z.clone();
    assert_eq!(z2.state(), State::Available);
    {
        let mut r = z2.get();
        assert_eq!(z.state(), State::Borrowed);
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
fn rcc_drop() {
    struct Dummy<'a>(&'a Cell<i32>);
    impl<'a> Drop for Dummy<'a> { fn drop(&mut self) { self.0.set(73) }}

    let q = Cell::new(11i32);
    let z = Rcc::new(Dummy(&q));
    assert_eq!(z.state(), State::Available);
    let z2 = z.clone();
    drop(z);
    assert_eq!(z2.state(), State::Available);
    assert_eq!(q.get(), 11);
    drop(z2);
    assert_eq!(q.get(), 73);
}

