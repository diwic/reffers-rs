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
//! * Last but not least, just writing `.get_ref()` is less characters than `.upgrade().unwrap().borrow()`
//! that you would do with a `Weak<RefCell<T>>`.
//!
//! # Four structs
//!
//! * `Strong` - A strong reference to the inner value, keeping it from being dropped.
//!   To access the inner value, use `.get_ref()` or `.get_refmut()` to create `Ref` and `RefMut` structs.
//!
//! * `Ref` - A strong reference to the inner value, with immutable access to the inner value.
//!
//! * `RefMut` - A strong reference to the inner value, with mutable access to the inner value.
//!   There can only be one RefMut reference; and when Ref references exist, there can be no RefMut references.
//!
//! * `Weak` - A weak reference, the inner value will be dropped when no other types of references exist.
//!   This can be helpful w r t breaking up cycles of Strong references.
//!   There is no need to "upgrade" a weak reference to a strong reference just to access the inner value -
//!   just call `.get_ref()` or `.get_refmut()` on the weak reference directly.
//!
//! Where applicable, there are `.get_strong()` and `.get_weak()` functions that create new Strong and
//! Weak references. There are also `.try_get_ref()`, `.try_get_refmut()` etc functions that return an error instead
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
//! *weak.get_refmut() = 7i32;
//!
//! // Inspect the change
//! {
//!     let r = strong.get_ref();
//!     assert_eq!(*r, 7i32);
//!
//!     // We cannot change the value from the other reference
//!     // now. It is still borrowed...
//!     assert_eq!(weak.try_get_refmut().unwrap_err(), State::Borrowed);
//! }
//!
//! // But now we can.
//! assert_eq!(strong.state(), State::Available);
//! *strong.get_refmut() = 9i32;
//!
//! // Drop the strong reference, this drops the inner value as well
//! drop(strong);
//!
//! // We can't access the inner value, it has been dropped.
//! assert_eq!(weak.try_get_ref().unwrap_err(), State::Dropped);
//! ```

use std::cell::{Cell, UnsafeCell};
use std::{fmt, mem, ptr, error, ops, borrow, convert, slice, hash, cmp, alloc};
use std::ptr::NonNull;
use std::marker::PhantomData;

use rc_bitmask::*;

pub use rc_bitmask::BitMask;


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

impl<M: BitMask> From<M> for State {
    fn from(m2: M) -> State {
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
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", error::Error::description(self))
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
        m2.set_state(s);
        self.mask.set(m2);
    }

    pub fn try_get<'a>(&'a self) -> Result<RCellRef<'a, T, M>, State> {
        let s = self.state();
        if s != State::Available && s != State::Borrowed { return Err(s); }

        let mut m = self.mask.get();
        m.inc(BM_REF)?;
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

impl<T> CSlice<T> {
    pub (crate) fn new(len: usize) -> Self {
        assert!(len <= u32::max_value() as usize);
        CSlice { len: len as u32, data: [] }
    }
    pub (crate) fn get_len(&self) -> usize { self.len as usize }
    pub (crate) fn data_ptr_mut(&mut self) -> *mut T { self.data.as_mut_ptr() }
}

fn cslice_len_to_layout<T, M: BitMask>(l: usize) -> alloc::Layout {
    let self_size = mem::size_of::<UnsafeCell<RCell<CSlice<T>, M>>>();
    let t_size = mem::size_of::<T>();
    let align = mem::align_of::<UnsafeCell<RCell<CSlice<T>, M>>>();
    let data_bytes = l * t_size;
    alloc::Layout::from_size_align(self_size + data_bytes, align).unwrap()
}


/// This is an implementation detail. Please don't mess with it.
///
/// It's for abstracting over sized and unsized types.
pub unsafe trait Repr {
    type Store;
    #[doc(hidden)]
    fn convert(*mut Self::Store) -> *mut Self;
    #[doc(hidden)]
    unsafe fn deallocate_mem<M: BitMask>(&mut UnsafeCell<RCell<Self::Store, M>>);
}

// Sized types, no problem here
unsafe impl<T> Repr for T {
    type Store = T;
    #[inline]
    fn convert(s: *mut T) -> *mut T { s }
    unsafe fn deallocate_mem<M: BitMask>(s: &mut UnsafeCell<RCell<Self::Store, M>>) {
        let layout = alloc::Layout::new::<UnsafeCell<RCell<T,M>>>();
        alloc::dealloc(s as *mut _ as *mut u8, layout);
    }
}

unsafe impl<T> Repr for [T] {
    type Store = CSlice<T>;
    #[inline]
    fn convert(s: *mut CSlice<T>) -> *mut [T] {
        unsafe { slice::from_raw_parts_mut((*s).data.as_mut_ptr(), (*s).len as usize) }
    }
    unsafe fn deallocate_mem<M: BitMask>(s: &mut UnsafeCell<RCell<Self::Store, M>>) {
        let layout = cslice_len_to_layout::<T, M>((*(*s.get()).inner.get()).len as usize);
        alloc::dealloc(s as *mut _ as *mut u8, layout);
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
        let layout = cslice_len_to_layout::<u8, M>((*(*s.get()).inner.get()).len as usize);
        alloc::dealloc(s as *mut _ as *mut u8, layout);
    }
}


// Note: This would benefit from CoerceUnsized support
//
// Note2: I'm not sure the UnsafeCell is needed. But otherwise we'd have to
// cast the *const to a *mut instead and using UnsafeCell makes me more sure
// that this isn't UB

//#[derive(Debug)]
struct RCellPtr<T: ?Sized + Repr, M: BitMask>(NonNull<UnsafeCell<RCell<T::Store, M>>>, PhantomData<T>);

unsafe fn allocate_mem<T, M: BitMask>(layout: alloc::Layout, data: T) -> NonNull<UnsafeCell<RCell<T,M>>> {
    let z = alloc::alloc(layout) as *mut UnsafeCell<RCell<T, M>>;
    let z = NonNull::new(z).unwrap(); // Panic on alloc failure
    ptr::write(z.as_ptr(), UnsafeCell::new(RCell::new(data)));
    z
}

impl<M: BitMask> RCellPtr<str, M> {
    fn new_str(t: &str) -> Self {
        let len = t.len();
        let layout = cslice_len_to_layout::<u8, M>(len);
        let mut z = unsafe { allocate_mem(layout, CSlice::new(len)) };
        unsafe { ptr::copy_nonoverlapping(t.as_ptr(), (*(*z.as_mut().get()).inner.get()).data.as_mut_ptr(), len) };
        RCellPtr(z, PhantomData)
    }
}


impl<T, M: BitMask> RCellPtr<[T], M> {
    fn new_slice<I: ExactSizeIterator<Item=T>>(iter: I) -> Self {
        let len = iter.len();
        let layout = cslice_len_to_layout::<T, M>(len);
        unsafe {
            let z = allocate_mem(layout, CSlice::new(len));
            let r: Self = RCellPtr(z, PhantomData);
            let p = (*r.get().inner.get()).data.as_mut_ptr();
            for (idx, item) in iter.enumerate() {
                ptr::write(p.offset(idx as isize), item)
            }
            r
        }
    }
}

impl<T, M: BitMask> RCellPtr<T, M> {
    fn new(t: T) -> Self {
        let layout = alloc::Layout::new::<UnsafeCell<RCell<T,M>>>();
        let z = unsafe { allocate_mem(layout, t) };
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
            self.inc(BM_STRONG)?;
            Ok(Strong(RCellPtr(self.0, PhantomData), PhantomData))
        }
        else { Err(e) }
    }

    #[inline]
    fn get_weak(&self) -> Result<Weak<T, M>, State> {
        self.inc(BM_WEAK)?;
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
            self.inc(BM_REF)?;
            Ok(Ref(RCellPtr(self.0, PhantomData), PhantomData))
        }
        else { Err(e) }
    }

    #[inline]
    fn state(&self) -> State { self.get().state() }

    #[inline]
    fn inc(&self, idx: usize) -> Result<(), State> {
        let mut m = self.get().mask.get();
        m.inc(idx)?;
        self.get().mask.set(m);
        Ok(())
    }

    #[inline]
    fn dec(&self, idx: usize) {
        let mut m = self.get().mask.get();
        m.dec(idx);
        self.get().mask.set(m);
    }

    #[inline]
    fn unpoison(&self) -> Result<(), State> { self.get().unpoison() }
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

impl_deref_and_friends!(Ref, BitMask);

impl<T: ?Sized + Repr, M: BitMask> Clone for Ref<T, M> {
    #[inline]
    fn clone(&self) -> Self { self.get_ref() }
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

impl_deref_and_friends!(RefMut, BitMask);

impl<T: ?Sized + Repr, M: BitMask> ops::DerefMut for RefMut<T, M> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { &mut *self.0.value_ptr() }}
}


/// A strong reference without access to the inner value.
///
/// To get immutable/mutable access, you need to use the
/// get_ref/get_refmut functions to create Ref or RefMut references.
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
/// get_ref/get_refmut functions to create Ref or RefMut references.
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
        let mut r = z2.get_refmut();
        assert_eq!(z.state(), State::BorrowedMut);
        assert_eq!(*r, 5i32);
        *r = 6i32;
        assert!(z.try_get_ref().is_err());
    }
    assert_eq!(z2.state(), State::Available);
    assert_eq!(*z.get_ref(), 6i32);
    drop(z2);
    assert_eq!(*z.get_ref(), 6i32);
}


#[test]
fn rc_drop() {
    struct Dummy<'a>(&'a Cell<i32>);
    impl<'a> Drop for Dummy<'a> {
        fn drop(&mut self) {
            assert!(self.0.get() != 73);
            self.0.set(73);
        }
    }

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
    assert_eq!(q2.get(), 12);
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
    assert_eq!(&*r.get_refmut(), "Hello world!");
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
