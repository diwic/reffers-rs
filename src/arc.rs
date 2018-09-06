//! This is somewhat like an `Arc<RwLock<T>>`, but with only one usize of overhead, 
//! and the lock is a spinlock (there is no wait-and-sleep functionality). 
//!
//! Conceptually similar to rc, but this is a thread-safe version.
//!
//! # Example
//! ```
//! use std::thread;
//! use reffers::arcu::Strong;
//!
//! let s = Strong::<_>::new(987i32);
//! let s2 = s.clone();
//! thread::spawn(move || {
//!     *s2.get_refmut() = 654i32;
//! }).join().unwrap();
//! assert_eq!(*s.get_ref(), 654i32);
//! ```


use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};

use std::cell::UnsafeCell;
use std::{mem, ptr, fmt, ops, borrow, convert, hash, cmp, alloc};
use std::ptr::NonNull;
use std::marker::PhantomData;
use rc::{BitMask, State, CSlice};
use rc_bitmask::{BitMaskOps, BM_REF, BM_STRONG, BM_WEAK};

#[doc(hidden)]
pub struct ArcBox<T: ?Sized, M> {
    mask: AtomicUsize,
    _dummy: PhantomData<M>,
    inner: UnsafeCell<T>,
}

/// This is an implementation detail. Please don't mess with it.
///
/// It's for abstracting over sized and unsized types.
pub unsafe trait Repr: ::rc::Repr {
    #[doc(hidden)]
    unsafe fn deallocate_arc<M: BitMask>(NonNull<ArcBox<Self::Store, M>>);
}

unsafe fn allocate_mem<T, M: BitMask>(layout: alloc::Layout, data: T) -> NonNull<ArcBox<T, M>> {
    let z = alloc::alloc(layout) as *mut ArcBox<T, M>;
    let z = NonNull::new(z).unwrap(); // Panic on alloc failure
    ptr::write(z.as_ptr(), ArcBox {
        mask: AtomicUsize::new(Default::default()),
        _dummy: PhantomData,
        inner: UnsafeCell::new(data),
    });
    z
}

unsafe impl<T> Repr for T {
    unsafe fn deallocate_arc<M: BitMask>(s: NonNull<ArcBox<Self::Store, M>>) {
        let layout = alloc::Layout::new::<ArcBox<Self::Store, M>>();
        alloc::dealloc(s.as_ptr() as *mut u8, layout);
    }
}

fn cslice_len_to_layout<T, M: BitMask>(l: usize) -> alloc::Layout {
    let self_size = mem::size_of::<ArcBox<CSlice<T>, M>>();
    let t_size = mem::size_of::<T>();
    let align = mem::align_of::<ArcBox<CSlice<T>, M>>();
    let data_bytes = l * t_size;
    alloc::Layout::from_size_align(self_size + data_bytes, align).unwrap()
}


unsafe impl Repr for str {
    unsafe fn deallocate_arc<M: BitMask>(s: NonNull<ArcBox<Self::Store, M>>) {
        let layout = cslice_len_to_layout::<u8, M>((*s.as_ref().inner.get()).get_len());
        alloc::dealloc(s.as_ptr() as *mut u8, layout);
    }
}

unsafe impl<T> Repr for [T] {
    unsafe fn deallocate_arc<M: BitMask>(s: NonNull<ArcBox<Self::Store, M>>) {
        let layout = cslice_len_to_layout::<T, M>((*s.as_ref().inner.get()).get_len());
        alloc::dealloc(s.as_ptr() as *mut u8, layout);
    }
}


struct ArcPtr<T: ?Sized + Repr, M>(NonNull<ArcBox<T::Store, M>>, PhantomData<T::Store>);

impl<T: ?Sized + Repr, M: BitMask<Num=usize>> ArcPtr<T, M> {
    #[inline]
    fn load_mask(&self) -> M {
        let u: usize = unsafe { self.0.as_ref().mask.load(SeqCst) };
        let mut r: M = Default::default();
        r.set_inner(u);
        r
    }

    #[inline]
    fn store_mask(&self, new_value: M, old_value: M) -> Result<(), M> {
        let u_new = new_value.get_inner();
        // println!("Storing mask: {:?} {:?}", u_new, new_value.is_alive());
        let u_old = old_value.get_inner();
        let u_cmp = unsafe { self.0.as_ref().mask.compare_and_swap(u_old, u_new, SeqCst) };
        if u_old == u_cmp { Ok(()) }
        else {
            let mut r: M = Default::default();
            r.set_inner(u_cmp);
            Err(r)
        }
    }

    fn cas_loop<R, F: FnMut(M) -> (R, Option<M>)>(&self, mut f: F) -> R {
        let mut m_prev = self.load_mask();
        loop {
            let (r, m_new) = f(m_prev);
            if let Some(m_new) = m_new {
                match self.store_mask(m_new, m_prev) {
                    Err(e) => { m_prev = e; continue; },
                    Ok(_) => { return r; }
                }
            } else { return r; }
        }
    }

    fn get_refmut(&self) -> Result<RefMut<T, M>, State> {
        self.cas_loop(|mut m| {
            let s: State = m.get_state().into();
            if s != State::Available { return (Err(s), None); }
            m.set_state(State::BorrowedMut as u8);
            (Ok(()), Some(m))
        }).map(|_| RefMut(ArcPtr(self.0, PhantomData)))
    }

    fn get_ref(&self) -> Result<Ref<T, M>, State> {
        self.cas_loop(|mut m| {
            let s = m.get_state();
            if s != State::Available as u8 { return (Err(s.into()), None); }
            if let Err(e) = m.inc(BM_REF) { return (Err(e.into()), None); }
            (Ok(()), Some(m))
        }).map(|_| Ref(ArcPtr(self.0, PhantomData)))
    }

    fn get_strong(&self) -> Result<Strong<T, M>, State> {
        self.cas_loop(|mut m| {
            let s = m.get_state();
            if s == State::Dropped as u8 { return (Err(s.into()), None); }
            if let Err(e) = m.inc(BM_STRONG) { return (Err(e.into()), None); }
            (Ok(()), Some(m))
        }).map(|_| Strong(ArcPtr(self.0, PhantomData)))
    }

    fn get_weak(&self) -> Result<Weak<T, M>, State> {
        self.cas_loop(|mut m| {
            if let Err(e) = m.inc(BM_WEAK) { return (Err(e.into()), None); }
            (Ok(()), Some(m))
        }).map(|_| Weak(ArcPtr(self.0, PhantomData)))
    }

    fn unpoison(&self) -> Result<(), State> {
        self.cas_loop(|mut m| {
            let s: State = m.get_state().into();
            if s != State::Poisoned { return (Err(s), None); }
            m.set_state(State::Available as u8);
            (Ok(()), Some(m))
        })
    }

    #[inline]
    fn value_ptr(&self) -> *mut T { T::convert(unsafe { self.0.as_ref().inner.get() }) }

    fn try_drop(&mut self, idx: Option<usize>) {
        let mut should_dealloc = false;
        let mut should_drop = None;
        self.cas_loop(|mut mask| {
            // Is this the last reference?
            if let Some(i) = idx { 
                mask.dec(i);
            } else {
                use std::thread;
                debug_assert_eq!(mask.get_state(), State::BorrowedMut as u8);
                mask.set_state(if thread::panicking() { State::Poisoned } else { State::Available } as u8);
            }
            if mask.is_alive() { return ((), Some(mask)) }

            should_dealloc = mask.is_zero(BM_WEAK);
            if mask.get_state() == State::Dropped as u8 { return ((), None) }

            // Prepare for drop
            mask.set_state(State::Dropped as u8);
            let used_ref = mask.inc(BM_REF).is_ok();
            if !used_ref { mask.inc(BM_STRONG).unwrap(); }
            should_drop = Some(used_ref);
            ((), Some(mask))
        });

        if let Some(used_ref) = should_drop {
            unsafe { ptr::drop_in_place(T::convert(self.0.as_ref().inner.get())) };
            self.cas_loop(|mut mask| {
                debug_assert_eq!(mask.get_state(), State::Dropped as u8);
                mask.dec(if used_ref { BM_REF } else { BM_STRONG });
                ((), Some(mask))
            });
        }

        if should_dealloc {
          unsafe { T::deallocate_arc(self.0) };
        }

    }

    fn state(&self) -> State { self.load_mask().into() }
}

impl<T: ?Sized + Repr, M: BitMask<Num=usize> + fmt::Debug> fmt::Debug for ArcPtr<T, M> 
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.state())
    }
}


impl<T, M: BitMask> ArcPtr<T, M> {
    fn new(t: T) -> Self {
        let layout = alloc::Layout::new::<ArcBox<T,M>>();
        let z = unsafe { allocate_mem(layout, t) };
        let r = ArcPtr(z, PhantomData);
        // debug_assert_eq!(r.0.as_ptr() as *const (), r.get() as *const _ as *const ());
        r
    }
}

impl<M: BitMask> ArcPtr<str, M> {
    fn new_str(t: &str) -> Self {
        let len = t.len();
        let layout = cslice_len_to_layout::<u8, M>(len);
        let mut z = unsafe { allocate_mem(layout, CSlice::new(len)) };
        unsafe { ptr::copy_nonoverlapping(t.as_ptr(), (*z.as_mut().inner.get()).data_ptr_mut(), len) };

        ArcPtr(z, PhantomData)
    }
}

impl<T, M: BitMask> ArcPtr<[T], M> {
    fn new_slice<I: ExactSizeIterator<Item=T>>(iter: I) -> Self {
        let len = iter.len();
        let layout = cslice_len_to_layout::<T, M>(len);
        unsafe {
            let z = allocate_mem(layout, CSlice::new(len));
            let mut r: Self = ArcPtr(z, PhantomData);
            let p = (*r.0.as_mut().inner.get()).data_ptr_mut();
            for (idx, item) in iter.enumerate() {
                ptr::write(p.offset(idx as isize), item)
            }
            r
        }
    }
}

/// An Arc which has mutable access to the inner value. Only
/// one RefMut can exist, and cannot coexist with any Ref.
#[derive(Debug)]
pub struct RefMut<T: ?Sized + Repr, M: BitMask<Num=usize> = usize>(ArcPtr<T, M>);

new_ref!(RefMut, ArcPtr, get_refmut, BitMask<Num=usize>);

impl<T: ?Sized + Repr, M: BitMask<Num=usize>> RefMut<T, M> {
    impl_ref_all!();
}

impl_deref_and_friends!(RefMut, BitMask<Num=usize>);

impl<T: ?Sized + Repr, M: BitMask<Num=usize>> ops::DerefMut for RefMut<T, M> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { &mut *self.0.value_ptr() }}
}

impl_arc_all!(RefMut, None);

// This is safe because there can only be one RefMut
unsafe impl<T: Send, M: Send + BitMask<Num=usize>> Sync for RefMut<T, M> {}


/// An Rc reference which has immutable access to the inner value.
///
/// It's like a strong reference, and a immutably borrowed interior,
/// in the same struct.
#[derive(Debug)]
pub struct Ref<T: ?Sized + Repr, M: BitMask<Num=usize> = usize>(ArcPtr<T, M>);

new_ref!(Ref, ArcPtr, get_ref, BitMask<Num=usize>);

impl_arc_all!(Ref, Some(BM_REF));

impl<T: ?Sized + Repr, M: BitMask<Num=usize>> Ref<T, M> {
    impl_get_ref!();
    impl_ref_all!();
}

impl_deref_and_friends!(Ref, BitMask<Num=usize>);

impl<T: ?Sized + Repr, M: BitMask<Num=usize>> Clone for Ref<T, M> {
    #[inline]
    fn clone(&self) -> Self { self.0.get_ref().unwrap() }
}


// This requires T: Sync because there can be many Refs doing deref in parallel
unsafe impl<T: Send + Sync, M: Send + BitMask<Num=usize>> Sync for Ref<T, M> {}

/// A strong reference without access to the inner value.
///
/// To get immutable/mutable access, you need to use the 
/// get_ref/get_refmut functions to create Ref or RefMut references.
///
/// The inner value cannot be dropped while Strong, Ref or RefMut references exist.
#[derive(Debug)]
pub struct Strong<T: ?Sized + Repr, M: BitMask<Num=usize> = usize>(ArcPtr<T, M>);

new_ref!(Strong, ArcPtr, get_strong, BitMask<Num=usize>);

impl_arc_all!(Strong, Some(BM_STRONG));

impl<T: ?Sized + Repr, M: BitMask<Num=usize>> Strong<T, M> {
    impl_get_refmut!();
    impl_get_ref!();
    impl_ref_all!();
}

impl<T: ?Sized + Repr, M: BitMask<Num=usize>> Clone for Strong<T, M> {
    #[inline]
    fn clone(&self) -> Self { self.0.get_strong().unwrap() }
}

// This is safe because there is no way to access the interior
unsafe impl<T: Send, M: Send + BitMask<Num=usize>> Sync for Strong<T, M> {}


/// A weak reference without access to the inner value.
///
/// To get immutable/mutable access, you need to use the 
/// get_ref/get_refmut functions to create Ref or RefMut references.
///
/// If only weak references exist to the inner value,
/// the inner value will be dropped, and can no longer be accessed.
#[derive(Debug)]
pub struct Weak<T: ?Sized + Repr, M: BitMask<Num=usize> = usize>(ArcPtr<T, M>);

impl_arc_all!(Weak, Some(BM_WEAK));

impl<T: ?Sized + Repr, M: BitMask<Num=usize>> Clone for Weak<T, M> {
    #[inline]
    fn clone(&self) -> Self { self.0.get_weak().unwrap() }
}

impl<T: ?Sized + Repr, M: BitMask<Num=usize>> Weak<T, M> {
    impl_get_refmut!();
    impl_get_ref!();
    impl_ref_all!();
}

// This is safe because there is no way to access the interior
unsafe impl<T: Send, M: Send + BitMask<Num=usize>> Sync for Weak<T, M> {}


#[test]
fn arc_basic() {
    let z: Strong<_> = Strong::new(5i32);
    assert_eq!(z.state(), State::Available);
    let z2 = z.clone();
    assert_eq!(z2.state(), State::Available);
    {
        let mut r = z2.get_refmut();
        assert_eq!(z.state(), State::BorrowedMut);
        assert_eq!(*r, 5i32);
        *r = 6i32;
        assert!(z.try_get_ref().is_err());
        assert_eq!(z.state(), State::BorrowedMut);
    }
    assert_eq!(z2.state(), State::Available);
    assert_eq!(*z.get_ref(), 6i32);
    drop(z2);
    assert_eq!(*z.get_ref(), 6i32);
}

#[test]
fn arc_drop() {
    use std::cell::Cell;
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
fn arc_str() {
    let s = Ref::<_>::new_str("Hello world!");
    assert_eq!(&*s, "Hello world!");
    let _q = s.get_strong();
    let r = s.get_weak();
    drop(s);
    assert_eq!(&*r.get_refmut(), "Hello world!");
}

#[test]
fn arc_slice() {
    let v = vec![String::from("abc"), String::from("def")];
    let mut s = RefMut::<[String]>::new_slice(v.into_iter());
    s[1] = String::from("ghi");
    assert_eq!(&*s[0], "abc");
    assert_eq!(&*s[1], "ghi");
}

#[test]
fn arc_send() {
    let s = Strong::<_>::new(987i32);
    let s2 = s.clone();
    ::std::thread::spawn(move || {
        *s2.get_refmut() = 654i32;
    }).join().unwrap();
    assert_eq!(*s.get_ref(), 654i32);

    let s3 = s.get_ref();    
    ::std::thread::spawn(move || {
        assert_eq!(*s3, 654i32);
    }).join().unwrap();

}

