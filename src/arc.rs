//! This is somewhat like an `Arc<RwLock<T>>`, but with only one usize of overhead, 
//! and the lock is a spinlock (there is no wait-and-sleep functionality). 
//!
//! Conceptually similar to rc, but this is a thread-safe version.

use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};

use std::cell::UnsafeCell;
use std::{mem, ptr, fmt, ops};
// error, ops, borrow, convert, slice, hash, cmp};
use std::ptr::NonNull;
use std::marker::PhantomData;
use rc::{BitMask, State};
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

fn allocate<T, M>(capacity: usize, data: T) -> NonNull<ArcBox<T, M>> {
    // Allocate trick from https://github.com/rust-lang/rust/issues/27700
    debug_assert!(capacity > 0);
    let mut v = Vec::with_capacity(capacity);
    v.push(ArcBox {
        mask: AtomicUsize::new(Default::default()),
        _dummy: PhantomData,
        inner: UnsafeCell::new(data),
    });
    let z = v.as_mut_ptr();
    mem::forget(v);
    debug_assert!(z != ptr::null_mut());
    unsafe { NonNull::new_unchecked(z) }
}

unsafe impl<T> Repr for T {
    unsafe fn deallocate_arc<M: BitMask>(s: NonNull<ArcBox<Self::Store, M>>) {
        let _ = Vec::from_raw_parts(s.as_ptr(), 0, 1);
    }
}

unsafe impl Repr for str {
    unsafe fn deallocate_arc<M: BitMask>(_: NonNull<ArcBox<Self::Store, M>>) {
        unimplemented!();
    }
}

unsafe impl<T> Repr for [T] {
    unsafe fn deallocate_arc<M: BitMask>(_: NonNull<ArcBox<Self::Store, M>>) {
        unimplemented!();
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
        let z = allocate(1, t);
        let r = ArcPtr(z, PhantomData);
        // debug_assert_eq!(r.0.as_ptr() as *const (), r.get() as *const _ as *const ());
        r
    }
}

impl<M: BitMask> ArcPtr<str, M> {
    fn new_str(_t: &str) -> Self { unimplemented!() }
}

impl<T, M: BitMask> ArcPtr<[T], M> {
    fn new_slice<I: ExactSizeIterator<Item=T>>(_iter: I) -> Self { unimplemented!() }
}

#[derive(Debug)]
pub struct RefMut<T: ?Sized + Repr, M: BitMask<Num=usize> = usize>(ArcPtr<T, M>);

new_ref!(RefMut, ArcPtr, get_refmut, BitMask<Num=usize>);

impl<T: ?Sized + Repr, M: BitMask<Num=usize>> RefMut<T, M> {
    impl_ref_all!();
}

impl<T: ?Sized + Repr + Send, M: BitMask<Num=usize>> ops::Deref for RefMut<T, M> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target { unsafe { &*self.0.value_ptr() }}
}

impl<T: ?Sized + Repr + Send, M: BitMask<Num=usize>> ops::DerefMut for RefMut<T, M> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { &mut *self.0.value_ptr() }}
}

impl_arc_all!(RefMut, None);



#[derive(Debug)]
pub struct Ref<T: ?Sized + Repr, M: BitMask<Num=usize> = usize>(ArcPtr<T, M>);

new_ref!(Ref, ArcPtr, get_ref, BitMask<Num=usize>);

impl_arc_all!(Ref, Some(BM_REF));

impl<T: ?Sized + Repr, M: BitMask<Num=usize>> Ref<T, M> {
    impl_get_ref!();
    impl_ref_all!();
}

impl<T: ?Sized + Repr, M: BitMask<Num=usize>> Clone for Ref<T, M> {
    #[inline]
    fn clone(&self) -> Self { self.0.get_ref().unwrap() }
}

impl<T: ?Sized + Repr + Send + Sync, M: BitMask<Num=usize>> ops::Deref for Ref<T, M> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target { unsafe { &*self.0.value_ptr() }}
}



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

    // let q2 = Cell::new(12i32); 
    // let z2 = <Strong<_>>::new_slice(vec![Dummy(&q2)].into_iter());
    // drop(z2);
    // assert_eq!(q2.get(), 73);
}

