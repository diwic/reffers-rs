//! Wrappers around references, boxes or Arcs.
//!
//! Features: 
//! * Bx and Bxm: Boxes without DerefMove.
//! * RMBA: Wrap a &T, &mut T, Box<T> or Arc<T> within the size of a single pointer. 

use std::sync::Arc;
use std::marker::PhantomData;
use std::mem::{transmute, forget, size_of, align_of};
use std::ops::{Deref, DerefMut};
use std::sync::atomic::AtomicUsize;
use std::fmt;

/// Slightly bigger and slower than RMBA, but same functionality.
/// Mostly used just to verify correctness of the real RMBA.
#[derive(Debug)]
pub enum SlowRMBA<'a, T: 'a> {
    Ref(&'a T),
    RefMut(&'a mut T),
    Box(Box<T>),
    Arc(Arc<T>),
}

impl<'a, T: 'a> SlowRMBA<'a, T> {
    /// Will return a clone if it contains a Arc<T> or &T, or None if it is a Box<T> or &mut T 
    pub fn try_clone(&self) -> Option<SlowRMBA<'a, T>> {
        match self {
            &SlowRMBA::Ref(ref t) => Some(SlowRMBA::Ref(t)),
            &SlowRMBA::Arc(ref t) => Some(SlowRMBA::Arc(t.clone())),
            _ => None,
        }
    }

    /// Will return a &mut to inner contents if it contains a &mut T, a Box<T> or if the Arc<T> is unique. Otherwise returns None.
    pub fn get_mut(&mut self) -> Option<&mut T> {
        match self {
            &mut SlowRMBA::RefMut(ref mut t) => Some(t),
            &mut SlowRMBA::Box(ref mut t) => Some(t),
            &mut SlowRMBA::Arc(ref mut t) => Arc::get_mut(t),
            _ => None,
        }
    }
}


impl<'a, T: 'a> Deref for SlowRMBA<'a, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        match self {
            &SlowRMBA::Ref(ref t) => t,
            &SlowRMBA::RefMut(ref t) => t,
            &SlowRMBA::Box(ref t) => t,
            &SlowRMBA::Arc(ref t) => t,
        }
    }
}


/// RMBA can store an &T, a &mut T, a Box<T> or an Arc<T>.
/// It will panic if you try to store something that's not 32 bit aligned.
///
/// Note: Drop flags were removed in 1.13-nightly. If you run an earlier version,
/// size might be larger than a single pointer due to the drop flag.
pub struct RMBA<'a, T: 'a>(usize, PhantomData<SlowRMBA<'a, T>>);

impl<'a, T: 'a> RMBA<'a, T> {
    fn make(p: *const T, add: usize) -> RMBA<'a, T> {
        let z: usize = unsafe { transmute(p) };
        assert!(align_of::<T>() >= 4);
        debug_assert!(z & 3 == 0);
        RMBA(z+add, PhantomData)
    }
    
    pub fn new<A: Into<RMBA<'a, T>>>(t: A) -> RMBA<'a, T> { t.into() }

    pub fn new_box(t: T) -> RMBA<'a, T> { Box::new(t).into() }

    /// Will return a clone if it contains a Arc<T> or &T, or None if it is a Box<T> or &mut T 
    pub fn try_clone(&self) -> Option<RMBA<'a, T>> {
        match self.0 & 3 {
            0 => Some(RMBA(self.0, PhantomData)),
            2 => unsafe {
                let t: Arc<T> = transmute(self.0 - 2 - 2*size_of::<AtomicUsize>());
                let t2 = t.clone();
                forget(t);
                Some(t2.into())
            },
            _ => None,
        }
    }

    /// Will return a &mut to inner contents if it contains a &mut T, a Box<T> or if the Arc<T> is unique. Otherwise returns None.
    pub fn get_mut(&mut self) -> Option<&mut T> {
        match self.0 & 3 {
            1 => unsafe {
                let mut b = Box::<T>::from_raw(transmute(self.0-1));
                let z: *mut T = &mut *b;
                forget(b);
                Some(&mut *z)
            },
            2 => unsafe {
                let mut t: Arc<T> = transmute(self.0 - 2 - 2*size_of::<AtomicUsize>());
                let z: Option<*mut T> = Arc::get_mut(&mut t).map(|z| -> *mut T { &mut *z });
                forget(t);
                z.map(|z| &mut *z)
            },
            3 => unsafe { Some(transmute(self.0 - 3)) },
            _ => None,
        }
    }
}


impl<'a, T: 'a> From<&'a T> for RMBA<'a, T> {
    fn from(t: &'a T) -> RMBA<'a, T> { RMBA::make(t as *const T, 0) }
}

impl<'a, T: 'a> From<&'a mut T> for RMBA<'a, T> {
    fn from(t: &'a mut T) -> RMBA<'a, T> { RMBA::make(t as *const T, 3) }
}

impl<'a, T: 'a> From<Box<T>> for RMBA<'a, T> {
    fn from(t: Box<T>) -> RMBA<'a, T> { RMBA::make(Box::into_raw(t) as *const T, 1) }
}

impl<'a, T: 'a> From<Arc<T>> for RMBA<'a, T> {
    fn from(t: Arc<T>) -> RMBA<'a, T> {
        let z = RMBA::make(&*t, 2);
        forget(t);
        z
    }
}

impl<'a, T: 'a> fmt::Debug for RMBA<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "RMBA({})", match self.0 & 3 { 0 => "&", 1 => "Box", 2 => "Arc", 3 => "&mut", _ => unreachable!() })
    }
}

impl<'a, T: 'a> Deref for RMBA<'a, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T { unsafe { transmute(self.0 & (!3)) }}
}

impl<'a, T: 'a> Drop for RMBA<'a, T> {
    fn drop(&mut self) {
        match self.0 & 3 {
            0|3 => {},
            1 => unsafe { Box::<T>::from_raw(transmute(self.0-1)); },
            2 => unsafe { let _: Arc<T> = transmute(self.0 - 2 - 2*size_of::<AtomicUsize>()); },
            _ => unreachable!(),
        }
    }
}

#[test]
fn rmba_box() {
    let mut z = RMBA::new_box(78);
    assert!(z.try_clone().is_none());
    assert_eq!(*z, 78);
    *z.get_mut().unwrap() = 73;
    assert_eq!(*z, 73);
}

#[test]
fn rmba_arc() {
    let mut a = Arc::new(53);
    let mut f = RMBA::new(a.clone());
    {
        let f2: &i32 = &f;
        assert_eq!(53, *f2);
    }
    assert!(f.get_mut().is_none());
    assert!(Arc::get_mut(&mut a).is_none());
    let z = f.try_clone().unwrap();
    drop(f);
    assert!(Arc::get_mut(&mut a).is_none());
    drop(z);
    assert!(Arc::get_mut(&mut a).is_some());
}

#[test]
#[should_panic]
fn rmba_unaligned() {
    let b = vec![5u8, 7u8];
    let _ = RMBA::new(&b[0]); // Fails - u8 is not 32 bit aligned
}

#[test]
fn rmba_typical() {
    struct Dummy {
        a: Arc<i32>,
        b: RMBA<'static, i32>,
    }
    let z = Arc::new(5i32);
    let d = Dummy { a: z.clone(), b: RMBA::new(z) };
    assert_eq!(&*d.b, &5i32);
    assert_eq!(&*d.a, &5i32);
}

#[test]
fn rmba_sizes() {
    assert_eq!(size_of::<&i32>(), size_of::<RMBA<i32>>());
    assert!(size_of::<RMBA<i32>>() < size_of::<SlowRMBA<i32>>());
}

/// A simple wrapper around Box to avoid DerefMove. There is no way to get to
/// &Box<T>, just &T. This way you can return a Bx<T> in your API and still be
/// sure the inner struct does not move in memory.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Bx<T>(Box<T>);

impl<T> Bx<T> {
    pub fn new(t: T) -> Bx<T> { Bx(Box::new(t)) }
}

impl<T> From<Box<T>> for Bx<T> {
    fn from(t: Box<T>) -> Bx<T> { Bx(t) }
}

impl<T> Deref for Bx<T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T { &self.0 }
}

/// A simple wrapper around Box to avoid DerefMove. Like Bx,
/// but also allows mutable access to the interior of the box.
///
/// Note that this will allow callers to use e g `mem::swap` and
/// `mem::replace` to move the box's contents to other memory
/// locations.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Bxm<T>(Box<T>);

impl<T> Bxm<T> {
    pub fn new(t: T) -> Bxm<T> { Bxm(Box::new(t)) }
}

impl<T> From<Box<T>> for Bxm<T> {
    fn from(t: Box<T>) -> Bxm<T> { Bxm(t) }
}

impl<T> Deref for Bxm<T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T { &self.0 }
}

impl<T> DerefMut for Bxm<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T { &mut self.0 }
}


