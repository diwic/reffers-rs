//! Wrappers around references, boxes or Arcs.

use std::sync::Arc;
use std::marker::PhantomData;
use std::mem::{transmute, forget, size_of, align_of};
use std::ops::{Deref, DerefMut};
use std::sync::atomic::AtomicUsize;
use std::fmt;

/// RBA can store an &T, a Box<T> or an Arc<T>, within just a pointer -
/// this will panic if you try to store something that's not 32 bit aligned.
pub struct RBA<'a, T: 'a>(usize, PhantomData<Option<&'a T>>,
    PhantomData<Option<Box<T>>>, PhantomData<Option<Arc<T>>>);

impl<'a, T: 'a> RBA<'a, T> {
    fn make(p: *const T, add: usize) -> RBA<'a, T> {
        let z: usize = unsafe { transmute(p) };
        assert!(align_of::<T>() >= 4);
        debug_assert!(z & 3 == 0);
        RBA(z+add, PhantomData, PhantomData, PhantomData)
    }
    
    pub fn new<A: Into<RBA<'a, T>>>(t: A) -> RBA<'a, T> { t.into() }

    pub fn new_box(t: T) -> RBA<'static, T> { Box::new(t).into() }
}


impl<'a, T: 'a> From<&'a T> for RBA<'a, T> {
    fn from(t: &'a T) -> RBA<'a, T> { RBA::make(t as *const T, 0) }
}

impl<'a, T: 'a> From<Box<T>> for RBA<'a, T> {
    fn from(t: Box<T>) -> RBA<'a, T> { RBA::make(Box::into_raw(t) as *const T, 1) }
}

impl<'a, T: 'a> From<Arc<T>> for RBA<'a, T> {
    fn from(t: Arc<T>) -> RBA<'a, T> {
        let z = RBA::make(&*t, 2);
        forget(t);
        z
    }
}

impl<'a, T: 'a> fmt::Debug for RBA<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "RBA({})", match self.0 & 3 { 0 => "&", 1 => "Box", 2 => "Arc", _ => unreachable!() })
    }
}


impl<'a, T: 'a> Deref for RBA<'a, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T { unsafe { transmute(self.0 & (!3)) }}
}

impl<'a, T: 'a> Drop for RBA<'a, T> {
    fn drop(&mut self) {
        match self.0 & 3 {
            0 => {},
            1 => unsafe { Box::<T>::from_raw(transmute(self.0-1)); },
            2 => unsafe { let _: Arc<T> = transmute(self.0 - 2 - 2*size_of::<AtomicUsize>()); },
            _ => unreachable!(),
        }
    }
}

#[test]
fn rba_arc() {
    let mut a = Arc::new(53);
    let f = RBA::new(a.clone());
    {
        let f2: &i32 = &f;
        assert_eq!(53, *f2);
    }
    assert!(Arc::get_mut(&mut a).is_none());
    drop(f);
    assert!(Arc::get_mut(&mut a).is_some());
}

#[test]
#[should_panic]
fn rba_unaligned() {
    let b = vec![5u8, 7u8];
    let _ = RBA::new(&b[0]); // Fails - u8 is not 32 bit aligned
}

#[test]
fn rba_typical() {
    struct Dummy {
        a: Arc<i32>,
        b: RBA<'static, i32>,
    }
    let z = Arc::new(5i32);
    let d = Dummy { a: z.clone(), b: RBA::new(z) };
    assert_eq!(&*d.b, &5i32);
    assert_eq!(&*d.a, &5i32);
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

impl<T> DerefMut for Bx<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T { &mut self.0 }
}
