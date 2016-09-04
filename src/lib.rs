//! Wrappers around references, boxes or Arcs.
//!
//! Features: 
//! * Bx and Bxm: Boxes without DerefMove.
//! * RMBA: Wrap a &T, &mut T, Box<T> or Arc<T> within the size of a single pointer. 

use std::sync::Arc;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::{fmt, mem};

/// Slightly bigger and slower than RMBA, but same functionality.
/// Mostly used just to verify correctness of the real RMBA.
#[derive(Debug)]
pub enum SlowRMBA<'a, T: 'a + ?Sized> {
    Ref(&'a T),
    RefMut(&'a mut T),
    Box(Box<T>),
    Arc(Arc<T>),
}

impl<'a, T: 'a + ?Sized> SlowRMBA<'a, T> {
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


impl<'a, T: 'a + ?Sized> Deref for SlowRMBA<'a, T> {
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
/// It will panic if you try to store a struct that's not 32 bit aligned.
///
/// Note: Drop flags were removed in 1.13-nightly. If you run an earlier version,
/// size might be larger than a single pointer due to the drop flag.
pub struct RMBA<'a, T: 'a + ?Sized>(*const T, PhantomData<SlowRMBA<'a, T>>);


impl<'a, T: 'a> RMBA<'a, T> {
    pub fn new_box(t: T) -> RMBA<'a, T> { Box::new(t).into() }
}

impl<'a, T: 'a + ?Sized> RMBA<'a, T> {

    #[inline]
    fn unpack(&self) -> (*const T, usize) {
        let mut p = self.0;
        let f: *mut usize = (&mut p) as *mut _ as *mut usize;
        unsafe {
            let g = *f & 3;
            *f = *f & (!3); 
            (p, g)
        }
    }

    fn make(mut p: *const T, add: usize) -> RMBA<'a, T> {
        let f: *mut usize = (&mut p) as *mut _ as *mut usize;
        debug_assert!(add <= 3);
        unsafe {
            assert!(*f & 3 == 0);
            *f = *f + add;
        }; 
        RMBA(p, PhantomData)
    }

    // Turns an already unpacked *const T into an Arc<T>.
    // Relies on how Arc is done internally, and no checking done!
    // Must be forgotten after use!
    unsafe fn arc(mut p: *const T) -> Arc<T> {
        use std::sync::atomic::AtomicUsize;
        let f: *mut usize = (&mut p) as *mut _ as *mut usize;
        *f = *f - 2*mem::size_of::<AtomicUsize>();
        mem::transmute(p)
    }
    
    pub fn new<A: Into<RMBA<'a, T>>>(t: A) -> RMBA<'a, T> { t.into() }

    /// Will return a clone if it contains a Arc<T> or &T, or None if it is a Box<T> or &mut T 
    pub fn try_clone(&self) -> Option<RMBA<'a, T>> {
        match self.unpack() {
            (_, 0) => Some(RMBA(self.0, PhantomData)),
            (p, 2) => unsafe {
                let a = Self::arc(p);
                let r = Some(a.clone().into());
                mem::forget(a);
                r
            },
            _ => None,
        }
    }

    /// Will return a &mut to inner contents if it contains a &mut T, a Box<T> or if the Arc<T> is unique. Otherwise returns None.
    pub fn get_mut(&mut self) -> Option<&mut T> {
        match self.unpack() {
            (p, 1) => unsafe {
                let mut b = Box::<T>::from_raw(p as *mut T);
                let z: *mut T = &mut *b;
                mem::forget(b);
                Some(&mut *z)
            },
            (p, 2) => unsafe {
                let mut a = Self::arc(p);
                let r = mem::transmute(Arc::get_mut(&mut a));
                mem::forget(a);
                r
            },
            (p, 3) => unsafe { Some(&mut *(p as *mut T)) },
            _ => None,
        }
    }

}


impl<'a, T: 'a + ?Sized> From<&'a T> for RMBA<'a, T> {
    fn from(t: &'a T) -> RMBA<'a, T> { RMBA::make(t as *const T, 0) }
}

impl<'a, T: 'a + ?Sized> From<&'a mut T> for RMBA<'a, T> {
    fn from(t: &'a mut T) -> RMBA<'a, T> { RMBA::make(t as *const T, 3) }
}

impl<'a, T: 'a + ?Sized> From<Box<T>> for RMBA<'a, T> {
    fn from(t: Box<T>) -> RMBA<'a, T> { RMBA::make(Box::into_raw(t) as *const T, 1) }
}

impl<'a, T: 'a + ?Sized> From<Arc<T>> for RMBA<'a, T> {
    fn from(t: Arc<T>) -> RMBA<'a, T> {
        let z = RMBA::make(&*t, 2);
        // debug_assert_eq!(unsafe { Self::arc(z.unpack().0) }, &t as *const Arc<T>);
        mem::forget(t);
        z
    }
}

impl<'a, T: 'a + ?Sized> fmt::Debug for RMBA<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "RMBA({})", match self.unpack().1 { 0 => "&", 1 => "Box", 2 => "Arc", 3 => "&mut", _ => unreachable!() })
    }
}

impl<'a, T: 'a + ?Sized> Deref for RMBA<'a, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T { unsafe { &*self.unpack().0 }}
}

impl<'a, T: 'a + ?Sized> Drop for RMBA<'a, T> {
    fn drop(&mut self) {
        match self.unpack() {
            (_, 0) => {},
            (p, 1) => unsafe { let _ = Box::<T>::from_raw(p as *mut T); },
            (p, 2) => unsafe { let _ = Self::arc(p); },
            (_, 3) => {},
            _ => unreachable!(),
        }
    }
}

#[test]
fn rmba_fat() {
    trait Dummy { fn foo(&self) -> i32; } 
    impl Dummy for u8 { fn foo(&self) -> i32 { *self as i32 } }
    impl Dummy for i32 { fn foo(&self) -> i32 { *self } }

    let z: SlowRMBA<Dummy> = SlowRMBA::Box(Box::new(9u8));
    let r: RMBA<Dummy> = (Box::new(9i32) as Box<Dummy>).into();
    let a: RMBA<Dummy> = (Arc::new(17i32) as Arc<Dummy>).into();
    assert_eq!(r.foo(), z.foo());
    assert_eq!(a.try_clone().unwrap().foo(), 17i32);
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
    let _ = RMBA::new(&b[0]); // Either of these two will fail - u8 is not 32 bit aligned
    let _ = RMBA::new(&b[1]); 
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
     use std::mem::size_of;
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

