
use super::{RMBA, Bx, Bxm};
use super::rcc::RccRef;
use std::{ptr, mem, fmt};
use std::ops::Deref;
use std::rc::Rc;
use std::sync::{Arc, MutexGuard, RwLockReadGuard, RwLockWriteGuard};
use std::cell::{Ref, RefMut};
use std::marker::PhantomData;

type ARefStorage = [usize; 3]; 

// An unsafe trait that makes sure the type can be used as owner for ARef.
//
// If you implement this for your own types, make sure that
// 1) it has a Stable address, i e, the reference stays the same even if the object moves and
// 2) it is no bigger than 3 usizes.
pub unsafe trait AReffic: Deref {}

// Runtime verification that a type is in fact AReffic.
//
// Use this as a test case in case you implement AReffic for your own type.
pub fn verify_areffic<T: AReffic>(t: T) -> Result<T, & 'static str> {

    // Verify size
    if mem::size_of::<T>() > mem::size_of::<ARefStorage>() {
        return Err("Too large");
    }

    // Verify movability
    let mut q = [None, None];
    q[0] = Some(t);
    let ptr1: *const T::Target = &**q[0].as_ref().unwrap();
    q[1] = q[0].take();
    let ptr2: *const T::Target = &**q[1].as_ref().unwrap();
    if ptr2 != ptr1 {
        return Err("Not movable");
    }
    Ok(q[1].take().unwrap())
}

unsafe impl<T: ?Sized> AReffic for Box<T> {}
unsafe impl<T: ?Sized> AReffic for Rc<T> {}
unsafe impl<T: ?Sized> AReffic for Arc<T> {}
unsafe impl<'a, T: ?Sized> AReffic for RMBA<'a, T> {}
unsafe impl<'a, T> AReffic for RccRef<'a, T> {}
unsafe impl<T: ?Sized> AReffic for Bx<T> {}
unsafe impl<T: ?Sized> AReffic for Bxm<T> {}
unsafe impl<T> AReffic for Vec<T> {}
unsafe impl AReffic for String {}
unsafe impl<'a, T: ?Sized> AReffic for &'a T {}
unsafe impl<'a, T: ?Sized> AReffic for &'a mut T {}
unsafe impl<'a, T: ?Sized> AReffic for Ref<'a, T> {}
unsafe impl<'a, T: ?Sized> AReffic for RefMut<'a, T> {}
unsafe impl<'a, T: ?Sized> AReffic for RwLockReadGuard<'a, T> {}
unsafe impl<'a, T: ?Sized> AReffic for RwLockWriteGuard<'a, T> {}
unsafe impl<'a, T: ?Sized> AReffic for MutexGuard<'a, T> {}


/// ARef - a reference that abstracts the owner completely.
///
/// ARef takes over where [OwningRef](https://crates.io/crates/owning_ref) ends, by abstracting the owner even further.
///
/// This makes it possible to return, say, an `ARef<str>` and have the caller drop the owner
/// when done looking at it, without having to bother about whether the owner is a `String`, `Rc<String>`, a
/// `Ref<String>`, or something else.
///
/// Oh, and it's repr(C), so it can be transferred over an FFI boundary
/// (if its target is repr(C), too).
///
/// # Example
/// ```
/// use std::rc::Rc;
/// use reffers::ARef;
/// 
/// struct CountDown(pub Rc<String>);
/// impl CountDown {
///     pub fn idx_to_str(&self, idx: u32) -> ARef<str> {
///         match idx {
///             0 => "Go!".into(),
///             // We clone the Rc instead of the String
///             // for performance,
///             // then we map from &String to &str
///             1 => ARef::new(self.0.clone()).map(|s| &**s),
///             _ => format!("{}...", idx).into(),
///         }
///     }
/// }
/// 
/// let c = CountDown(Rc::new("Ready!".into()));
/// assert_eq!(&*c.idx_to_str(3), "3...");
/// assert_eq!(&*c.idx_to_str(2), "2...");
/// assert_eq!(&*c.idx_to_str(1), "Ready!");
/// assert_eq!(&*c.idx_to_str(0), "Go!");
/// ```

#[repr(C)]
pub struct ARef<'a, U: ?Sized> {
    target: *const U,
    dropfn: unsafe fn (*mut ARefStorage),
    owner: ARefStorage,
    // Just to be 100% to disable Send and Sync
    _dummy: PhantomData<(Rc<()>, &'a ())>
}

// We can't call drop_in_place directly, see https://github.com/rust-lang/rust/issues/34123
unsafe fn aref_drop_wrapper<T>(t: *mut ARefStorage) {
    ptr::drop_in_place::<T>(t as *mut _ as *mut T);
}

impl<'a, U: fmt::Debug + ?Sized> fmt::Debug for ARef<'a, U> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("ARef").field(&(&self as &U)).finish()
    }
}

impl<'a, U: ?Sized> Drop for ARef<'a, U> {
    fn drop(&mut self) {
        unsafe {
            (self.dropfn)(&mut self.owner);
        }
    }
}

impl<'a, U: ?Sized> Deref for ARef<'a, U> {
    type Target = U;

    #[inline]
    fn deref(&self) -> &U {
        unsafe { &*self.target }
    }
}

impl<'a, U: ?Sized> AsRef<U> for ARef<'a, U> {
    fn as_ref(&self) -> &U {
        &*self
    }
}

impl<'a, U: ?Sized> ARef<'a, U> {
    /// Creates a new ARef from what the ARef points to.
    ///
    /// # Example
    /// ```
    /// use std::rc::Rc;
    /// use reffers::ARef;
    ///
    /// let aref = ARef::new(Rc::new(43));
    /// assert_eq!(*aref, 43);
    /// ```
    pub fn new<O>(owner: O) -> Self
        where O: 'a + AReffic + Deref<Target = U>
    {
        owner.into()
    }

    /// Maps the ARef's target to something reachable from the target.
    ///
    /// # Example
    /// ```
    /// use std::rc::Rc;
    /// use reffers::ARef;
    ///
    /// let aref: ARef<[u8]> = vec![0u8, 5, 7].into();
    /// assert_eq!(*aref.map(|s| &s[1]), 5);
    /// ```
    pub fn map<V: ?Sized, F: FnOnce(&U) -> &V>(self, f: F) -> ARef<'a, V>
    {
        let t: *const V = f(&self);
        let o = self.owner;
        let d = self.dropfn;
        mem::forget(self);
        ARef {
            target: t,
            owner: o,
            dropfn: d,
            _dummy: PhantomData,
        }
    }
}

impl<'a, O: 'a + AReffic + Deref<Target = U>, U: ?Sized> From<O> for ARef<'a, U>
{
    fn from(owner: O) -> Self {
        let mut o2 = owner;
        debug_assert!({ o2 = verify_areffic::<O>(o2).unwrap(); true });
        let target: *const U = &*o2;
        unsafe {
            let mut storage: ARefStorage = mem::uninitialized();
            ptr::copy(&o2, &mut storage as *mut _ as *mut O, 1);
            mem::forget(o2);
            ARef {
                target: target,
                dropfn: aref_drop_wrapper::<O>,
                owner: storage,
                _dummy: PhantomData,
            }
        }
    }
}

#[test]
fn debug_impl() {
    let f = 5u8;
    let z: ARef<u8> = (&f).into();
    assert_eq!(&*format!("{:?}", z), "ARef(5)");
}

#[test]
fn verify_drop() {
    let mut z = Rc::new(79);
    let q: ARef<i32> = z.clone().into();
    assert!(Rc::get_mut(&mut z).is_none());
    assert_eq!(*q, 79);
    drop(q);
    assert!(Rc::get_mut(&mut z).is_some());
}

#[test]
fn verify_types() {
    use super::Rcc;
    use std::cell::RefCell;
    use std::sync::{Mutex, RwLock};
    verify_areffic(Box::new(5u8)).unwrap();
    verify_areffic(Rc::new(5u8)).unwrap();
    verify_areffic(Arc::new(5u8)).unwrap();
    verify_areffic(Bx::new(5u8)).unwrap();
    verify_areffic(Bxm::new(5u8)).unwrap();
    verify_areffic(RMBA::from(Arc::new(5u8))).unwrap();
    verify_areffic(String::from("Hello aref")).unwrap();
    verify_areffic(vec![4711]).unwrap();
    verify_areffic("This is areffic").unwrap();
    let r = RefCell::new(5u8);
    verify_areffic(r.borrow_mut()).unwrap();
    verify_areffic(r.borrow()).unwrap();
    let r = RwLock::new(5u8);
    assert_eq!(*verify_areffic(r.write().unwrap()).unwrap(), 5u8);
    assert_eq!(*verify_areffic(r.read().unwrap()).unwrap(), 5u8);
    let m = Mutex::new(5u8);
    assert_eq!(*verify_areffic(m.lock().unwrap()).unwrap(), 5u8);
    let r = Rcc::new(5u8);
    verify_areffic(r.get()).unwrap();
}

/*
fn compile_fail<'a>() -> ARef<'a, str> {
    let z = String::from("Hello world");
    let z2: &str = &z; 
    z2.into()
}

fn compile_fail2<'a>() -> ARef<'a, [&'a u8]> {
    let z = vec![5u8, 4, 3];
    let z2 = vec![&z[0], &z[2]]; 
    z2.into()
}
*/

#[test]
fn countdown_example() {
    struct CountDown(pub Rc<String>);
    impl CountDown {
        pub fn idx_to_str(&self, idx: u32) -> ARef<str> {
            match idx {
                0 => "Go!".into(),
                1 => ARef::new(self.0.clone()).map(|s| &**s),
                _ => format!("{}...", idx).into(),
            }
        }
    }

    let c = CountDown(Rc::new(String::from("Ready!")));
    assert_eq!(&*c.idx_to_str(0), "Go!");
    assert_eq!(&*c.idx_to_str(1), "Ready!");
    assert_eq!(&*c.idx_to_str(2), "2...");
}

