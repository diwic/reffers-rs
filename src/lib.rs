//! Wrappers around references, boxes or Arcs.
//!
//! Features: 
//!
//! * rc::Strong/Weak/Ref/RefMut: An `Rc<RefCell<T>>` in just a few bytes of storage, and poisoning support.
//!
//! * ARef: `OwningRef` with even further erasure of the owner.
//!
//! * RMBA: Wrap a `&T`, `&mut T`, `Box<T>` or `Arc<T>` within the size of a single pointer. 
//!
//! * Bx and Bxm: Boxes without DerefMove.

use std::ops::{Deref, DerefMut};

pub mod aref;
pub mod rmba;
pub mod rc;

pub use aref::ARef as ARef;
pub use aref::ARefs as ARefs;
pub use aref::ARefss as ARefss;
pub use rmba::RMBA as RMBA;


/// A simple wrapper around Box to avoid DerefMove.
///
/// There is no way to get to
/// &Box<T>, just &T. This way you can return a Bx<T> in your API and still be
/// sure the inner struct does not move in memory. (This might be helpful if you're
/// dealing with FFI or unsafe code.)
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Bx<T: ?Sized>(Box<T>);

impl<T> Bx<T> {
    pub fn new(t: T) -> Bx<T> { Bx(Box::new(t)) }
}

impl<T: ?Sized> From<Box<T>> for Bx<T> {
    fn from(t: Box<T>) -> Bx<T> { Bx(t) }
}

impl<T: ?Sized> Deref for Bx<T> {
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
pub struct Bxm<T: ?Sized>(Box<T>);

impl<T> Bxm<T> {
    pub fn new(t: T) -> Bxm<T> { Bxm(Box::new(t)) }
}

impl<T: ?Sized> From<Box<T>> for Bxm<T> {
    fn from(t: Box<T>) -> Bxm<T> { Bxm(t) }
}

impl<T: ?Sized> Deref for Bxm<T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T { &self.0 }
}

impl<T: ?Sized> DerefMut for Bxm<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T { &mut self.0 }
}

