// Internal macros.

// Cannot use $bm:tt here due to https://github.com/rust-lang/rust/issues/20272 :-(

macro_rules! new_ref {
    ($r: ident, $p: ident, $gr: ident, $($bm:tt)*) => {

impl<T, M: $($bm)*> $r<T, M> {
    /// Creates a new reference.
    #[inline]
    pub fn new(t: T) -> Self { $p::new(t).$gr().unwrap() }
}


impl<M: $($bm)*> $r<str, M> {
    /// Creates a new reference from a str.
    #[inline]
    pub fn new_str(t: &str) -> Self { $p::new_str(t).$gr().unwrap() }
}

impl<T, M: $($bm)*> $r<[T], M> {
    /// Creates a new slice reference from an iterator.
    #[inline]
    pub fn new_slice<I: ExactSizeIterator<Item=T>>(t: I) -> Self { $p::new_slice(t).$gr().unwrap() }
}

impl<T: Default, M: $($bm)*> Default for $r<T, M> {
    #[inline]
    fn default() -> Self { $r::new(Default::default()) }
}

impl<T, M: $($bm)*> From<T> for $r<T, M> {
    #[inline]
    fn from(t: T) -> Self { $r::new(t) }
}

    }
}

macro_rules! impl_get_refmut {
    () => {

    /// Returns a new RefMut, or panics if this is not possible
    ///
    /// Will panic in case a RefMut or Ref is currently held
    #[inline]
    #[deprecated(note="Renamed to get_refmut")]
    pub fn get_mut(&self) -> RefMut<T, M> { self.0.get_refmut().unwrap() }

    /// Returns a new RefMut, or panics if this is not possible
    ///
    /// Will return an error in case a RefMut or Ref is currently held
    #[inline]
    #[deprecated(note="Renamed to try_get_refmut")]
    pub fn try_get_mut(&self) -> Result<RefMut<T, M>, State> { self.0.get_refmut() }

    /// Returns a new RefMut, or panics if this is not possible
    ///
    /// Will panic in case a RefMut or Ref is currently held
    #[inline]
    pub fn get_refmut(&self) -> RefMut<T, M> { self.0.get_refmut().unwrap() }

    /// Returns a new RefMut, or panics if this is not possible
    ///
    /// Will return an error in case a RefMut or Ref is currently held
    #[inline]
    pub fn try_get_refmut(&self) -> Result<RefMut<T, M>, State> { self.0.get_refmut() }

    }
}

macro_rules! impl_get_ref {
    () => {

    /// Returns a new Ref, or panics if this is not possible
    ///
    /// Will panic in case a RefMut is currently held, or there are no more Refs available
    #[inline]
    pub fn get_ref(&self) -> Ref<T, M> { self.0.get_ref().unwrap() }

    /// Returns a new Ref, or returns an error if there are no such references available
    ///
    /// Will return an error in case a RefMut is currently held, or there are no more Refs available
    #[inline]
    pub fn try_get_ref(&self) -> Result<Ref<T, M>, State> { self.0.get_ref() }

    /// Returns a new Ref, or panics if this is not possible
    ///
    /// Will panic in case a RefMut is currently held, or there are no more Refs available
    #[inline]
    #[deprecated(note="Renamed to get_ref")]
    pub fn get(&self) -> Ref<T, M> { self.get_ref() }

    /// Returns a new Ref, or returns an error if there are no such references available
    ///
    /// Will return an error in case a RefMut is currently held, or there are no more Refs available
    #[inline]
    #[deprecated(note="Renamed to try_get_ref")]
    pub fn try_get(&self) -> Result<Ref<T, M>, State> { self.0.get_ref() }

    }
}

macro_rules! impl_ref_all {

    () => {

    /// Returns a new Weak reference, or panics if there are no such references available
    #[inline]
    pub fn get_weak(&self) -> Weak<T, M> { self.0.get_weak().unwrap() }

    /// Returns a new Strong reference, or panics if there are no such references available
    #[inline]
    pub fn get_strong(&self) -> Strong<T, M> { self.0.get_strong().unwrap() }

    /// Returns a new Weak reference, or returns an error if there are no such references available
    #[inline]
    pub fn try_get_weak(&self) -> Result<Weak<T, M>, State> { self.0.get_weak() }

    /// Returns a new Strong reference, or returns an error if there are no such references available
    #[inline]
    pub fn try_get_strong(&self) -> Result<Strong<T, M>, State> { self.0.get_strong() }

    /// Returns the current state
    #[inline]
    pub fn state(&self) -> State { self.0.state() }

    /// Reverts poisoning
    ///
    /// Poisoning happens when a RefMut is dropped during a panic.
    #[inline]
    pub fn unpoison(&self) -> Result<(), State> { self.0.unpoison() }

    }

}

macro_rules! impl_arc_all {
    ($t: ident, $drop_expr: expr) => {

unsafe impl<T: Send, M: Send + BitMask<Num=usize>> Send for $t<T, M> {}

impl<T: ?Sized + Repr, M: BitMask<Num=usize>> Drop for $t<T, M> {
    #[inline]
    fn drop(&mut self) {
        self.0.try_drop($drop_expr);
    }
}

    }
}

macro_rules! impl_deref_and_friends {
    ($r: ident, $($bm:tt)*) => {

impl<T: ?Sized + Repr, M: $($bm)*> ops::Deref for $r<T, M> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target { unsafe { &*self.0.value_ptr() }}
}

unsafe impl<T: ?Sized + Repr, M: $($bm)*> crate::StableDeref for $r<T, M> {}

impl<T: ?Sized + Repr + fmt::Display, M: $($bm)*> fmt::Display for $r<T, M> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Display::fmt(&**self, f) }
}

impl<T: ?Sized + Repr, M: $($bm)*> borrow::Borrow<T> for $r<T, M> {
    #[inline]
    fn borrow(&self) -> &T { &**self }
}

impl<T: ?Sized + Repr, M: $($bm)*> convert::AsRef<T> for $r<T, M> {
    #[inline]
    fn as_ref(&self) -> &T { &**self }
}

impl<T: ?Sized + Repr + hash::Hash, M: $($bm)*> hash::Hash for $r<T, M> {
    #[inline]
    fn hash<H>(&self, state: &mut H) where H: hash::Hasher { (**self).hash(state) }
}

impl<T: ?Sized + Repr + PartialEq, M: $($bm)*> PartialEq for $r<T, M> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { **self == **other }
    #[inline]
    fn ne(&self, other: &Self) -> bool { **self != **other }
}

impl<T: ?Sized + Repr + Eq, M: $($bm)*> Eq for $r<T, M> {}

impl<T: ?Sized + Repr + PartialOrd, M: $($bm)*> PartialOrd for $r<T, M> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { (**self).partial_cmp(&**other) }
    #[inline]
    fn lt(&self, other: &Self) -> bool { **self < **other }
    #[inline]
    fn le(&self, other: &Self) -> bool { **self <= **other }
    #[inline]
    fn gt(&self, other: &Self) -> bool { **self > **other }
    #[inline]
    fn ge(&self, other: &Self) -> bool { **self >= **other }
}

impl<T: ?Sized + Repr + Ord, M: $($bm)*> Ord for $r<T, M> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering { (**self).cmp(&**other) }
}


    }
}
