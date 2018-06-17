// Internal macros.


// Cannot use $bm:tt here due to https://github.com/rust-lang/rust/issues/20272 :-(

macro_rules! new_ref {
    ($r: ident, $p: ident, $gr: ident, $($bm:tt)*) => {

impl<T, M: $($bm)*> $r<T, M> {
    #[inline]
    pub fn new(t: T) -> Self { $p::new(t).$gr().unwrap() }
}


impl<M: $($bm)*> $r<str, M> {
    #[inline]
    pub fn new_str(t: &str) -> Self { $p::new_str(t).$gr().unwrap() }
}

impl<T, M: $($bm)*> $r<[T], M> {
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

    #[inline]
    #[deprecated(note="Renamed to get_refmut")]
    pub fn get_mut(&self) -> RefMut<T, M> { self.0.get_refmut().unwrap() }

    #[inline]
    #[deprecated(note="Renamed to try_get_refmut")]
    pub fn try_get_mut(&self) -> Result<RefMut<T, M>, State> { self.0.get_refmut() }

    #[inline]
    pub fn get_refmut(&self) -> RefMut<T, M> { self.0.get_refmut().unwrap() }

    #[inline]
    pub fn try_get_refmut(&self) -> Result<RefMut<T, M>, State> { self.0.get_refmut() }

    }
}

macro_rules! impl_get_ref {
    () => {

    #[inline]
    pub fn get_ref(&self) -> Ref<T, M> { self.0.get_ref().unwrap() }

    #[inline]
    pub fn try_get_ref(&self) -> Result<Ref<T, M>, State> { self.0.get_ref() }

    #[inline]
    #[deprecated(note="Renamed to get_ref")]
    pub fn get(&self) -> Ref<T, M> { self.get_ref() }

    #[inline]
    #[deprecated(note="Renamed to try_get_ref")]
    pub fn try_get(&self) -> Result<Ref<T, M>, State> { self.0.get_ref() }

    }
}

macro_rules! impl_ref_all {

    () => {

    #[inline]
    pub fn get_weak(&self) -> Weak<T, M> { self.0.get_weak().unwrap() }

    #[inline]
    pub fn get_strong(&self) -> Strong<T, M> { self.0.get_strong().unwrap() }

    #[inline]
    pub fn try_get_weak(&self) -> Result<Weak<T, M>, State> { self.0.get_weak() }

    #[inline]
    pub fn try_get_strong(&self) -> Result<Strong<T, M>, State> { self.0.get_strong() }

    #[inline]
    pub fn state(&self) -> State { self.0.state() }

    #[inline]
    pub fn unpoison(&self) -> Result<(), State> { self.0.get().unpoison() }

    }

}
