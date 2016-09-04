/*
 Note: This never worked correctly. Instead see https://github.com/diwic/refstruct-rs for a
more robust alternative. 
*/


use std::marker::PhantomData;
use std::{mem, ops, ptr};

/// This StructInfo can be implemented using the impl_bbx macro.
///
/// Known problem: For struct with internal mutability + Drop destructors,
/// might be unsafe if the lifetimes are swapped. Hence the trait being unsafe.
pub unsafe trait StructInfo: Sized {
    /// Number of fields in struct.
    fn count() -> usize;

    /// Glue code for calling drop_one with the right generic type
    fn drop_nr(f: &mut BBx<Self>, nr: usize);
}

/// FullBox, FinishedBox, FixedBox or something like that. It's what you use
/// when the struct has been built. It derefs into your struct.
///
/// Known caveat: Even if T implements Drop, the destructor will never run.
/// The individual fields' destructors will run, in reverse to append order. 
pub struct FBx<T: StructInfo>(Box<[u8]>, PhantomData<T>);

impl<T: StructInfo> ops::Deref for FBx<T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        let z: *const u8 = &self.0[0];
        unsafe { mem::transmute(z) } 
    }
}

impl<T: StructInfo> Drop for FBx<T> {
    fn drop(&mut self) {
        let r = mem::replace(&mut self.0, Box::new([]));
        let _ = BBx::<T> { size: r.len(), data: r, count: T::count(), p: PhantomData };
    }
}

/// Building Box: used while T is constructing. Call the "build" method to get a FBx<T>,
/// which Deref's to a T.
///
/// Known limitation: Won't work if the struct contains padding.
pub struct BBx<T: StructInfo> {
    data: Box<[u8]>, 
    count: usize, 
    size: usize,
    p: PhantomData<T>,
}

impl<T: StructInfo> BBx<T> {
    pub fn new() -> BBx<T> {
        let v = vec!(0; mem::size_of::<T>());
        BBx { data: v.into_boxed_slice(), count: 0, size: 0, p: PhantomData }
    }

    pub fn get_count(&self) -> usize { self.count }

    pub fn build(mut self) -> FBx<T> {
        assert_eq!(T::count(), self.count);
        assert_eq!(self.data.len(), self.size);
        let d = mem::replace(&mut self.data, Box::new([]));
        self.size = 0;
        self.count = 0;
        FBx(d, PhantomData)
    }

    pub unsafe fn drop_one<S>(&mut self) {
        assert!(self.count > 0);
        let newcount = self.count - 1;
        let i = mem::size_of::<S>();
        let newsize = self.size - i;
        let p: *const u8 = &self.data[newsize];
        self.size = newsize;
        self.count = newcount;
        let _d = ptr::read(p as *const S);
    }

    pub unsafe fn append<S, F: FnOnce() -> S>(&mut self, f: F) {
        assert!(self.count < T::count());
        let i = mem::size_of::<S>();
        assert!(i + self.size <= self.data.len());
        let p: *mut u8 = &mut self.data[self.size];
        ptr::write(p as *mut S, f());
        self.count += 1;
        self.size += i; 
    }

    /// Gives access to first field in a closure returning a new field.
    pub unsafe fn append_with0<F0, S: ?Sized, F: FnOnce(&F0) -> &S>(&mut self, f: F) {
        assert!(self.count >= 1);
        let p0: *const u8 = &self.data[0];
        self.append(|| {
            f(&* (p0 as *const F0))
        })
    }

    /// Gives access to first and second fields in a closure returning a new field.
    pub unsafe fn append_with1<F0, F1, S: ?Sized, F: for<'z> FnOnce(&'z F0, &'z F1) -> &'z S>(&mut self, f: F) {
        assert!(self.count >= 2);
        let p0: *const u8 = &self.data[0];
        let p1 = p0.offset(mem::size_of::<F0>() as isize);
        self.append(|| {
            f(&*(p0 as *const F0), &*(p1 as *const F1))
        })
    }

    /// Removes already appended fields, downto the field of index i.
    pub fn truncate(&mut self, i: usize) {
        while self.count > i {
            let newcount = self.count-1;
            T::drop_nr(self, newcount);
            assert_eq!(newcount, self.count);
        }
    }
}

impl<T: StructInfo> Drop for BBx<T> {
    fn drop(&mut self) { self.truncate(0) }
}


#[macro_export]
/// Internal use only. Use the impl_bbx macro instead
macro_rules! bbx_helper_main {
    ($t: ident, $twrap: ident, $c: expr, $f: ident, $nr: ident, $drops: expr) => {

unsafe impl<'a> $crate::StructInfo for $t<'a> {
    fn count() -> usize { $c }
    fn drop_nr($f: &mut $crate::BBx<Self>, $nr: usize) {
        unsafe { $drops }
    }
}

struct $twrap<'a>($crate::BBx<$t<'a>>);

impl<'a> $twrap<'a> {
    pub fn new() -> Self { $twrap($crate::BBx::new()) }
    pub fn build(self) -> $crate::FBx<$t<'a>> { self.0.build() }
}

    }
}

#[macro_export]
/// Internal use only. Use the impl_bbx macro instead
macro_rules! bbx_helper_append {

    ($i: ident, $tr: ty, $c: expr, $aw: ident, $( $ta: ty,)* ) => {

    pub fn $i<F: for <'q> FnOnce($(&'q $ta,)*) -> &'q $tr>(&mut self, f: F) {
        assert_eq!(self.0.get_count(), $c);
        unsafe { (self.0).$aw(f); }
    }

    }
}

#[macro_export]
/// Implements StructInfo for a particular struct.
///
/// Parameters are: 1) Type to implement StructInfo for, 2) Name of wrapper type around BBx,
/// 3) List of fields (in declaration order) in the form `field_name => type`.
///
/// Known limitation: Type to implement StructInfo must have exactly one lifetime parameter.
macro_rules! impl_bbx {

    ($t: ident, $twrap: ident, $i0: ident => $t0: ty, $i1: ident => $t1: ty) => {

        bbx_helper_main!($t, $twrap, 2, f, nr, match nr {
            0 => f.drop_one::<$t0>(),
            1 => f.drop_one::<$t1>(),
            _ => unreachable!(),
        });

        impl<'a> $twrap<'a> {
            bbx_helper_append!($i0, $t0, 0, append,);
            bbx_helper_append!($i1, $t1, 1, append_with0, $t0,);
        }
    };

    ($t: ident, $twrap: ident, $i0: ident => $t0: ty, $i1: ident => $t1: ty, $i2: ident => $t2: ty) => {

        bbx_helper_main!($t, $twrap, 3, f, nr, match nr {
            0 => f.drop_one::<$t0>(),
            1 => f.drop_one::<$t1>(),
            2 => f.drop_one::<$t2>(),
            _ => unreachable!(),
        });

        impl<'a> $twrap<'a> {
            bbx_helper_append!($i0, $t0, 0, append,);
            bbx_helper_append!($i1, $t1, 1, append_with0, $t0,);
            bbx_helper_append!($i2, $t2, 2, append_with1, $t0, $t1,);
        }
    }


}

/*

unsafe impl<'a> $crate::StructInfo for $t<'a> {
    fn count() -> usize { 2 }
    fn drop_nr(f: &mut $crate::BBx<Self>, nr: usize) {
        unsafe { match nr {
            0 => f.drop_one::<$t0>(),
            1 => f.drop_one::<$t1>(),
            _ => unreachable!(),
        }}
    }
}

struct $twrap<'a>($crate::BBx<$t<'a>>);

impl<'a> $twrap<'a> {
    pub fn new() -> Self { $twrap($crate::BBx::new()) }
    pub fn build(self) -> $crate::FBx<$t<'a>> { self.0.build() }
    pub fn $i0<F: FnOnce() -> $t0>(&mut self, f: F) {
        assert_eq!(self.0.get_count(), 0);
        unsafe { self.0.append(f); }
    }
    pub fn $i1<F: FnOnce(&$t0) -> $t1>(&mut self, f: F) {
        assert_eq!(self.0.get_count(), 1);
        unsafe { self.0.append_with0(f); }
    }

*/


#[cfg(test)]
mod tests {
    struct Simple<'a> { a: String, b: &'a str }
    impl_bbx!(Simple, BSimple, a => String, b => &str);

    struct Simple2<'a> { a: String, b: &'a str, c: &'a str }
    impl_bbx!(Simple2, BSimple2, a => String, b => &str, c => &str);


/*
    struct BSimple<'a>(BBx<Simple<'a>>);

    unsafe impl<'a> StructInfo for Simple<'a> {
        fn count() -> usize { 2 }
        fn drop_nr(f: &mut BBx<Self>, nr: usize) {
            unsafe { match nr {
                0 => f.drop_one::<String>(),
                1 => f.drop_one::<&str>(),
                _ => unreachable!(),
            }}
        }
    }

    impl<'a> BSimple<'a> {
        fn a(a: String) -> Self { let mut z = BSimple(BBx::new()); unsafe { z.0.append(|| a); } z }
        fn b<F: FnOnce(&String) -> &str>(&mut self, f: F) { unsafe { self.0.append_with0::<String, str, _>(|a| f(a)); }}
        fn build(self) -> FBx<Simple<'a>> { self.0.build() }
    }
*/
    #[test]
    fn test_bbx() {
        let mut z = BSimple::new();
        z.a(|| "Hello world".into());
        z.b(|a| &a[6..]);
        let f = z.build();
        assert_eq!(&f.a, "Hello world");
        assert_eq!(f.b, "world");
    }

} 
