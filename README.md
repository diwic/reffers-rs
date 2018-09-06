Assorted smart pointers for Rust. 

[![API Docs](https://docs.rs/reffers/badge.svg)](https://docs.rs/reffers)

[![Crates.io](https://img.shields.io/crates/v/reffers.svg)](https://crates.io/crates/reffers)

Features:

Strong / Weak / Ref / RefMut
----------------------------

This is like `Rc<RefCell<T>>`, but with slightly different trade-offs:

* Configurable overhead (compared to a fixed 24 or 12 for `Rc<RefCell<T>>`)

* The default of 4 bytes overhead gives you max 1024 immutable references, 1024 strong references
  and 1024 weak references, but this can easily be tweaked with just a few lines of code.

* Poisoning support - after a panic with an active mutable reference,
  trying to get mutable or immutable references will return an error.
  This can be reverted by calling unpoison().

There is also a thread-safe version which is something like an `Arc<RwSpinlock<T>>`.


ARef
----

ARef takes over where [OwningRef](https://crates.io/crates/owning_ref) ends, by abstracting the owner even further.

This makes it possible to return, say, an `ARef<str>` and have the caller drop the owner
when done looking at it, without having to bother about whether the owner is a `String`, `Rc<String>`, a
`Ref<String>`, a simple `&'static str` or something else.

It's also repr(C), so it can be transferred over an FFI boundary (if its target is repr(C), too).
 
RMBA
----

The RMBA wraps either a `&T`, `&mut T`, `Box<T>` or `Arc<T>` within the size of a single pointer. 

There are two gotchas here: 

  * It will panic if you try to store a struct that's not 32 bit aligned.

  * Drop flags were removed in 1.13-nightly. If you run an earlier version,
    size might be larger than a single pointer due to the drop flag.

Bx, Bxm
-------

These are just simple wrappers around `Box` that lets you get rid of DerefMove.

This way you can return a Bx<T> in your API and still be sure the inner struct
does not move in memory. (This might be helpful if you're dealing with FFI or unsafe code.)


License
-------

Apache 2.0 or MIT, at your preference.
