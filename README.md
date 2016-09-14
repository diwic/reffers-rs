Assorted smart pointers for Rust. 



Features:

== Rcc == 

This is like `Rc<RefCell<T>>`, but with slightly different trade-offs:

 * 4 bytes overhead (compared to 12 or 24 for `Rc<RefCell<T>>`)

 * One mutable reference, no multiple immutable references. 
   I e, if RefCell is a single-threaded RwLock, then this is a single-threaded Mutex.

 * Poisoning support - after a panic during an active lock,

 * Max 32767 strong pointers and 32767 weak pointers.

Maybe something for your next tree with parent pointers?

== ARef ==

ARef takes over where [OwningRef](https://crates.io/crates/owning_ref) ends, by abstracting the owner even further.

This makes it possible to return, say, an `ARef<str>` and have the caller drop the owner
when done looking at it, without having to bother about whether the owner is a `String`, `Rc<String>`, a
`Ref<String>`, or something else.

It's also repr(C), so it can be transferred over an FFI boundary (if its target is repr(C), too).
 
== RMBA ==

The RMBA wraps either a `&T`, `&mut T`, `Box<T>` or `Arc<T>` within the size of a single pointer. 

There are two gotchas here: 

  * It will panic if you try to store a struct that's not 32 bit aligned.

  * Drop flags were removed in 1.13-nightly. If you run an earlier version,
    size might be larger than a single pointer due to the drop flag.

== Bx, Bxm ==

These are just simple wrappers around `Box` that lets you get rid of DerefMove.

This way you can return a Bx<T> in your API and still be sure the inner struct
does not move in memory. (This might be helpful if you're dealing with FFI or unsafe code.)

