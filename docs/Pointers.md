I used to use pointers - now what?
==================================

This is a post for you coming from C, like I did. In C, we use pointers a lot. Rust offers a lot of different replacements; all of which have their own pros and cons. This is a small opinionated guide to some common pointer patterns, and what to do in Rust instead.



References
----------

The most common Rust pointer replacement is the immutable reference `&` and the mutable reference `&mut`. You probably already know about them, if not, read [the book](https://doc.rust-lang.org/stable/book/references-and-borrowing.html) for an introduction. They should be your first choice whenever practical.

Typical usages are function call arguments and local variables, and sometimes return values as well - if reachable from the arguments, like this:

    impl Foo {
        fn get_bar(&self) -> &Bar { &self.bar }
    }

The rest of this guide is about when they are not practical.



New / free API
--------------

Here's a typical C API:

    typedef struct Foo Foo;
    Foo* foo_new(void);
    foo_dosomething(Foo*);
    foo_free(Foo*);

If we try to translate this to Rust, we'll soon find that we can't return a `&mut Foo` from `Foo::new`. The idiomatic solution is this:

    pub struct Foo { /* fields */ };

    impl Foo {
        pub fn new() -> Foo { /* code */ }
        pub fn dosomething(&mut self) { /* code */ }
    }

    impl Drop for Foo {
        fn drop(&mut self) { /* code for foo_free goes here, if any */ }
    }

There's no need to hide `Foo` behind a pointer for abstraction purposes, as the fields inside a struct are hidden from the API user by default.

There's also no need to put `Foo` in a `Box` - it's just superfluous to put `Foo` inside a heap allocation. Boxes are commonly used to contain closures and other traits, but rarely used for structs.



References in a struct
----------------------

In C, writing this is not a problem:

    struct Message {
        Connection* conn; /* stores a reference to conn, but does not own it */
    };
    struct Server {
        Message* message; /* owns the message */
    };

But in general, storing references in a struct in Rust is a bit clumsy, both w r t the syntax and the borrow checker. Syntax wise, you'll find your code cluttered with `'a`s, like this:

    pub struct Message<'a> {
        conn: &'a Connection,
    }

    pub struct Server<'a> {
        message: Message<'a>,
    }

As you see, not only `Message` gets the `'a` clutter, but anything else containing a `Message` as well (and anything containing a `Server`, etc).

But that's not all. During the lifetime of `Message`, you must prove to the compiler that the `Connection` is not destroyed, mutated or moved. And in practice, this can be difficult to do. My experience is that lifetimes in structs, are mostly useful when those structs are short lived, e g, if a struct is just an iterator over something else, like [this one](https://doc.rust-lang.org/std/slice/struct.Iter.html).



Using indices
-------------

Say that you have written a wrapper around a file format, and that file format contains header and data. After initial parsing, you have found where the data starts and want to store a pointer to the data. C version:

    struct MyFileFormat {
        unsigned char* file_contents; /* owned by MyFileFormat */
        unsigned char* data; /* a pointer to somewhere inside file_contents */
    };

Naive Rust version, that does not work:

    pub struct MyFileFormat {
        file_contents: Vec<u8>,
        data: &[u8],
    }

(Side note: a C `unsigned char` and `signed char` often does not translate to a Rust [char](https://doc.rust-lang.org/std/primitive.char.html) - a Rust `char` is always Unicode. Rust's version of `unsigned char` is usually `u8`. By extension, a `unsigned char *` is often not a `&str` but a `&[u8]` or `Vec<u8>`.)

Anyhow, references to another struct field are not allowed in Rust. In this case, just storing the index is the simplest option:

    pub struct MyFileFormat {
        file_contents: Vec<u8>,
        data: usize, /* data part of file is at file_contents[data..] */
    }


 
Rc (and Arc)
------------

For longer lived structs, which needs to be referenced from many places, you'll have to resort to [Rc](https://doc.rust-lang.org/std/rc/struct.Rc.html) (or [Arc](https://doc.rust-lang.org/std/sync/struct.Arc.html), the thread safe version). And along comes the usual problems of making sure there are no Rc cycles, or your application will have memory leaks. But in Rust, you'll quickly discover something else: anything inside an Rc cannot be mutated. All you got is an immutable reference.

To the rescue comes [RefCell](https://doc.rust-lang.org/std/cell/struct.RefCell.html), which allows the interior to be mutated even through just an immutable reference. You might find `Rc<RefCell<T>>` to be a fairly common pattern to resolve this, but it comes with its own twist: now you have to think about avoiding RefCell panics. Here's an example of how a RefCell panic can occur:

    struct Wheel {
        bicycle: Rc<RefCell<Bicycle>>,
        diameter: i32,
    }

    struct Bicycle {
        wheels: Vec<Wheel>,
        size: i32,
    }

    impl Bicycle {
        pub fn inflate(&mut self) {
            self.size += 1;
            for w in &mut self.wheels {
                w.adjust_diameter();
            }
        }
    }

    impl Wheel {
        pub fn adjust_diameter(&mut self) {
            self.diameter = self.bicycle.borrow().size / 2;
        }
    }

Calling `Bicycle::inflate` will require the `RefCell` to already be borrowed mutably (how else can we call a function that takes a `&mut self`?). When `adjust_diameter` then borrows the bicycle immutably, it is already mutably borrowed and your program will panic. This is a relatively simple example - real world code is more complex and so the potential panic can be more difficult to reveal.
The solution is to avoid `Rc<RefCell<Bicycle>>` and instead RefCell or [Cell](https://doc.rust-lang.org/std/cell/struct.Cell.html) the fields that can change, like this:

    struct Wheel {
        bicycle: Rc<Bicycle>,
        diameter: Cell<i32>,
    }

    struct Bicycle {
        wheels: RefCell<Vec<Wheel>>,
        size: Cell<i32>,
    }

    impl Bicycle {
        pub fn inflate(&self) {
            self.size.set(self.size.get() + 1);
            for w in &*self.wheels.borrow() {
                w.adjust_diameter();
            }
        }
    }

    impl Wheel {
        pub fn adjust_diameter(&self) {
            self.diameter.set(self.bicycle.size.get() / 2);
        }
    }

Now we can change the fields inside `Bicycle` and `Wheel`, and still avoid mutable references.

Two additional notes:

 1) Cell is generally preferred over RefCell, where both are applicable, because Cell just copies data in and out instead of borrowing it, thereby circumventing the problem. But in many cases Cell won't work, due to the types that a Cell can contain is quite limited.

 2) In case memory is scarce, it could be good to remember that every `Rc` (and `Arc`) costs two extra `usize`, and a `RefCell` costs one extra `usize`. `Cell`s have no extra memory cost. If this is a problem, feel free to have a look at [my Rc/RefCell struct](https://docs.rs/reffers/%5E0/reffers/rc/) which has configurable overhead and a few other features that the ordinary Rc/RefCell does not have.



Interlude: Unsafe / raw pointers
--------------------------------

Resist the temptation to use raw pointers and other unsafe patterns. Not only because you lose Rust's guarantees, but also because there are subtle differences between C and unsafe Rust, that in some cases makes unsafe Rust even more unsafe than C. 

One example of such a pitfall, is that Rust tells its LLVM backend that `&` references will never be written through, and that its `&mut` references are unique. Rust does so in the hope of LLVM being able to generate better code, but this also means, e g, that you cannot transmute a `&` into a `&mut` just because you know that no other references exist at that point: because then you're violating what Rust tells LLVM, which can in turn lead to Undefined Behaviour, i e, really weird bugs. For more info, see [documentation for UnsafeCell](https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html) or the [Nomicon](https://doc.rust-lang.org/nomicon/transmutes.html).

There are other pitfalls as well, including the fact that it's [not even completely defined](https://github.com/nikomatsakis/rust-memory-model) at this point exactly what you can and can't do in unsafe Rust. So, resist the thought "I can go unsafe here - I know it's safe because...", unless you're sure you know what you're doing and you're aware of the potential pitfalls.



Being generic over the owner
----------------------------

Back to our file format example, and let's add a twist: the buffer is allocated by the owner for maximum flexibility. This would allow the API user to point to something else than loading from a file, e g, shared memory, a resource inside the library, something made by the API user in an earlier step, etc. So one API user would like to use your code on a `Vec<u8>`, another has a `&[u8]` on the stack, and so on. If the file is big, it makes sense to avoid extra copies of it in memory. 
And in C, you would just have this be a pointer as usual, and just not bothering about freeing it when you're done using it.

In Rust, you want anything that you can easily transform into a `&[u8]` to be usable with your file format parser, but you don't want to specify a `&[u8]` (because storing references in struct is often impractical). 
There is another solution: to be generic over [AsRef](https://doc.rust-lang.org/std/convert/trait.AsRef.html) (or it's mutable version, [AsMut](https://doc.rust-lang.org/std/convert/trait.AsMut.html)), like this:

    pub struct MyFileFormat<T: AsRef<[u8]>> {
        file_contents: T,
        data: usize, /* data part of file is at file_contents.as_ref()[data..] */
    }

There's another caveat with this approach though - choosing between `AsRef` and `Deref`. `AsRef` is the more correct solution, but in the wild, my experience is that crates implement `Deref` for their structs more often than `AsRef`, so it might be that `Deref<Target=T>` is a more practical solution than `AsRef<T>`.



Tuples and results
------------------

Here's a different example where you would use a pointer in C. If you have a function that calculates both the quotient and the remainder, a common pattern to do that in C would be:

    long long divide(double dividend, double divisor, double* remainder);

...and only set remainder in case the supplied pointer is not NULL. In Rust, just use a tuple:

    /// Returns a tuple of (dividend, divisor)
    pub fn divide(dividend: f64, divisor: f64) -> (i64, f64) { /* code */ }

A similar example comes for GLib where many functions have an error pointer:

    gint g_file_open_tmp(const gchar* tmpl, gchar **name_used, GError **error);

The Rust version will just return a Result:

    /// Returns a tuple of (handle, name_used) on success or an error otherwise.
    GFile::open_tmp(tmpl: &Path) -> Result<(i32, String), GError> { /* code */ }



Wrap up
-------

I hope you've found this guide helpful. I wanted to write it while I still remember how it was, being new to all these concepts. Maybe it also gives a small background to the smart pointers I've been writing in this repository. If you have any corrections or comments, feel free to file an [issue](https://github.com/diwic/reffers-rs/issues) or a [PR](https://github.com/diwic/reffers-rs/pulls). Thanks!

