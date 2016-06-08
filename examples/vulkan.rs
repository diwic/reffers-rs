// Tomaka's problem with sibling references: https://gist.github.com/tomaka/da8c374ce407e27d5dac
// In short; If you have a struct X and a struct Y<'a> where Y contains a reference to X,
// there is no way you can store both X and Y in the same parent struct.
//
// This is my attempt to solve it; to try to provide a safe abstraction where this works. (Haven't succeeded yet...)

use std::mem;
use std::marker::PhantomData;
use std::cell::{UnsafeCell, Cell};
use std::ptr;

pub struct Program(u64);

impl Drop for Program {
    fn drop(&mut self) { println!("Program dropped") }
}

pub struct CommandBuffer<'a>(u64, PhantomData<&'a ()>);

impl<'a> Drop for CommandBuffer<'a> {
    fn drop(&mut self) { println!("CommandBuffer dropped") }
}

impl<'a> CommandBuffer<'a> {
    pub fn new(_program: &'a Program) -> CommandBuffer<'a> { CommandBuffer(23, PhantomData) }
}

pub struct MyAssets(Box<[u8]>);
pub struct MyAssetsBuilder<'b>(UnsafeCell<Box<[u8]>>, Cell<i32>, PhantomData<&'b ()>);

impl<'b> MyAssetsBuilder<'b> {
    // FIXME: Padding to make sure no fields are unaligned
    fn total_size() -> usize { mem::size_of::<Program>() + mem::size_of::<CommandBuffer>() } 
    fn program_ptr(&self) -> *const Program {
        unsafe { &(*self.0.get())[0] as *const _ as *const Program }
    }
    fn command_buffer_ptr(&self) -> *const CommandBuffer {
        unsafe { &(*self.0.get())[mem::size_of::<Program>()] as *const _ as *const CommandBuffer }
    }

    pub fn new() -> MyAssetsBuilder<'b> {
        let v = vec!(0; Self::total_size());
        MyAssetsBuilder(UnsafeCell::new(v.into_boxed_slice()), Cell::new(0), PhantomData)
    }

    pub fn set_program(&self, p: Program) {
        assert_eq!(self.1.get(), 0);
        unsafe { ptr::write(self.program_ptr() as *mut _, p) };
        self.1.set(1);
    }

    pub fn program(&self) -> &Program {
        assert!(self.1.get() > 0);
        unsafe { &*self.program_ptr() }
    }

    pub fn set_command_buffer(&self, cb: CommandBuffer<'b>) {
        assert_eq!(self.1.get(), 1);
        unsafe { ptr::write(self.command_buffer_ptr() as *mut _, cb) };
        self.1.set(2);
    }

    pub fn command_buffer(&'b self) -> &CommandBuffer<'b> {
        assert!(self.1.get() > 1);
        unsafe { &*self.command_buffer_ptr() }
    }

    pub fn build(self) -> MyAssets {
        assert_eq!(self.1.get(), 2);
        self.1.set(-1);
        let pp = unsafe { &mut *self.0.get() };
        MyAssets(mem::replace(pp, Box::new([])))
    }

    pub fn truncate(&mut self, n: i32) {
        assert!(n >= 0); 
        loop {
            let z = self.1.get();
            if z <= n { return };
            match z {
                2 => unsafe { ptr::read(self.command_buffer_ptr()); },
                1 => unsafe { ptr::read(self.program_ptr()); },
                _ => unreachable!(),
            }
            self.1.set(z-1);
        }
    }
}

impl MyAssets {
    fn program_ptr(&self) -> *const Program {
        &self.0[0] as *const _ as *const Program
    }
    fn command_buffer_ptr(&self) -> *const CommandBuffer {
        &self.0[mem::size_of::<Program>()] as *const _ as *const CommandBuffer
    }

    pub fn program(&self) -> &Program {
        unsafe { &*self.program_ptr() }
    }
    pub fn command_buffer<'a>(&'a self) -> &CommandBuffer<'a> {
        unsafe { &*self.command_buffer_ptr() }
    }
}

impl Drop for MyAssets {
    fn drop(&mut self) {
        let _ = MyAssetsBuilder(UnsafeCell::new(mem::replace(&mut self.0, Box::new([]))), Cell::new(2), PhantomData);
    }
}

impl<'b> Drop for MyAssetsBuilder<'b> {
    fn drop(&mut self) { self.truncate(0) }
}

// And now for some testing...

fn make_asset() -> MyAssets {
    let a = MyAssetsBuilder::new();
    a.set_program(Program(56));
    {
      let cb = CommandBuffer::new(a.program());
      a.set_command_buffer(cb);
    }
    assert_eq!(a.program().0, 56);
    assert_eq!(a.command_buffer().0, 23);
    a.build()
}

fn this_should_not_compile() {
    let a = MyAssetsBuilder::new();
    a.set_program(Program(56));
    {
      let q = Program(99);
      let cb = CommandBuffer::new(&q);
      a.set_command_buffer(cb);
    } // Oh no! Dropping program before command buffer!
    a.command_buffer();
}

fn main() {
    this_should_not_compile();

    // Normal usage 
    {
        let newa = make_asset();
        println!("Assets built");
        assert_eq!(newa.program().0, 56);
        assert_eq!(newa.command_buffer().0, 23);
        println!("Dropping assets...");
    }

    // Error halfway through init
    {
        let a = MyAssetsBuilder::new();
        a.set_program(Program(29));
        println!("Program set but not command buffer");
    }
}
