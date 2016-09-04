
#![feature(test)]


extern crate test;
extern crate reffers;
use reffers::*;
use std::sync::Arc;
    
    #[bench]
    fn rmba(b: &mut test::Bencher) {
        let z = Arc::new(String::from("Hello world"));
        let q = RMBA::from(z);
        b.iter(|| test::black_box(&q).len());
    }

    #[bench]
    fn slow_rmba(b: &mut test::Bencher) {
        use std::sync::Arc;
        let z = Arc::new(String::from("Hello world"));
        let q = SlowRMBA::Arc(z);
        b.iter(|| test::black_box(&q).len());
    }


