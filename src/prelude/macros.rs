macro_rules! for_loop {
    (let mut $i:ident = $init:expr; $cond:expr; $next:expr => $body:block) => {
        let mut $i = $init;
        while $cond {
            $body;
            $next;
        }
    };
}

pub(crate) use for_loop;
