#![feature(slice_patterns)]
#![doc(html_root_url = "https://docs.rs/improved_slice_patterns/1.0.1")]

//! A tiny crate that provides two macros to help matching
//! on `Vec`s and iterators using the syntax of
//! [`slice_patterns`][slice_patterns]
//!
//! [slice_patterns]: https://doc.rust-lang.org/nightly/unstable-book/language-features/slice-patterns.html

/// Destructure an iterator using the syntax of slice_patterns.
///
/// Wraps the match body in `Some` if there was a match; returns
/// `None` otherwise.
///
/// Contrary to slice_patterns, this allows moving out
/// of the iterator.
///
/// A variable length pattern (`x..`) is only allowed as the last
/// pattern, unless the iterator is double-ended.
///
/// Example:
/// ```edition2018
/// use improved_slice_patterns::destructure_iter;
///
/// let vec = vec![Some(1), Some(2), Some(3), None];
///
/// let res = destructure_iter!(vec.into_iter();
///     [Some(x), y.., z] => {
///         // x: usize
///         // y: impl Iterator<Option<usize>>
///         // z: Option<usize>
///         (x, y.collect::<Vec<_>>(), z)
///     }
/// );
///
/// assert_eq!(res, Some((1, vec![Some(2), Some(3)], None)));
///
/// # Ok::<(), ()>(())
/// ```
///
///
#[macro_export]
macro_rules! destructure_iter {
    // Variable length pattern
    (@match_forwards, $iter:expr, ($body:expr), $x:ident.., $($rest:tt)*) => {
        $crate::destructure_iter!(@match_backwards,
            $iter,
            ({
                let $x = $iter;
                $body
            }),
            $($rest)*
        )
    };
    // Special variable length pattern with a common unary variant
    (@match_forwards, $iter:expr, ($body:expr),
            $variant:ident ($x:ident).., $($rest:tt)*) => {
        $crate::destructure_iter!(@match_backwards,
            $iter,
            ({
                let $x = $iter
                    .map(|x| match x {
                        $variant(y) => y,
                        _ => unreachable!(),
                    });
                $body
            }),
            $($rest)*
        )
    };
    // Variable length pattern without a binder
    (@match_forwards, $iter:expr, ($body:expr), .., $($rest:tt)*) => {
        $crate::destructure_iter!(@match_backwards,
            $iter,
            ($body),
            $($rest)*
        )
    };
    // Single item pattern
    (@match_forwards, $iter:expr, ($body:expr), $x:pat, $($rest:tt)*) => {
        if let std::option::Option::Some($x) = $iter.next() {
            $crate::destructure_iter!(@match_forwards,
                $iter,
                ($body),
                $($rest)*
            )
        } else {
            std::option::Option::None
        }
    };
    // Single item pattern after a variable length one: declare reversed and take from the end
    (@match_backwards, $iter:expr, ($body:expr), $x:pat, $($rest:tt)*) => {
        $crate::destructure_iter!(@match_backwards, $iter, (
            if let std::option::Option::Some($x) = $iter.next_back() {
                $body
            } else {
                std::option::Option::None
            }
        ), $($rest)*)
    };

    // Check no elements remain
    (@match_forwards, $iter:expr, ($body:expr) $(,)*) => {
        if $iter.next().is_some() {
            std::option::Option::None
        } else {
            $body
        }
    };
    // After a variable length pattern, everything has already been consumed
    (@match_backwards, $iter:expr, ($body:expr) $(,)*) => {
        $body
    };

    ($iter:expr; [$($args:tt)*] => $body:expr) => {
        {
            #[allow(unused_mut)]
            let mut iter = $iter;
            $crate::destructure_iter!(@match_forwards,
                iter,
                (std::option::Option::Some($body)),
                $($args)*,
            )
        }
    };
}

/// Pattern-match on a vec using the syntax of slice_patterns.
///
/// Wraps the match body in `Some` if there was a match; returns
/// `None` otherwise.
///
/// Contrary to slice_patterns, this allows moving out
/// of the `Vec`.
///
/// A variable length pattern (`x..`) returns an iterator.
///
/// Example:
/// ```edition2018
/// #![feature(slice_patterns)]
/// use improved_slice_patterns::match_vec;
///
/// let vec = vec![Some(1), Some(2), Some(3), None];
///
/// let res = match_vec!(vec;
///     [Some(_), y.., None] => {
///         y.collect::<Vec<_>>()
///     },
///     [None, None] => {
///         vec![]
///     },
///     [..] => vec![]
/// );
///
/// assert_eq!(res, Some(vec![Some(2), Some(3)]));
///
///
/// let vec = vec![Some(1), Some(2), Some(3), None];
///
/// let res = match_vec!(vec;
///     [Some(_), y.., Some(_)] => {
///         y.collect::<Vec<_>>()
///     },
///     [None, None] => {
///         vec![]
///     },
/// );
///
/// assert_eq!(res, None); // there was no match
///
/// # Ok::<(), ()>(())
/// ```
///
///
#[macro_export]
macro_rules! match_vec {
    // Variable length pattern
    (@make_pat; ($($acc:tt)*), $x:ident.., $($rest:tt)*) => {
        $crate::match_vec!(@make_pat;
            ($($acc)*, $x..),
            $($rest)*
        )
    };
    // Special variable length pattern with a common unary variant
    (@make_pat; ($($acc:tt)*), $variant:ident ($x:ident).., $($rest:tt)*) => {
        $crate::match_vec!(@make_pat;
            ($($acc)*, $x..),
            $($rest)*
        )
    };
    // Variable length pattern without a binder
    (@make_pat; ($($acc:tt)*), .., $($rest:tt)*) => {
        $crate::match_vec!(@make_pat;
            ($($acc)*, ..),
            $($rest)*
        )
    };
    // Single item pattern
    (@make_pat; ($($acc:tt)*), $x:pat, $($rest:tt)*) => {
        $crate::match_vec!(@make_pat;
            ($($acc)*, $x),
            $($rest)*
        )
    };
    (@make_pat; (, $($acc:tt)*), $(,)*) => {
        [$($acc)*]
    };
    (@make_pat; ($($acc:tt)*), $(,)*) => {
        [$($acc)*]
    };

    (@make_filter; $x:ident.., $($rest:tt)*) => {
        $crate::match_vec!(@make_filter;
            $($rest)*
        )
    };
    (@make_filter; $variant:ident ($x:ident).., $($rest:tt)*) => {
        {
            // Circumvent https://github.com/rust-lang/rust/issues/59803
            let is_all_variant = || $x.iter()
                .all(|x| match x {
                    $variant(_) => true,
                    _ => false,
                });
            is_all_variant()
        }
        &&
        $crate::match_vec!(@make_filter;
            $($rest)*
        )
    };
    (@make_filter; .., $($rest:tt)*) => {
        $crate::match_vec!(@make_filter;
            $($rest)*
        )
    };
    (@make_filter; $x:pat, $($rest:tt)*) => {
        $crate::match_vec!(@make_filter;
            $($rest)*
        )
    };
    (@make_filter; $(,)*) => {
        true
    };

    ($arg:expr; $( [$($args:tt)*] => $body:expr ),* $(,)*) => {
        {
            let vec = $arg;
            // Match as references to decide which branch to take
            // I think `match_default_bindings` should make this always work but
            // there may be some patterns this doesn't capture.
            #[allow(unused_variables, unreachable_patterns)]
            match vec.as_slice() {
                $(
                    $crate::match_vec!(@make_pat; (), $($args)*,)
                    if
                    $crate::match_vec!(@make_filter; $($args)*,)
                    => {
                        // Actually consume the values
                        #[allow(unused_mut)]
                        let mut iter = vec.into_iter();
                        $crate::destructure_iter!(iter; [$($args)*] => $body)
                    }
                )*
                _ => std::option::Option::None,
            }
        }
    };
}

#[test]
fn test() {
    let test = |v: Vec<Option<isize>>| {
        match_vec!(v.into_iter();
            [Some(_x), None, None] => 4,
            [Some(_x), None] => 2,
            [None, Some(y)] => 1,
            [None, _y..] => 3,
            [_x.., Some(y), Some(z), None] => y - z,
            [Some(ys)..] => ys.sum(),
            [] => 0,
            [..] => -1,
        )
        .unwrap()
    };

    assert_eq!(test(vec![Some(0), None, None]), 4);
    assert_eq!(test(vec![Some(0), None]), 2);
    assert_eq!(test(vec![None, Some(0)]), 1);
    assert_eq!(test(vec![Some(1), Some(2), Some(5), Some(14), None]), -9);
    assert_eq!(test(vec![Some(1), Some(2), Some(3), Some(4)]), 10);
    assert_eq!(test(vec![None]), 3);
    assert_eq!(test(vec![]), 0);
    assert_eq!(test(vec![Some(0), None, Some(1)]), -1);

    // Test move out of pattern
    struct Foo;
    let _: (Foo, Foo) = match_vec!(vec![Some(Foo), Some(Foo)].into_iter();
        [Some(f1), Some(f2)] => (f1, f2),
    )
    .unwrap();
}
