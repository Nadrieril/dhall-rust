use once_cell::unsync::OnceCell;
use std::cell::Cell;
use std::fmt::Debug;
use std::ops::Deref;

pub trait Eval<Tgt> {
    fn eval(self) -> Tgt;
}

/// A value which is initialized from a `Src` on the first access.
pub struct Lazy<Src, Tgt> {
    /// Exactly one of `src` of `tgt` must be set at a given time.
    /// Once `src` is unset and `tgt` is set, we never go back.
    src: Cell<Option<Src>>,
    tgt: OnceCell<Tgt>,
}

impl<Src, Tgt> Lazy<Src, Tgt>
where
    Src: Eval<Tgt>,
{
    /// Creates a new lazy value with the given initializing value.
    pub fn new(src: Src) -> Self {
        Lazy {
            src: Cell::new(Some(src)),
            tgt: OnceCell::new(),
        }
    }
    /// Creates a new lazy value with the given already-initialized value.
    pub fn new_completed(tgt: Tgt) -> Self {
        let lazy = Lazy {
            src: Cell::new(None),
            tgt: OnceCell::new(),
        };
        let _ = lazy.tgt.set(tgt);
        lazy
    }
}

impl<Src, Tgt> Deref for Lazy<Src, Tgt>
where
    Src: Eval<Tgt>,
{
    type Target = Tgt;
    fn deref(&self) -> &Self::Target {
        self.tgt.get_or_init(|| {
            let src = self.src.take().unwrap();
            src.eval()
        })
    }
}

impl<Src, Tgt> Debug for Lazy<Src, Tgt>
where
    Tgt: Debug,
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(tgt) = self.tgt.get() {
            fmt.debug_tuple("Lazy@Init").field(tgt).finish()
        } else {
            fmt.debug_tuple("Lazy@Uninit").finish()
        }
    }
}
