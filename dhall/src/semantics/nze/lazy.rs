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

    pub fn force(&self) -> &Tgt {
        self.tgt.get_or_init(|| {
            let src = self.src.take().unwrap();
            src.eval()
        })
    }

    pub fn get_mut(&mut self) -> &mut Tgt {
        self.force();
        self.tgt.get_mut().unwrap()
    }
    pub fn into_inner(self) -> Tgt {
        self.force();
        self.tgt.into_inner().unwrap()
    }
}

impl<Src, Tgt> Deref for Lazy<Src, Tgt>
where
    Src: Eval<Tgt>,
{
    type Target = Tgt;
    fn deref(&self) -> &Self::Target {
        self.force()
    }
}

/// This implementation evaluates before cloning, because we can't clone the contents of a `Cell`.
impl<Src, Tgt> Clone for Lazy<Src, Tgt>
where
    Src: Eval<Tgt>,
    Tgt: Clone,
{
    fn clone(&self) -> Self {
        Self::new_completed(self.force().clone())
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
