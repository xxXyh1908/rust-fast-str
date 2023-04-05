#![doc(hidden)]
use std::sync::Arc;

#[derive(Clone)]
pub(super) enum NormalStringInner {
    Static,
    Arc(Arc<String>),
}

#[repr(C)]
#[derive(Clone)]
pub struct NormalString {
    pub(super) str: &'static str,
    pub(super) inner: NormalStringInner,
}

impl NormalString {
    #[inline(always)]
    pub(super) fn map_ref(&self, str: &str) -> Self {
        Self {
            str: unsafe { &*(str as *const str) },
            inner: self.inner.clone(),
        }
    }

    #[inline(always)]
    pub(super) fn map_ref_into(self, str: &str) -> Self {
        Self {
            str: unsafe { &*(str as *const str) },
            inner: self.inner,
        }
    }

    #[inline(always)]
    pub const fn from_static(str: &'static str) -> Self {
        Self {
            str,
            inner: NormalStringInner::Static,
        }
    }

    #[inline]
    pub fn is_static(&self) -> bool {
        if let NormalStringInner::Static = &self.inner {
            true
        } else {
            false
        }
    }

    #[inline]
    pub fn static_str(&self) -> Option<&'static str> {
        if let NormalStringInner::Static = &self.inner {
            Some(self.str)
        } else {
            None
        }
    }

    #[inline]
    pub fn from_string(str: String) -> Self {
        let str = Arc::new(str);

        Self {
            str: unsafe {
                let str: &str = str.as_str();
                &*(str as *const str)
            },
            inner: NormalStringInner::Arc(str),
        }
    }

    pub fn into_string(self) -> String {
        let Self { str, inner, .. } = self;
        if let NormalStringInner::Arc(arc) = inner {
            let arc_str = arc.as_str();
            if std::ptr::eq(arc_str as *const str, str as *const str) {
                let result = Arc::try_unwrap(arc);

                if let Ok(str) = result {
                    return str;
                }
            }
        }

        str.into()
    }

    #[inline(always)]
    pub fn as_str(&self) -> &str {
        self.str
    }
}
