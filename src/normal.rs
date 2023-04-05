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
            str: unsafe { &*std::ptr::addr_of!(*str) },
            inner: self.inner.clone(),
        }
    }

    #[inline(always)]
    pub(super) fn map_ref_into(self, str: &str) -> Self {
        Self {
            str: unsafe { &*std::ptr::addr_of!(*str) },
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
                let str = str.as_str();
                let ptr = std::ptr::addr_of!(*str);
                &*ptr
            },
            inner: NormalStringInner::Arc(str),
        }
    }

    pub fn into_string(self) -> String {
        let Self { str, inner, .. } = self;
        if let NormalStringInner::Arc(arc) = inner {
            if std::ptr::eq(std::ptr::addr_of!(*arc.as_str()), std::ptr::addr_of!(*str)) {
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

// fn optimize(this: &NormalString, other: &NormalString) {
//     match &this.inner {
//         NormalStringInner::Static => {
//             if let NormalStringInner::Arc(_) = &other.inner {
//                 unsafe {
//                     let ptr = std::ptr::addr_of!(*other) as *mut NormalString;
//                     (*ptr).str = this.str;
//                     (*ptr).inner = NormalStringInner::Static;
//                 }
//             }
//         }
//         NormalStringInner::Arc(_) => {
//             if let NormalStringInner::Static = &this.inner {
//                 unsafe {
//                     let ptr = std::ptr::addr_of!(*this) as *mut NormalString;
//                     (*ptr).str = other.str;
//                     (*ptr).inner = NormalStringInner::Static;
//                 }
//             }
//         }
//     };
// }

// impl PartialEq for NormalString {
//     #[inline]
//     fn eq(&self, other: &Self) -> bool {
//         if PartialEq::eq(self.as_str(), other.as_str()) {
//             optimize(self, other);

//             true
//         } else {
//             false
//         }
//     }
// }

// impl Eq for NormalString {}

// impl PartialOrd for NormalString {
//     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
//         PartialOrd::partial_cmp(self.as_str(), other.as_str())
//     }
// }

// impl Ord for NormalString {
//     #[inline]
//     fn cmp(&self, other: &Self) -> std::cmp::Ordering {
//         let result = Ord::cmp(self.as_str(), other.as_str());
//         if result == std::cmp::Ordering::Equal {
//             optimize(self, other);
//         }

//         result
//     }
// }
