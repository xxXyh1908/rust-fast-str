use crate::{normal::NormalString, stack::StackString};
use std::mem::{size_of, ManuallyDrop};

const STACK_STRING_SIZE: usize = size_of::<NormalString>() - size_of::<*const u8>();

union FastStrInner {
    ptr: *const u8,
    inline: (*const u8, StackString<STACK_STRING_SIZE>),
    normal: ManuallyDrop<NormalString>,
}

#[repr(transparent)]
pub struct FastStr(FastStrInner);

impl FastStrInner {
    #[inline(always)]
    fn is_inline(&self) -> bool {
        unsafe { self.ptr.is_null() }
    }

    #[inline(always)]
    fn get_inline_ref(&self) -> &StackString<STACK_STRING_SIZE> {
        unsafe { &self.inline.1 }
    }

    #[inline(always)]
    fn get_inline(&self) -> StackString<STACK_STRING_SIZE> {
        unsafe { self.inline.1 }
    }

    #[inline(always)]
    fn get_normal_ref(&self) -> &NormalString {
        unsafe { &self.normal }
    }

    #[inline]
    fn get_normal(mut self) -> NormalString {
        unsafe {
            let result = ManuallyDrop::take(&mut self.normal);
            std::mem::forget(self);
            result
        }
    }

    #[inline(always)]
    const fn from_inline(inline: StackString<STACK_STRING_SIZE>) -> Self {
        Self {
            inline: (std::ptr::null(), inline),
        }
    }

    #[inline(always)]
    const fn from_normal(normal: NormalString) -> Self {
        Self {
            normal: ManuallyDrop::new(normal),
        }
    }
}

#[allow(unused)]
impl FastStr {
    pub(super) fn do_sub_with<
        'a,
        R: 'a,
        F: FnOnce(&'a str, Box<dyn Fn(&str) -> Self + 'a>) -> R,
    >(
        &'a self,
        f: F,
    ) -> R {
        if self.is_inline() {
            let inline = self.get_inline_ref();
            f(
                inline.as_str(),
                Box::new(|str| Self::from_inline(inline.map_ref(str))),
            )
        } else {
            let normal = self.get_normal_ref();
            f(
                normal.as_str(),
                Box::new(|str| Self::from_normal(normal.map_ref(str))),
            )
        }
    }

    pub(super) fn do_sub_into<F: FnOnce(&str) -> &str>(self, f: F) -> Self {
        if self.is_inline() {
            let inline = self.get_inline();
            let str = f(inline.as_str());
            Self::from_inline(inline.map_ref_into(str))
        } else {
            let normal = self.get_normal();
            let str = f(normal.str);
            Self::from_normal(normal.map_ref_into(str))
        }
    }

    #[inline(always)]
    fn is_inline(&self) -> bool {
        self.0.is_inline()
    }

    #[inline(always)]
    fn get_inline_ref(&self) -> &StackString<STACK_STRING_SIZE> {
        self.0.get_inline_ref()
    }

    #[inline(always)]
    fn get_inline(&self) -> StackString<STACK_STRING_SIZE> {
        self.0.get_inline()
    }

    #[inline(always)]
    fn get_normal_ref(&self) -> &NormalString {
        self.0.get_normal_ref()
    }

    #[inline(always)]
    fn get_normal(self) -> NormalString {
        self.0.get_normal()
    }

    #[inline(always)]
    const fn from_inline(inline: StackString<STACK_STRING_SIZE>) -> Self {
        Self(FastStrInner::from_inline(inline))
    }

    #[inline(always)]
    const fn from_normal(normal: NormalString) -> Self {
        Self(FastStrInner::from_normal(normal))
    }

    /// Create an empty FastStr.
    #[inline]
    pub const fn new() -> Self {
        Self::from_static("")
    }

    /// Create a FastStr based on a `'static` data reference .
    #[inline]
    pub const fn from_static(str: &'static str) -> Self {
        Self::from_normal(NormalString::from_static(str))
    }

    /// Create a FastStr based on String storage.
    #[inline]
    pub fn from_string(str: String) -> Self {
        Self::from_normal(NormalString::from_string(str))
    }

    /// Create an FastStr and automatically use the best storage method.
    pub fn from_ref(str: &str) -> Self {
        if str.len() <= StackString::<STACK_STRING_SIZE>::MAX_LEN {
            Self::from_inline(StackString::new(str))
        } else {
            Self::from_normal(NormalString::from_string(str.into()))
        }
    }

    /// Converted to a string of standard [`String`] type.
    pub fn into_string(self) -> String {
        if self.is_inline() {
            self.get_inline().as_str().into()
        } else {
            self.get_normal().into_string()
        }
    }

    /// Extracts a string slice containing the entire [FastStr].
    pub fn as_str(&self) -> &str {
        if self.is_inline() {
            self.get_inline_ref().as_str()
        } else {
            self.get_normal_ref().as_str()
        }
    }

    /// Judge whether [FastStr] uses static storage.
    pub fn is_static(&self) -> bool {
        if self.is_inline() {
            false
        } else {
            self.get_normal_ref().is_static()
        }
    }

    #[inline]
    pub fn static_str(&self) -> Option<&'static str> {
        if self.is_inline() {
            None
        } else {
            self.get_normal_ref().static_str()
        }
    }
}

impl Clone for FastStr {
    /// O(1) Clone() of time complexity.
    fn clone(&self) -> Self {
        if self.is_inline() {
            Self::from_inline(self.get_inline())
        } else {
            Self::from_normal(self.get_normal_ref().clone())
        }
    }
}

impl Drop for FastStrInner {
    fn drop(&mut self) {
        if !self.is_inline() {
            unsafe { ManuallyDrop::drop(&mut self.normal) }
        }
    }
}
