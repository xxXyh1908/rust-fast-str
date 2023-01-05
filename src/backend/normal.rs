use crate::normal::NormalString;

#[repr(transparent)]
#[derive(Clone)]
pub struct FastStr(NormalString);

#[allow(unused)]
impl FastStr {
    #[inline]
    pub(super) fn do_sub_with<
        'a,
        R: 'a,
        F: FnOnce(&'a str, Box<dyn Fn(&str) -> Self + 'a>) -> R,
    >(
        &'a self,
        f: F,
    ) -> R {
        f(self.0.str, Box::new(|str| Self(self.0.map_ref(str))))
    }

    #[inline]
    pub(super) fn do_sub_into<F: FnOnce(&str) -> &str>(self, f: F) -> Self {
        let str = f(self.0.str);
        Self(self.0.map_ref_into(str))
    }

    /// Create an empty FastStr.
    #[inline]
    pub const fn new() -> Self {
        Self::from_static("")
    }

    /// Create a FastStr based on a `'static` data reference .
    #[inline]
    pub const fn from_static(str: &'static str) -> Self {
        Self(NormalString::from_static(str))
    }

    /// Create a FastStr based on String storage.
    #[inline]
    pub fn from_string(str: String) -> Self {
        Self(NormalString::from_string(str))
    }

    /// Create an FastStr and automatically use the best storage method.
    #[inline]
    pub fn from_ref(str: &str) -> Self {
        Self(NormalString::from_string(str.into()))
    }

    /// Converted to a string of standard [`String`] type.
    #[inline]
    pub fn into_string(self) -> String {
        self.0.into_string()
    }

    /// Extracts a string slice containing the entire [FastStr].
    #[inline]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    /// Judge whether [FastStr] uses static storage.
    #[inline]
    pub fn is_static(&self) -> bool {
        self.0.is_static()
    }
}
