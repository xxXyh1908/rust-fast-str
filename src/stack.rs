#![allow(unused)]
#![doc(hidden)]
use std::ops::RangeBounds;

/// Fixed-size stack-allocated string
#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct StackString<const SIZE: usize>([u8; SIZE]);

impl<const SIZE: usize> StackString<SIZE> {
    pub const MAX_LEN: usize = SIZE - 1;

    #[inline(always)]
    pub(super) fn map_ref(&self, str: &str) -> Self {
        Self::new(str)
    }

    #[inline(always)]
    pub(super) fn map_ref_into(self, str: &str) -> Self {
        Self::new(str)
    }

    #[inline(always)]
    pub const fn empty() -> Self {
        Self([0; SIZE])
    }

    pub fn new(str: &str) -> Self {
        let str: &[u8] = str.as_ref();
        let len = std::cmp::min(str.len(), Self::MAX_LEN);
        let mut buffer = Self::empty();
        buffer.0[0] = len as u8;
        unsafe { std::ptr::copy_nonoverlapping(str.as_ptr(), std::ptr::addr_of_mut!(buffer.0).cast::<u8>().add(1), len) };
        buffer
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(self.as_bytes()) }
    }

    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        let len = self.0[0] as usize;
        &self.0[1..1 + len]
    }
}
