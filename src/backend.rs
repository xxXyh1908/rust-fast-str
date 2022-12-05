use super::{
    iter::{
        MatchIndicesInternal, MatchesInternal, SearcherIterator, SearcherIteratorRev,
        SplitInclusiveInternal, SplitInternal, SplitNInternal,
    },
    pattern::{Pattern, ReverseSearcher, SearchStep, Searcher, StrSearcher},
};
use std::{
    borrow::{Borrow, Cow},
    fmt::{Debug, Display},
    hash::Hash,
    ops::{Add, Deref, RangeBounds},
    rc::Rc,
    str::FromStr,
    sync::Arc,
};

#[doc(hidden)]
#[cfg(any(not(feature = "stack"), target_pointer_width = "16", target_pointer_width = "32"))]
#[path = "backend_normal.rs"]
mod internal;
#[doc(hidden)]
#[cfg(not(any(not(feature = "stack"), target_pointer_width = "16", target_pointer_width = "32")))]
#[path = "backend_stack.rs"]
mod stack_backend;

pub use self::stack_backend::FastString;

unsafe impl Sync for FastString {}
unsafe impl Send for FastString {}

impl FastString {
    /// Creates a new [FastString] by repeating a string `n` times.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fast_str::FastString;
    /// assert_eq!(FastString::from("abc").repeat(4), "abcabcabcabc");
    /// ```
    pub fn repeat(&self, n: usize) -> Self {
        if n == 1 {
            self.clone()
        } else {
            Self::from_string(self.as_str().repeat(n))
        }
    }

    /// Returns a copy of this string where each character is mapped to its
    /// ASCII upper case equivalent.
    ///
    /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To uppercase ASCII characters in addition to non-ASCII characters, use
    /// [`to_uppercase`].
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_str::FastString;
    /// let s = FastString::from("Grüße, Jürgen ❤");
    ///
    /// assert_eq!("GRüßE, JüRGEN ❤", s.to_ascii_uppercase());
    /// ```
    ///
    /// [`to_uppercase`]: #method.to_uppercase
    #[inline]
    pub fn to_ascii_uppercase(&self) -> Self {
        Self::from_string(self.as_str().to_ascii_uppercase())
    }

    /// Returns a copy of this string where each character is mapped to its
    /// ASCII lower case equivalent.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To lowercase ASCII characters in addition to non-ASCII characters, use
    /// [`to_lowercase`].
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_str::FastString;
    /// let s = FastString::from("Grüße, Jürgen ❤");
    ///
    /// assert_eq!("grüße, jürgen ❤", s.to_ascii_lowercase());
    /// ```
    ///
    /// [`to_lowercase`]: #method.to_lowercase
    #[inline]
    pub fn to_ascii_lowercase(&self) -> Self {
        Self::from_string(self.as_str().to_ascii_lowercase())
    }

    /// Returns the uppercase equivalent of this string slice, as a new [FastString].
    ///
    /// 'Uppercase' is defined according to the terms of the Unicode Derived Core Property
    /// `Uppercase`.
    ///
    /// Since some characters can expand into multiple characters when changing
    /// the case, this function returns a [FastString] instead of modifying the
    /// parameter in-place.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let s = FastString::from("hello");
    ///
    /// assert_eq!("HELLO", s.to_uppercase());
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let new_year = FastString::from("农历新年");
    ///
    /// assert_eq!(new_year, new_year.to_uppercase());
    /// ```
    ///
    /// One character can become multiple:
    /// ```
    /// use fast_str::FastString;
    /// let s = FastString::from("tschüß");
    ///
    /// assert_eq!("TSCHÜSS", s.to_uppercase());
    /// ```
    #[inline]
    pub fn to_uppercase(&self) -> Self {
        Self::from_string(self.as_str().to_uppercase())
    }

    /// Returns the lowercase equivalent of this string slice, as a new [FastString].
    ///
    /// 'Lowercase' is defined according to the terms of the Unicode Derived Core Property
    /// `Lowercase`.
    ///
    /// Since some characters can expand into multiple characters when changing
    /// the case, this function returns a [FastString] instead of modifying the
    /// parameter in-place.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let s = FastString::from("HELLO");
    ///
    /// assert_eq!("hello", s.to_lowercase());
    /// ```
    ///
    /// A tricky example, with sigma:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let sigma = FastString::from("Σ");
    ///
    /// assert_eq!("σ", sigma.to_lowercase());
    ///
    /// // but at the end of a word, it's ς, not σ:
    /// let odysseus = FastString::from("ὈΔΥΣΣΕΎΣ");
    ///
    /// assert_eq!("ὀδυσσεύς", odysseus.to_lowercase());
    /// ```
    ///
    /// Languages without case are not changed:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let new_year = FastString::from("农历新年");
    ///
    /// assert_eq!(new_year, new_year.to_lowercase());
    /// ```
    #[inline]
    pub fn to_lowercase(&self) -> Self {
        Self::from_string(self.as_str().to_lowercase())
    }

    /// Converts a string slice to a byte slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let bytes = FastString::from("bors").as_bytes();
    /// assert_eq!(b"bors", bytes);
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        self.as_str().as_bytes()
    }

    /// Returns an substring of [FastString].
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_str::FastString;
    /// let v = FastString::from("🗻∈🌏");
    ///
    /// assert_eq!("🗻", v.slice(0..4));
    /// assert_eq!("∈", v.slice(4..7));
    /// assert_eq!("🌏", v.slice(7..11));
    /// ```
    pub fn slice<R>(&self, range: R) -> Self
    where
        R: RangeBounds<usize>,
    {
        use std::ops::Bound;

        self.do_sub_with(|str, wrapper| {
            let len = str.len();

            let start = match range.start_bound() {
                Bound::Included(&n) => std::cmp::max(0, n),
                Bound::Excluded(&n) => std::cmp::max(0, n + 1),
                Bound::Unbounded => 0,
            };

            let end = match range.end_bound() {
                Bound::Included(&n) => std::cmp::min(len, n + 1),
                Bound::Excluded(&n) => std::cmp::min(len, n),
                Bound::Unbounded => len,
            };

            wrapper(&str[start..end])
        })
    }

    /// Returns a [FastString] with leading and trailing whitespace removed.
    ///
    /// 'Whitespace' is defined according to the terms of the Unicode Derived
    /// Core Property `White_Space`, which includes newlines.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let s = FastString::from("\n Hello\tworld\t\n");
    ///
    /// assert_eq!("Hello\tworld", s.trim());
    /// ```
    #[inline]
    pub fn trim(&self) -> Self {
        self.do_sub_with(|str, wrapper| wrapper(str.trim()))
    }

    #[inline]
    pub fn trim_into(self) -> Self {
        self.do_sub_into(|str| str.trim())
    }

    /// Returns a [FastString] with leading whitespace removed.
    ///
    /// 'Whitespace' is defined according to the terms of the Unicode Derived
    /// Core Property `White_Space`, which includes newlines.
    ///
    /// # Text directionality
    ///
    /// A string is a sequence of bytes. `start` in this context means the first
    /// position of that byte string; for a left-to-right language like English or
    /// Russian, this will be left side, and for right-to-left languages like
    /// Arabic or Hebrew, this will be the right side.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let s = FastString::from("\n Hello\tworld\t\n");
    /// assert_eq!("Hello\tworld\t\n", s.trim_start());
    /// ```
    #[inline]
    pub fn trim_start(&self) -> Self {
        self.do_sub_with(|str, wrapper| wrapper(str.trim_start()))
    }

    #[inline]
    pub fn trim_start_into(self) -> Self {
        self.do_sub_into(|str| str.trim_start())
    }

    /// Returns a [FastString] with leading whitespace removed.
    ///
    /// 'Whitespace' is defined according to the terms of the Unicode Derived
    /// Core Property `White_Space`.
    ///
    /// # Text directionality
    ///
    /// A string is a sequence of bytes. 'Left' in this context means the first
    /// position of that byte string; for a language like Arabic or Hebrew
    /// which are 'right to left' rather than 'left to right', this will be
    /// the _right_ side, not the left.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let s = FastString::from(" Hello\tworld\t");
    ///
    /// assert_eq!("Hello\tworld\t", s.trim_left());
    /// ```
    #[inline]
    pub fn trim_end(&self) -> Self {
        self.do_sub_with(|str, wrapper| wrapper(str.trim_end()))
    }

    #[inline]
    pub fn trim_end_into(self) -> Self {
        self.do_sub_into(|str| str.trim_end())
    }

    /// An iterator over the disjoint matches of a pattern within the given [FastString].
    ///
    /// The `pattern` can be a `&str`, `char`, a slice of `char`s, or a
    /// function or closure that determines if a character matches.
    ///
    /// [`rmatches`]: str::matches
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let v: Vec<&str> = FastString::from("abcXXXabcYYYabc").matches("abc").collect();
    /// //["abc", "abc", "abc"];
    ///
    /// let v: Vec<&str> = "1abc2abc3".matches(char::is_numeric).collect();
    /// assert_eq!(v, ["1", "2", "3"]);
    /// ```
    pub fn matches<'a, P: Pattern<'a> + 'a>(
        &'a self,
        pat: P,
    ) -> impl Iterator<Item = FastString> + 'a {
        self.do_sub_with(move |str, wrapper| {
            SearcherIterator::new(MatchesInternal::<P>::new(pat.into_searcher(str))).map(wrapper)
        })
    }

    /// An iterator over the disjoint matches of a pattern within this [FastString]
    /// as well as the index that the match starts at.
    ///
    /// For matches of `pat` within `self` that overlap, only the indices
    /// corresponding to the first match are returned.
    ///
    /// The `pattern` can be a `&str`, `char`, a slice of `char`s, or a
    /// function or closure that determines if a character matches.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let v: Vec<_> = FastString::from("abcXXXabcYYYabc").match_indices("abc").collect();
    /// //[(0, "abc"), (6, "abc"), (12, "abc")];
    /// ```
    pub fn match_indices<'a, P: Pattern<'a> + 'a>(
        &'a self,
        pat: P,
    ) -> impl Iterator<Item = (usize, FastString)> + 'a {
        self.do_sub_with(move |str, wrapper| {
            SearcherIterator::new(MatchIndicesInternal::<P>::new(pat.into_searcher(str)))
                .map(move |(i, str)| (i, wrapper(str)))
        })
    }

    /// An iterator over the disjoint matches of a pattern within this [FastString],
    /// yielded in reverse order.
    ///
    /// The `pattern` can be a `&str`, `char`, a slice of `char`s, or a
    /// function or closure that determines if a character matches.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let v: Vec<&str> = FastString::from("abcXXXabcYYYabc").rmatches("abc").collect();
    /// //["abc", "abc", "abc"];
    /// ```
    pub fn rmatches<'a, P: Pattern<'a> + 'a>(
        &'a self,
        pat: P,
    ) -> impl Iterator<Item = FastString> + 'a
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        self.do_sub_with(move |str, wrapper| {
            SearcherIteratorRev::new(MatchesInternal::<P>::new(pat.into_searcher(str))).map(wrapper)
        })
    }

    /// An iterator over the disjoint matches of a pattern within `self`,
    /// yielded in reverse order along with the index of the match.
    ///
    /// For matches of `pat` within `self` that overlap, only the indices
    /// corresponding to the last match are returned.
    ///
    /// The `pattern` can be a `&str`, `char`, a slice of `char`s, or a
    /// function or closure that determines if a character matches.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let v: Vec<_> = FastString::from("abcXXXabcYYYabc").rmatch_indices("abc").collect();
    /// // [(12, "abc"), (6, "abc"), (0, "abc")];
    /// ```
    pub fn rmatch_indices<'a, P: Pattern<'a> + 'a>(
        &'a self,
        pat: P,
    ) -> impl Iterator<Item = (usize, FastString)> + 'a
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        self.do_sub_with(move |str, wrapper| {
            SearcherIteratorRev::new(MatchIndicesInternal::<P>::new(pat.into_searcher(str)))
                .map(move |(i, str)| (i, wrapper(str)))
        })
    }

    /// Replaces all matches of a pattern with another string.
    ///
    /// `replace` creates a new [FastString], and copies the data from this string slice into it.
    /// While doing so, it attempts to find matches of a pattern. If it finds any, it
    /// replaces them with the replacement string slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let s = FastString::from("this is old");
    ///
    /// assert_eq!("this is new", s.replace("old", "new"));
    /// assert_eq!("than an old", s.replace("is", "an"));
    /// ```
    ///
    /// When the pattern doesn't match:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let s = FastString::from("this is old");
    /// assert_eq!(s, s.replace("cookie monster", "little lamb"));
    /// ```
    pub fn replace<'a, P: Pattern<'a> + 'a, To: AsRef<str>>(
        &'a self,
        from: P,
        to: To,
    ) -> FastString {
        let mut result = String::with_capacity(32);
        let mut last_end = 0;
        let to = to.as_ref();
        let str = self.as_str();
        for (start, part) in
            SearcherIterator::new(MatchIndicesInternal::<P>::new(from.into_searcher(str)))
        {
            result.push_str(unsafe { str.get_unchecked(last_end..start) });
            result.push_str(to);
            last_end = start + part.len();
        }
        result.push_str(unsafe { str.get_unchecked(last_end..str.len()) });
        result.into()
    }

    /// Replaces first N matches of a pattern with another string.
    ///
    /// `replacen` creates a new [FastString], and copies the data from this string slice into it.
    /// While doing so, it attempts to find matches of a pattern. If it finds any, it
    /// replaces them with the replacement string slice at most `count` times.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let s = FastString::from("foo foo 123 foo");
    /// assert_eq!("new new 123 foo", s.replacen("foo", "new", 2));
    /// assert_eq!("faa fao 123 foo", s.replacen('o', "a", 3));
    /// assert_eq!("foo foo new23 foo", s.replacen(char::is_numeric, "new", 1));
    /// ```
    ///
    /// When the pattern doesn't match:
    ///
    /// ```
    /// use fast_str::FastString;
    /// let s = FastString::from("this is old");
    /// assert_eq!(s, s.replacen("cookie monster", "little lamb", 10));
    /// ```
    pub fn replacen<'a, P: Pattern<'a> + 'a, To: AsRef<str>>(
        &'a self,
        from: P,
        to: To,
        count: usize,
    ) -> FastString {
        let mut result = String::with_capacity(32);
        let mut last_end = 0;
        let to = to.as_ref();
        let str = self.as_str();
        for (start, part) in
            SearcherIterator::new(MatchIndicesInternal::<P>::new(from.into_searcher(str)))
                .take(count)
        {
            result.push_str(unsafe { str.get_unchecked(last_end..start) });
            result.push_str(to);
            last_end = start + part.len();
        }
        result.push_str(unsafe { str.get_unchecked(last_end..str.len()) });
        result.into()
    }

    /// An iterator over substrings of this string slice, separated by
    /// characters matched by a pattern.
    pub fn split<'a, P: Pattern<'a> + 'a>(
        &'a self,
        pat: P,
    ) -> impl Iterator<Item = FastString> + 'a {
        self.do_sub_with(move |str, wrapper| {
            SearcherIterator::new(SplitInternal::<P> {
                start: 0,
                end: str.len(),
                matcher: pat.into_searcher(str),
                allow_trailing_empty: true,
                finished: false,
            })
            .map(wrapper)
        })
    }

    pub fn splitn<'a, P: Pattern<'a> + 'a>(
        &'a self,
        n: usize,
        pat: P,
    ) -> impl Iterator<Item = FastString> + 'a {
        self.do_sub_with(move |str, wrapper| {
            SearcherIterator::new(SplitNInternal::<P> {
                iter: SplitInternal {
                    start: 0,
                    end: str.len(),
                    matcher: pat.into_searcher(str),
                    allow_trailing_empty: true,
                    finished: false,
                },
                count: n,
            })
            .map(wrapper)
        })
    }

    pub fn split_terminator<'a, P: Pattern<'a> + 'a>(
        &'a self,
        pat: P,
    ) -> impl Iterator<Item = FastString> + 'a {
        self.do_sub_with(move |str, wrapper| {
            SearcherIterator::new(SplitInternal::<P> {
                start: 0,
                end: str.len(),
                matcher: pat.into_searcher(str),
                allow_trailing_empty: false,
                finished: false,
            })
            .map(wrapper)
        })
    }

    /// An iterator over substrings of this [FastString], separated by
    /// characters matched by a pattern. Differs from the iterator produced by
    /// `split` in that `split_inclusive` leaves the matched part as the
    /// terminator of the substring.
    pub fn split_inclusive<'a, P: Pattern<'a> + 'a>(
        &'a self,
        pat: P,
    ) -> impl Iterator<Item = FastString> + 'a {
        self.do_sub_with(move |str, wrapper| {
            SearcherIterator::new(SplitInclusiveInternal::<P>(SplitInternal {
                start: 0,
                end: str.len(),
                matcher: pat.into_searcher(str),
                allow_trailing_empty: false,
                finished: false,
            }))
            .map(wrapper)
        })
    }

    pub fn split_whitespace<'a>(&'a self) -> impl Iterator<Item = FastString> + 'a {
        self.split(char::is_whitespace)
            .filter(|str| !str.is_empty())
    }

    pub fn split_ascii_whitespace<'a>(&'a self) -> impl Iterator<Item = FastString> + 'a {
        self.do_sub_with(move |str, wrapper| {
            str.as_bytes()
                .split(u8::is_ascii_whitespace)
                .filter(|bytes| !bytes.is_empty())
                .map(move |bytes| wrapper(unsafe { std::str::from_utf8_unchecked(bytes) }))
        })
    }

    pub fn split_once<'a, P: Pattern<'a>>(
        &'a self,
        delimiter: P,
    ) -> Option<(FastString, FastString)> {
        self.do_sub_with(move |str, wrapper| {
            let (start, end) = delimiter.into_searcher(str).next_match()?;
            // SAFETY: `Searcher` is known to return valid indices.
            unsafe {
                Some((
                    wrapper(str.get_unchecked(..start)),
                    wrapper(str.get_unchecked(end..)),
                ))
            }
        })
    }

    pub fn split_at(&self, mid: usize) -> (FastString, FastString) {
        self.do_sub_with(move |str, wrapper| {
            // is_char_boundary checks that the index is in [0, .len()]
            if str.is_char_boundary(mid) {
                // SAFETY: just checked that `mid` is on a char boundary.
                unsafe {
                    (
                        wrapper(str.get_unchecked(0..mid)),
                        wrapper(str.get_unchecked(mid..str.len())),
                    )
                }
            } else {
                panic!("failed to slice string");
            }
        })
    }

    pub fn rsplit<'a, P: Pattern<'a> + 'a>(
        &'a self,
        pat: P,
    ) -> impl Iterator<Item = FastString> + 'a
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        self.do_sub_with(move |str, wrapper| {
            SearcherIteratorRev::new(SplitInternal::<P> {
                start: 0,
                end: str.len(),
                matcher: pat.into_searcher(str),
                allow_trailing_empty: true,
                finished: false,
            })
            .map(wrapper)
        })
    }

    pub fn rsplitn<'a, P: Pattern<'a> + 'a>(
        &'a self,
        n: usize,
        pat: P,
    ) -> impl Iterator<Item = FastString> + 'a
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        self.do_sub_with(move |str, wrapper| {
            SearcherIteratorRev::new(SplitNInternal::<P> {
                iter: SplitInternal {
                    start: 0,
                    end: str.len(),
                    matcher: pat.into_searcher(str),
                    allow_trailing_empty: true,
                    finished: false,
                },
                count: n,
            })
            .map(wrapper)
        })
    }

    pub fn rsplit_terminator<'a, P: Pattern<'a> + 'a>(
        &'a self,
        pat: P,
    ) -> impl Iterator<Item = FastString> + 'a
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        self.do_sub_with(move |str, wrapper| {
            SearcherIteratorRev::new(SplitInternal::<P> {
                start: 0,
                end: str.len(),
                matcher: pat.into_searcher(str),
                allow_trailing_empty: false,
                finished: false,
            })
            .map(wrapper)
        })
    }

    pub fn rsplit_once<'a, P: Pattern<'a>>(
        &'a self,
        delimiter: P,
    ) -> Option<(FastString, FastString)>
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        self.do_sub_with(move |str, wrapper| {
            let (start, end) = delimiter.into_searcher(str).next_match_back()?;
            // SAFETY: `Searcher` is known to return valid indices.
            unsafe {
                Some((
                    wrapper(str.get_unchecked(..start)),
                    wrapper(str.get_unchecked(end..)),
                ))
            }
        })
    }

    /// Returns a [FastString] with the prefix removed.
    ///
    /// If the string starts with the pattern `prefix`, returns substring after the prefix, wrapped
    /// in `Some`.  Unlike `trim_start_matches`, this method removes the prefix exactly once.
    ///
    /// If the string does not start with `prefix`, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_str::FastString;
    /// assert_eq!(FastString::from("foo:bar").strip_prefix("foo:"), Some(FastString("bar")));
    /// assert_eq!(FastString::from("foo:bar").strip_prefix("bar"), None);
    /// assert_eq!(FastString::from("foofoo").strip_prefix("foo"), Some(FastString("foo")));
    /// ```
    pub fn strip_prefix<'a, P: Pattern<'a>>(&'a self, prefix: P) -> Option<FastString> {
        self.do_sub_with(|str, wrapper| prefix.strip_prefix_of(str).map(wrapper))
    }

    /// Returns a [FastString] with the suffix removed.
    ///
    /// If the string ends with the pattern `suffix`, returns the substring before the suffix,
    /// wrapped in `Some`.  Unlike `trim_end_matches`, this method removes the suffix exactly once.
    ///
    /// If the string does not end with `suffix`, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_str::FastString;
    /// assert_eq!(FastString::from("bar:foo").strip_suffix(":foo"), Some(FastString::from("bar")));
    /// assert_eq!(FastString::from("bar:foo").strip_suffix("bar"), None);
    /// assert_eq!(FastString::from("foofoo").strip_suffix("foo"), Some(FastString::from("foo")));
    /// ```
    pub fn strip_suffix<'a, P: Pattern<'a>>(&'a self, suffix: P) -> Option<FastString>
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        self.do_sub_with(|str, wrapper| suffix.strip_suffix_of(str).map(wrapper))
    }
}

static FASTSTR_DEFAULT: FastString = FastString::new();

impl Default for FastString {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl Default for &FastString {
    #[inline]
    fn default() -> Self {
        &FASTSTR_DEFAULT
    }
}

impl Deref for FastString {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl Borrow<str> for FastString {
    #[inline]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<str> for FastString {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<[u8]> for FastString {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_str().as_ref()
    }
}

impl Hash for FastString {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

impl Eq for FastString {}

impl PartialEq for FastString {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        PartialEq::eq(self, other.as_str())
    }
}

impl PartialEq<&FastString> for FastString {
    #[inline]
    fn eq(&self, other: &&FastString) -> bool {
        PartialEq::eq(self, *other)
    }
}

impl PartialEq<str> for FastString {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        let this = self.as_str();
        std::ptr::eq(std::ptr::addr_of!(*this), std::ptr::addr_of!(*other))
            || PartialEq::eq(this, other)
    }
}

impl PartialEq<FastString> for str {
    #[inline]
    fn eq(&self, other: &FastString) -> bool {
        PartialEq::eq(other, self)
    }
}

impl PartialEq<&str> for FastString {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        PartialEq::eq(self, *other)
    }
}

impl PartialEq<FastString> for &str {
    #[inline]
    fn eq(&self, other: &FastString) -> bool {
        PartialEq::eq(other, *self)
    }
}

impl PartialEq<&FastString> for str {
    #[inline]
    fn eq(&self, other: &&FastString) -> bool {
        PartialEq::eq(*other, self)
    }
}

impl PartialEq<String> for FastString {
    #[inline]
    fn eq(&self, other: &String) -> bool {
        PartialEq::eq(self.as_str(), other.as_str())
    }
}

impl PartialEq<FastString> for String {
    #[inline]
    fn eq(&self, other: &FastString) -> bool {
        PartialEq::eq(other, self)
    }
}

impl PartialEq<&String> for FastString {
    #[inline]
    fn eq(&self, other: &&String) -> bool {
        PartialEq::eq(self.as_str(), other.as_str())
    }
}

impl PartialEq<FastString> for &String {
    #[inline]
    fn eq(&self, other: &FastString) -> bool {
        PartialEq::eq(other, self)
    }
}

impl Ord for FastString {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let str1 = self.as_str();
        let str2 = other.as_str();
        if std::ptr::eq(std::ptr::addr_of!(*str1), std::ptr::addr_of!(*str2)) {
            return std::cmp::Ordering::Equal;
        }
        Ord::cmp(str1, str2)
    }
}

impl PartialOrd for FastString {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(self, other.as_str())
    }
}

impl PartialOrd<&FastString> for FastString {
    #[inline]
    fn partial_cmp(&self, other: &&FastString) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(self, *other)
    }
}

impl PartialOrd<str> for FastString {
    #[inline]
    fn partial_cmp(&self, other: &str) -> Option<std::cmp::Ordering> {
        let str1 = self.as_str();
        let str2 = other;
        if std::ptr::eq(std::ptr::addr_of!(*str1), std::ptr::addr_of!(*str2)) {
            return Some(std::cmp::Ordering::Equal);
        }
        PartialOrd::partial_cmp(self.as_str(), other)
    }
}

impl PartialOrd<FastString> for str {
    #[inline]
    fn partial_cmp(&self, other: &FastString) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(other, self)
    }
}

impl PartialOrd<&str> for FastString {
    #[inline]
    fn partial_cmp(&self, other: &&str) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_str(), *other)
    }
}

impl PartialOrd<&FastString> for str {
    #[inline]
    fn partial_cmp(&self, other: &&FastString) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(*other, self)
    }
}

impl PartialOrd<FastString> for &str {
    #[inline]
    fn partial_cmp(&self, other: &FastString) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(other, *self)
    }
}

impl PartialOrd<String> for FastString {
    #[inline]
    fn partial_cmp(&self, other: &String) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_str(), other.as_str())
    }
}

impl PartialOrd<FastString> for String {
    #[inline]
    fn partial_cmp(&self, other: &FastString) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(other, self)
    }
}

impl PartialOrd<&String> for FastString {
    #[inline]
    fn partial_cmp(&self, other: &&String) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_str(), other.as_str())
    }
}

impl PartialOrd<FastString> for &String {
    #[inline]
    fn partial_cmp(&self, other: &FastString) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(other, *self)
    }
}

impl Debug for FastString {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self.as_str(), f)
    }
}

impl Display for FastString {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self.as_str(), f)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for FastString {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serde::Serialize::serialize(self.as_str(), serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for FastString {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let result = <String as serde::Deserialize>::deserialize(deserializer);

        match result {
            Ok(ok) => Ok(Self::from_string(ok)),
            Err(err) => Err(err),
        }
    }
}

impl FromStr for FastString {
    type Err = <String as FromStr>::Err;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let result = FromStr::from_str(s);
        match result {
            Ok(ok) => Ok(Self::from_string(ok)),
            Err(err) => Err(err),
        }
    }
}

impl From<&&str> for FastString {
    #[inline]
    fn from(str: &&str) -> Self {
        Self::from_ref(*str)
    }
}

impl From<&'static str> for FastString {
    #[inline]
    fn from(str: &'static str) -> Self {
        Self::from_static(str)
    }
}

impl From<Rc<str>> for FastString {
    #[inline]
    fn from(str: Rc<str>) -> Self {
        Self::from_ref(str.as_ref())
    }
}

impl From<Arc<str>> for FastString {
    #[inline]
    fn from(str: Arc<str>) -> Self {
        Self::from_ref(str.as_ref())
    }
}

impl From<Box<str>> for FastString {
    #[inline]
    fn from(str: Box<str>) -> Self {
        Self::from_string(str.into())
    }
}

impl From<String> for FastString {
    #[inline]
    fn from(str: String) -> Self {
        Self::from_string(str)
    }
}

impl From<&String> for FastString {
    #[inline]
    fn from(str: &String) -> Self {
        Self::from_ref(str)
    }
}

impl From<&FastString> for FastString {
    #[inline]
    fn from(str: &FastString) -> Self {
        str.clone()
    }
}

impl From<Cow<'static, str>> for FastString {
    #[inline]
    fn from(str: Cow<'static, str>) -> Self {
        Self::from_string(str.into_owned())
    }
}

impl From<&Cow<'static, str>> for FastString {
    #[inline]
    fn from(str: &Cow<'static, str>) -> Self {
        Self::from_ref(str.as_ref())
    }
}

impl From<Cow<'static, String>> for FastString {
    #[inline]
    fn from(str: Cow<'static, String>) -> Self {
        Self::from_string(str.into_owned())
    }
}

impl From<&Cow<'static, String>> for FastString {
    #[inline]
    fn from(str: &Cow<'static, String>) -> Self {
        Self::from_ref(str.as_ref())
    }
}

impl From<FastString> for String {
    #[inline]
    fn from(str: FastString) -> Self {
        str.into_string()
    }
}

impl From<FastString> for Box<str> {
    #[inline]
    fn from(str: FastString) -> Self {
        str.as_str().into()
    }
}

impl From<FastString> for Rc<str> {
    #[inline]
    fn from(str: FastString) -> Self {
        str.as_str().into()
    }
}

impl From<FastString> for Arc<str> {
    #[inline]
    fn from(str: FastString) -> Self {
        str.as_str().into()
    }
}

impl<'a> From<FastString> for Cow<'a, str> {
    #[inline]
    fn from(str: FastString) -> Self {
        Cow::from(String::from(str))
    }
}

impl From<&FastString> for String {
    #[inline]
    fn from(str: &FastString) -> Self {
        str.as_str().into()
    }
}

impl<'a> From<&'a FastString> for &'a str {
    #[inline]
    fn from(str: &'a FastString) -> Self {
        str.as_str()
    }
}

impl<'a> From<&'a FastString> for Cow<'a, str> {
    #[inline]
    fn from(str: &'a FastString) -> Self {
        Cow::from(str.as_str())
    }
}

#[cfg(target_arch = "wasm32")]
impl From<js_sys::JsString> for FastString {
    #[inline]
    fn from(str: js_sys::JsString) -> Self {
        Self::from_string(String::from(str))
    }
}

#[cfg(target_arch = "wasm32")]
impl From<&js_sys::JsString> for FastString {
    #[inline]
    fn from(str: &js_sys::JsString) -> Self {
        Self::from_string(String::from(str))
    }
}

#[cfg(target_arch = "wasm32")]
impl From<FastString> for js_sys::JsString {
    #[inline]
    fn from(str: FastString) -> Self {
        js_sys::JsString::from(str.as_str())
    }
}

#[cfg(target_arch = "wasm32")]
impl From<&FastString> for js_sys::JsString {
    #[inline]
    fn from(str: &FastString) -> Self {
        js_sys::JsString::from(str.as_str())
    }
}

#[cfg(target_arch = "wasm32")]
impl From<FastString> for wasm_bindgen::JsValue {
    #[inline]
    fn from(str: FastString) -> Self {
        wasm_bindgen::JsValue::from_str(str.as_str())
    }
}

#[cfg(target_arch = "wasm32")]
impl From<&FastString> for wasm_bindgen::JsValue {
    #[inline]
    fn from(str: &FastString) -> Self {
        wasm_bindgen::JsValue::from_str(str.as_str())
    }
}

impl<A> FromIterator<A> for FastString
where
    String: FromIterator<A>,
{
    #[inline]
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        Self::from_string(String::from_iter(iter))
    }
}

impl FromIterator<FastString> for FastString {
    fn from_iter<T: IntoIterator<Item = FastString>>(iter: T) -> Self {
        let mut buf = String::new();
        for s in iter.into_iter() {
            buf += s.borrow();
        }
        Self::from(buf)
    }
}

impl<'a> FromIterator<&'a FastString> for FastString {
    fn from_iter<T: IntoIterator<Item = &'a FastString>>(iter: T) -> Self {
        Self::from_string(String::from_iter(iter.into_iter().map(|s| s.as_str())))
    }
}

impl Add<&str> for FastString {
    type Output = FastString;

    #[inline]
    fn add(self, rhs: &str) -> Self::Output {
        Self::from_string(String::from(self) + rhs)
    }
}

impl Add<&FastString> for FastString {
    type Output = FastString;

    #[inline]
    fn add(self, rhs: &FastString) -> Self::Output {
        Self::from_string(String::from(self) + rhs.as_str())
    }
}

impl Add<FastString> for FastString {
    type Output = FastString;

    #[inline]
    fn add(self, rhs: FastString) -> Self::Output {
        Self::from_string(String::from(self) + rhs.as_str())
    }
}

impl Add<String> for FastString {
    type Output = FastString;

    #[inline]
    fn add(self, rhs: String) -> Self::Output {
        Self::from_string(String::from(self) + rhs.as_str())
    }
}

impl Add<&String> for FastString {
    type Output = FastString;

    #[inline]
    fn add(self, rhs: &String) -> Self::Output {
        Self::from_string(String::from(self) + rhs.as_str())
    }
}

#[cfg(target_arch = "wasm32")]
impl wasm_bindgen::describe::WasmDescribe for FastString {
    #[inline]
    fn describe() {
        <String as wasm_bindgen::describe::WasmDescribe>::describe()
    }
}

#[cfg(target_arch = "wasm32")]
impl wasm_bindgen::convert::FromWasmAbi for FastString {
    type Abi = <String as wasm_bindgen::convert::FromWasmAbi>::Abi;

    #[inline]
    unsafe fn from_abi(js: Self::Abi) -> Self {
        Self::from(<String as wasm_bindgen::convert::FromWasmAbi>::from_abi(js))
    }
}

#[cfg(target_arch = "wasm32")]
impl wasm_bindgen::convert::IntoWasmAbi for FastString {
    type Abi = <&'static str as wasm_bindgen::convert::IntoWasmAbi>::Abi;

    #[inline]
    fn into_abi(self) -> Self::Abi {
        <&'static str as wasm_bindgen::convert::IntoWasmAbi>::into_abi(unsafe {
            &*std::ptr::addr_of!(*self.as_str())
        })
    }
}

#[cfg(target_arch = "wasm32")]
impl wasm_bindgen::convert::IntoWasmAbi for &FastString {
    type Abi = <&'static str as wasm_bindgen::convert::IntoWasmAbi>::Abi;

    #[inline]
    fn into_abi(self) -> Self::Abi {
        <&'static str as wasm_bindgen::convert::IntoWasmAbi>::into_abi(unsafe {
            &*std::ptr::addr_of!(*self.as_str())
        })
    }
}

#[cfg(target_arch = "wasm32")]
impl wasm_bindgen::convert::OptionFromWasmAbi for FastString {
    #[inline]
    fn is_none(abi: &Self::Abi) -> bool {
        <String as wasm_bindgen::convert::OptionFromWasmAbi>::is_none(abi)
    }
}

#[cfg(target_arch = "wasm32")]
impl wasm_bindgen::convert::OptionIntoWasmAbi for FastString {
    #[inline]
    fn none() -> Self::Abi {
        <&'static str as wasm_bindgen::convert::OptionIntoWasmAbi>::none()
    }
}

#[cfg(feature = "actix")]
impl actix_web::Responder for FastString {
    type Body = <String as actix_web::Responder>::Body;

    #[inline]
    fn respond_to(self, req: &actix_web::HttpRequest) -> actix_web::HttpResponse<Self::Body> {
        <String as actix_web::Responder>::respond_to(self.into(), req)
    }
}

#[cfg(feature = "actix")]
impl actix_web::Responder for &FastString {
    type Body = <String as actix_web::Responder>::Body;

    #[inline]
    fn respond_to(self, req: &actix_web::HttpRequest) -> actix_web::HttpResponse<Self::Body> {
        <String as actix_web::Responder>::respond_to(self.into(), req)
    }
}

#[cfg(feature = "rocket")]
impl<'r> rocket::response::Responder<'r> for FastString {
    fn respond_to(self, request: &rocket::Request) -> rocket::response::Result<'r> {
        if self.is_static() {
            let str = unsafe { &*std::ptr::addr_of!(*self.as_str()) };
            <&'static str as rocket::response::Responder<'r>>::respond_to(str, request)
        } else {
            let str: String = self.into();
            <String as rocket::response::Responder<'r>>::respond_to(str, request)
        }
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for FastString {
    #[inline]
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        <String as arbitrary::Arbitrary<'a>>::arbitrary(u).map(Self::from)
    }

    #[inline]
    fn arbitrary_take_rest(u: arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        <String as arbitrary::Arbitrary<'a>>::arbitrary_take_rest(u).map(Self::from)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <String as arbitrary::Arbitrary<'a>>::size_hint(depth)
    }
}

impl<'a> Pattern<'a> for &'a FastString {
    type Searcher = <&'a str as Pattern<'a>>::Searcher;

    fn into_searcher(self, haystack: &'a str) -> Self::Searcher {
        <&'a str as Pattern<'a>>::into_searcher(self.as_str(), haystack)
    }
}

pub struct FaststrSearch<'a, 'b> {
    _str: Box<FastString>,
    searcher: StrSearcher<'a, 'b>,
}

unsafe impl<'a, 'b> Searcher<'a> for FaststrSearch<'a, 'b> {
    #[inline]
    fn haystack(&self) -> &'a str {
        self.searcher.haystack()
    }

    #[inline]
    fn next(&mut self) -> SearchStep {
        self.searcher.next()
    }
}

impl<'a> Pattern<'a> for FastString {
    type Searcher = FaststrSearch<'a, 'a>;

    fn into_searcher(self, haystack: &'a str) -> Self::Searcher {
        let _str = Box::new(self);
        let searcher = <&'a str as Pattern<'a>>::into_searcher(
            unsafe { &*std::ptr::addr_of!(*_str.as_str()) },
            haystack,
        );
        FaststrSearch { _str, searcher }
    }
}
