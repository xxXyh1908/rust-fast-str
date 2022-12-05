#![allow(unused)]
#![doc(hidden)]
use std::marker::PhantomData;
use super::pattern::{Pattern, ReverseSearcher, Searcher};

pub(super) trait SearcherIteratorInternal<'a, P: Pattern<'a>> {
    type Item;

    fn next(&mut self) -> Option<Self::Item>;
    fn next_back(&mut self) -> Option<Self::Item>
    where
        P::Searcher: ReverseSearcher<'a>;
}

pub(super) struct SearcherIterator<'a, P: Pattern<'a>, Internal: SearcherIteratorInternal<'a, P> + 'a> {
    internal: Internal,
    __marker: PhantomData<&'a P>,
}

pub(super) struct SearcherIteratorRev<'a, P: Pattern<'a>, Internal: SearcherIteratorInternal<'a, P> + 'a>
where
    P::Searcher: ReverseSearcher<'a>,
{
    internal: Internal,
    __marker: PhantomData<&'a P>,
}

impl<'a, P: Pattern<'a>, Internal: SearcherIteratorInternal<'a, P> + 'a> Iterator for SearcherIterator<'a, P, Internal> {
    type Item = Internal::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.internal.next()
    }
}

impl<'a, P: Pattern<'a>, Internal: SearcherIteratorInternal<'a, P> + 'a> Iterator for SearcherIteratorRev<'a, P, Internal>
where
    P::Searcher: ReverseSearcher<'a>,
{
    type Item = Internal::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.internal.next_back()
    }
}

impl<'a, P: Pattern<'a>, Internal: SearcherIteratorInternal<'a, P>> SearcherIterator<'a, P, Internal> {
    #[inline]
    pub fn rev(self) -> SearcherIteratorRev<'a, P, Internal>
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        SearcherIteratorRev {
            internal: self.internal,
            __marker: PhantomData,
        }
    }

    #[inline]
    pub fn new(internal: Internal) -> Self {
        Self { internal, __marker: PhantomData }
    }
}

impl<'a, P: Pattern<'a>, Internal: SearcherIteratorInternal<'a, P>> SearcherIteratorRev<'a, P, Internal>
where
    P::Searcher: ReverseSearcher<'a>,
{
    #[inline]
    pub fn rev(self) -> SearcherIterator<'a, P, Internal> {
        SearcherIterator {
            internal: self.internal,
            __marker: PhantomData,
        }
    }

    #[inline]
    pub fn new(internal: Internal) -> Self {
        Self { internal, __marker: PhantomData }
    }
}

pub(super) struct MatchIndicesInternal<'a, P: Pattern<'a>> {
    matcher: P::Searcher,
}

impl<'a, P: Pattern<'a>> MatchIndicesInternal<'a, P> {
    #[inline]
    pub fn new(matcher: P::Searcher) -> Self {
        Self { matcher }
    }
}

impl<'a, P: Pattern<'a>> SearcherIteratorInternal<'a, P> for MatchIndicesInternal<'a, P> {
    type Item = (usize, &'a str);

    fn next(&mut self) -> Option<Self::Item> {
        self.matcher
            .next_match()
            // SAFETY: `Searcher` guarantees that `start` and `end` lie on unicode boundaries.
            .map(|(start, end)| unsafe { (start, self.matcher.haystack().get_unchecked(start..end)) })
    }

    fn next_back(&mut self) -> Option<Self::Item>
    where
        <P as Pattern<'a>>::Searcher: ReverseSearcher<'a>,
    {
        self.matcher
            .next_match_back()
            // SAFETY: `Searcher` guarantees that `start` and `end` lie on unicode boundaries.
            .map(|(start, end)| unsafe { (start, self.matcher.haystack().get_unchecked(start..end)) })
    }
}

pub(super) struct MatchesInternal<'a, P: Pattern<'a>> {
    matcher: P::Searcher,
}

impl<'a, P: Pattern<'a>> MatchesInternal<'a, P> {
    #[inline]
    pub fn new(matcher: P::Searcher) -> Self {
        Self { matcher }
    }
}

impl<'a, P: Pattern<'a>> SearcherIteratorInternal<'a, P> for MatchesInternal<'a, P> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        self.matcher
            .next_match()
            // SAFETY: `Searcher` guarantees that `start` and `end` lie on unicode boundaries.
            .map(|(start, end)| unsafe { self.matcher.haystack().get_unchecked(start..end) })
    }

    fn next_back(&mut self) -> Option<Self::Item>
    where
        <P as Pattern<'a>>::Searcher: ReverseSearcher<'a>,
    {
        self.matcher
            .next_match_back()
            // SAFETY: `Searcher` guarantees that `start` and `end` lie on unicode boundaries.
            .map(|(start, end)| unsafe { self.matcher.haystack().get_unchecked(start..end) })
    }
}

pub(super) struct SplitInternal<'a, P: Pattern<'a>> {
    pub(super) start: usize,
    pub(super) end: usize,
    pub(super) matcher: P::Searcher,
    pub(super) allow_trailing_empty: bool,
    pub(super) finished: bool,
}

pub(super) struct SplitInclusiveInternal<'a, P: Pattern<'a>>(pub(super) SplitInternal<'a, P>);

impl<'a, P: Pattern<'a>> SearcherIteratorInternal<'a, P> for SplitInternal<'a, P> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.next()
    }

    #[inline]
    fn next_back(&mut self) -> Option<Self::Item>
    where
        <P as Pattern<'a>>::Searcher: ReverseSearcher<'a>,
    {
        self.next_back()
    }
}

impl<'a, P: Pattern<'a>> SearcherIteratorInternal<'a, P> for SplitInclusiveInternal<'a, P> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next_inclusive()
    }

    #[inline]
    fn next_back(&mut self) -> Option<Self::Item>
    where
        <P as Pattern<'a>>::Searcher: ReverseSearcher<'a>,
    {
        self.0.next_back_inclusive()
    }
}

impl<'a, P: Pattern<'a>> SplitInternal<'a, P> {
    #[inline]
    fn get_end(&mut self) -> Option<&'a str> {
        if !self.finished && (self.allow_trailing_empty || self.end - self.start > 0) {
            self.finished = true;
            // SAFETY: `self.start` and `self.end` always lie on unicode boundaries.
            unsafe {
                let string = self.matcher.haystack().get_unchecked(self.start..self.end);
                Some(string)
            }
        } else {
            None
        }
    }

    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        if self.finished {
            return None;
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match() {
            // SAFETY: `Searcher` guarantees that `a` and `b` lie on unicode boundaries.
            Some((a, b)) => unsafe {
                let elt = haystack.get_unchecked(self.start..a);
                self.start = b;
                Some(elt)
            },
            None => self.get_end(),
        }
    }

    #[inline]
    fn next_inclusive(&mut self) -> Option<&'a str> {
        if self.finished {
            return None;
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match() {
            // SAFETY: `Searcher` guarantees that `b` lies on unicode boundary,
            // and self.start is either the start of the original string,
            // or `b` was assigned to it, so it also lies on unicode boundary.
            Some((_, b)) => unsafe {
                let elt = haystack.get_unchecked(self.start..b);
                self.start = b;
                Some(elt)
            },
            None => self.get_end(),
        }
    }

    #[inline]
    fn next_back(&mut self) -> Option<&'a str>
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        if self.finished {
            return None;
        }

        if !self.allow_trailing_empty {
            self.allow_trailing_empty = true;
            match self.next_back() {
                Some(elt) if !elt.is_empty() => return Some(elt),
                _ => {
                    if self.finished {
                        return None;
                    }
                }
            }
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match_back() {
            // SAFETY: `Searcher` guarantees that `a` and `b` lie on unicode boundaries.
            Some((a, b)) => unsafe {
                let elt = haystack.get_unchecked(b..self.end);
                self.end = a;
                Some(elt)
            },
            // SAFETY: `self.start` and `self.end` always lie on unicode boundaries.
            None => unsafe {
                self.finished = true;
                Some(haystack.get_unchecked(self.start..self.end))
            },
        }
    }

    #[inline]
    fn next_back_inclusive(&mut self) -> Option<&'a str>
    where
        P::Searcher: ReverseSearcher<'a>,
    {
        if self.finished {
            return None;
        }

        if !self.allow_trailing_empty {
            self.allow_trailing_empty = true;
            match self.next_back_inclusive() {
                Some(elt) if !elt.is_empty() => return Some(elt),
                _ => {
                    if self.finished {
                        return None;
                    }
                }
            }
        }

        let haystack = self.matcher.haystack();
        match self.matcher.next_match_back() {
            // SAFETY: `Searcher` guarantees that `b` lies on unicode boundary,
            // and self.end is either the end of the original string,
            // or `b` was assigned to it, so it also lies on unicode boundary.
            Some((_, b)) => unsafe {
                let elt = haystack.get_unchecked(b..self.end);
                self.end = b;
                Some(elt)
            },
            // SAFETY: self.start is either the start of the original string,
            // or start of a substring that represents the part of the string that hasn't
            // iterated yet. Either way, it is guaranteed to lie on unicode boundary.
            // self.end is either the end of the original string,
            // or `b` was assigned to it, so it also lies on unicode boundary.
            None => unsafe {
                self.finished = true;
                Some(haystack.get_unchecked(self.start..self.end))
            },
        }
    }
}

pub(super) struct SplitNInternal<'a, P: Pattern<'a>> {
    pub(super) iter: SplitInternal<'a, P>,
    /// The number of splits remaining
    pub(super) count: usize,
}

impl<'a, P: Pattern<'a>> SearcherIteratorInternal<'a, P> for SplitNInternal<'a, P> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.count {
            0 => None,
            1 => {
                self.count = 0;
                self.iter.get_end()
            }
            _ => {
                self.count -= 1;
                self.iter.next()
            }
        }
    }

    #[inline]
    fn next_back(&mut self) -> Option<Self::Item>
    where
        <P as Pattern<'a>>::Searcher: ReverseSearcher<'a>,
    {
        match self.count {
            0 => None,
            1 => {
                self.count = 0;
                self.iter.get_end()
            }
            _ => {
                self.count -= 1;
                self.iter.next_back()
            }
        }
    }
}
