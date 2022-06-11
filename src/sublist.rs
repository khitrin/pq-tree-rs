#[derive(Debug)]
pub(crate) struct SubCircularList {
    first: usize,
    last: usize,
    first_cut: Option<usize>,
    len: usize,
}

impl SubCircularList {
    pub(crate) fn new() -> SubCircularList {
        SubCircularList { first: 0, last: 0, len: 0, first_cut: None }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    pub(crate) fn first(&self) -> usize {
        debug_assert_ne!(self.len, 0);
        self.first
    }

    pub(crate) fn last(&self) -> usize {
        debug_assert_ne!(self.len, 0);
        self.last
    }

    pub(crate) fn first_cut(&self) -> Option<usize> {
        debug_assert_ne!(self.len, 0);
        self.first_cut
    }

    pub(crate) fn add(&mut self, idx: usize) {
        if self.len == 0 {
            self.first = idx;
            self.last = idx;
            self.len = 1;
        } else {
            self.last = idx;
            self.len += 1;
        }
    }

    pub(crate) fn cut(&mut self) {
        debug_assert_ne!(self.len, 0);

        if self.first_cut.is_none() {
            self.first_cut = Some(self.last);
        }
    }
}
