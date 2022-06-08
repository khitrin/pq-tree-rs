#[derive(Debug, Copy, Clone)]
pub(crate) enum Rel {
    Root,
    P(ChildOfP),
    LQ(LeftChildOfQ),
    RQ(RightChildOfQ),
    IQ(InteriorChildOfQ),
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct ChildOfP {
    pub(crate) parent: usize,
    pub(crate) next: usize,
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct LeftChildOfQ {
    pub(crate) parent: usize,
    pub(crate) right: usize,
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct RightChildOfQ {
    pub(crate) parent: usize,
    pub(crate) left: usize,
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct InteriorChildOfQ {
    pub(crate) parent_of_unblocked: usize,
    pub(crate) left: usize,
    pub(crate) right: usize,
}

impl RightChildOfQ {
    #[must_use]
    pub(crate) fn to_iq(&self, right: usize) -> Rel {
        Rel::IQ(InteriorChildOfQ { parent_of_unblocked: self.parent, left: self.left, right })
    }
}

impl LeftChildOfQ {
    #[must_use]
    pub(crate) fn to_iq(&self, left: usize) -> Rel {
        Rel::IQ(InteriorChildOfQ { parent_of_unblocked: self.parent, left, right: self.right })
    }
}

#[allow(dead_code)]
impl Rel {
    pub(crate) fn as_p(&self) -> &ChildOfP {
        if let Rel::P(p) = self {
            p
        } else {
            panic!("Not P: {:?}", self);
        }
    }

    pub(crate) fn as_mut_p(&mut self) -> &mut ChildOfP {
        if let Rel::P(p) = self {
            p
        } else {
            panic!("Not P: {:?}", self);
        }
    }

    pub(crate) fn as_lq(&self) -> &LeftChildOfQ {
        if let Rel::LQ(lq) = self {
            lq
        } else {
            panic!("Not LQ: {:?}", self);
        }
    }

    pub(crate) fn as_mut_lq(&mut self) -> &mut LeftChildOfQ {
        if let Rel::LQ(lq) = self {
            lq
        } else {
            panic!("Not LQ: {:?}", self);
        }
    }

    pub(crate) fn as_rq(&self) -> &RightChildOfQ {
        if let Rel::RQ(rq) = self {
            rq
        } else {
            panic!("Not RQ: {:?}", self);
        }
    }

    pub(crate) fn as_mut_rq(&mut self) -> &mut RightChildOfQ {
        if let Rel::RQ(rq) = self {
            rq
        } else {
            panic!("Not RQ: {:?}", self);
        }
    }

    pub(crate) fn as_iq(&self) -> &InteriorChildOfQ {
        if let Rel::IQ(iq) = self {
            iq
        } else {
            panic!("Not IQ: {:?}", self);
        }
    }

    pub(crate) fn as_mut_iq(&mut self) -> &mut InteriorChildOfQ {
        if let Rel::IQ(iq) = self {
            iq
        } else {
            panic!("Not IQ: {:?}", self);
        }
    }

    pub(crate) fn mut_left(&mut self) -> &mut usize {
        match self {
            Rel::RQ(RightChildOfQ { left, .. }) => left,
            Rel::IQ(InteriorChildOfQ { left, .. }) => left,
            _ => panic!("Not RQ or IQ: {:?}", self),
        }
    }

    pub(crate) fn mut_right(&mut self) -> &mut usize {
        match self {
            Rel::LQ(LeftChildOfQ { right, .. }) => right,
            Rel::IQ(InteriorChildOfQ { right, .. }) => right,
            _ => panic!("Not LQ or IQ: {:?}", self),
        }
    }

    pub(crate) fn left(&self) -> usize {
        *match self {
            Rel::RQ(RightChildOfQ { left, .. }) => left,
            Rel::IQ(InteriorChildOfQ { left, .. }) => left,
            _ => panic!("Not RQ or IQ: {:?}", self),
        }
    }

    pub(crate) fn right(&self) -> usize {
        *match self {
            Rel::LQ(LeftChildOfQ { right, .. }) => right,
            Rel::IQ(InteriorChildOfQ { right, .. }) => right,
            _ => panic!("Not LQ or IQ: {:?}", self),
        }
    }

    pub(crate) fn next(&self) -> usize {
        *match self {
            Rel::P(ChildOfP { next, .. }) => next,
            _ => panic!("Not P: {:?}", self),
        }
    }
}
