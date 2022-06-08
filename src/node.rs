#[derive(Copy, Clone, Debug)]
pub(crate) enum Node {
    P(PNode),
    Q(QNode),
    L,
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct PNode {
    pub(crate) child: usize,
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct QNode {
    pub(crate) left: usize,
    pub(crate) right: usize,
}

#[allow(dead_code)]
impl Node {
    pub(crate) fn as_p(&self) -> &PNode {
        if let Node::P(p) = self {
            p
        } else {
            panic!("Not a P-node: {:?}!", self);
        }
    }

    pub(crate) fn as_mut_p(&mut self) -> &mut PNode {
        if let Node::P(p) = self {
            p
        } else {
            panic!("Not a P-node: {:?}!", self);
        }
    }

    pub(crate) fn as_q(&self) -> &QNode {
        if let Node::Q(q) = self {
            q
        } else {
            panic!("Not a Q-node: {:?}!", self);
        }
    }

    pub(crate) fn as_mut_q(&mut self) -> &mut QNode {
        if let Node::Q(q) = self {
            q
        } else {
            panic!("Not a Q-node: {:?}!", self);
        }
    }
}
