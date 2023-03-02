use crate::learner::LearnerId;

use super::proto::{Ballot, HPaxos1a, HPaxos1b, HPaxos2a};

// #[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[derive(Clone, Debug)]
pub enum HPaxosMessage {
    HPaxos1a(HPaxos1a),
    HPaxos1b(HPaxos1b),
    HPaxos2a(HPaxos2a),
}

// TODO
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct MessageHash {
    pub hash: u64,
}

// TODO
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Sig {
    pub sig: u64,
}

// TODO
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AcceptorId {
    pub id: u64,
}

// TODO
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BallotId {
    pub ballot: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValueId {
    pub value: u64,
}

impl HPaxosMessage {
    // TODO
    pub fn hash(&self) -> MessageHash {
        MessageHash { hash: 0 }
    }

    // return Some(ballot_id) if the message is 1a, otherwise returns None
    pub fn is_1a(&self) -> Option<(BallotId, ValueId)> {
        match self {
            // TODO
            HPaxosMessage::HPaxos1a(_raw) => Some((BallotId { ballot: 0 }, ValueId { value: 0 })),
            _ => None,
        }
    }

    pub fn is_1b(&self) -> bool {
        matches!(self, HPaxosMessage::HPaxos1b(_raw))
    }

    pub fn is_2a(&self) -> bool {
        matches!(self, HPaxosMessage::HPaxos2a(_raw))
    }

    // TODO: implement MessageHashIter
    pub fn refs(&self) -> Vec<MessageHash> {
        // TODO return iterator
        match self {
            HPaxosMessage::HPaxos1a(_) => Vec::new(),
            HPaxosMessage::HPaxos1b(_msg) => Vec::new(), // TODO
            HPaxosMessage::HPaxos2a(_msg) => Vec::new(), // TODO
        }
    }

    pub fn sender(&self) -> Option<AcceptorId> {
        match self {
            HPaxosMessage::HPaxos1a(_) => None,
            HPaxosMessage::HPaxos1b(_msg) => None, // TODO
            HPaxosMessage::HPaxos2a(_msg) => None, // TODO
        }
    }

    pub fn value(&self) -> ValueId {
        match self {
            HPaxosMessage::HPaxos1a(_) => ValueId { value: 0 }, // TODO
            HPaxosMessage::HPaxos1b(_msg) => ValueId { value: 0 }, // TODO
            HPaxosMessage::HPaxos2a(_msg) => ValueId { value: 0 }, // TODO
        }
    }

    pub fn learner(&self) -> Option<LearnerId> {
        Some(LearnerId("fix me".to_string()))
    }

    #[cfg(test)]
    pub fn mock_1a() -> Self {
        Self::HPaxos1a(HPaxos1a {
            ballot: None,
            sig: None,
        })
    }
}
