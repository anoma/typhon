use super::proto::{Ballot, HPaxos1a, HPaxos1b, HPaxos2a};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum HPaxosMessage {
    HPaxos1a(HPaxos1a),
    HPaxos1b(HPaxos1b),
    HPaxos2a(HPaxos2a),
}

// TODO
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
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

impl HPaxosMessage {
    // TODO
    pub fn hash(&self) -> MessageHash {
        MessageHash { hash: 0 }
    }

    // return Some(ballot_id) if the message is 1a, otherwise returns None
    pub fn is_1a(&self) -> Option<BallotId> {
        match self {
            // TODO
            HPaxosMessage::HPaxos1a(_raw) => Some(BallotId { ballot: 0 }),
            _ => None,
        }
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
}
