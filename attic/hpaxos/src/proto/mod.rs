pub mod hpaxosmessage;

pub use self::hpaxosmessage::{Ballot, HPaxos1a, HPaxos1b, HPaxos2a};
use std::hash::Hash;

impl Hash for Ballot {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.bal.hash(state);
        self.value_hash.hash(state);
    }
}

impl Eq for HPaxos1a {}
impl Eq for HPaxos1b {}
impl Eq for HPaxos2a {}

impl Hash for HPaxos1a {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ballot.hash(state)
        // TODO
    }
}
impl Hash for HPaxos1b {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {
        // TODO
    }
}

impl Hash for HPaxos2a {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {
        // TODO
    }
}
