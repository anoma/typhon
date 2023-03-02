use crate::learner::{Learner, LearnerId};
use crate::message::AcceptorId;
use std::collections::{HashMap, HashSet};

pub struct Quorum(HashSet<AcceptorId>);

#[derive(Debug)]
pub struct LearnerGraph {
    learners: HashMap<LearnerId, HashSet<AcceptorId>>,
}

impl LearnerGraph {
    pub fn get_learners(&self) -> Vec<LearnerId> {
        return self.learners.keys().cloned().collect(); // TODO return iterator?
    }

    // TODO
    pub fn is_trust_live(&self, _lr: LearnerId, _q: Quorum) -> bool {
        false
    }

    // TODO
    pub fn is_trust_safe(&self, _lr: (LearnerId, LearnerId), _q: Quorum) -> bool {
        false
    }

    #[cfg(test)]
    pub fn mock() -> Self {
        return Self {
            learners: HashMap::<LearnerId, HashSet<AcceptorId>>::default(),
        };
    }
}

#[derive(Debug)]
pub struct Configuration {
    pub learner_graph: LearnerGraph,
}

impl Configuration {
    #[cfg(test)]
    pub fn mock() -> Self {
        return Self {
            learner_graph: LearnerGraph::mock(),
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let config = Configuration {
            learner_graph: LearnerGraph::mock(),
        };
        assert!(config.learner_graph.get_learners().is_empty());
    }
}
