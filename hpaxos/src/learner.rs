#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct LearnerId(pub String);

#[derive(Debug)]
pub struct Learner {
    lid: LearnerId,
}
