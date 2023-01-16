use super::message::{AcceptorId, BallotId, HPaxosMessage, MessageHash};
use std::cmp;
use std::collections::{HashMap, HashSet};
use unwrap_or::unwrap_some_or;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Index(u64);

impl Index {
    fn next(&self) -> Self {
        // it should never overflow, practically
        Self(self.0 + 1)
    }
}

impl Default for Index {
    fn default() -> Self {
        Self(0)
    }
}

#[derive(Debug, Clone)]
pub struct MessageInfo {
    // raw heterogeneous paxos protocol message
    msg: HPaxosMessage,

    // message ballot id
    ballot: BallotId,

    // previous message sent by the same sender
    // prev: Option<MessageHash>,

    // TODO comment
    referenced_leaves: HashMap<AcceptorId, Index>,
    branch_index: Index,
}

impl MessageInfo {
    pub fn hash(&self) -> MessageHash {
        self.msg.hash()
    }

    pub fn sender(&self) -> Option<AcceptorId> {
        self.msg.sender()
    }

    pub fn is_1a(&self) -> Option<BallotId> {
        self.msg.is_1a()
    }
}

#[derive(Debug)]
struct MessageHistoryTableComponent {
    max_index: Index,
    msg_index_map: HashMap<MessageHash, Index>,
}

impl MessageHistoryTableComponent {
    // create a new component for the given message hash
    fn new(msg_hash: MessageHash) -> Self {
        let mut comp = Self {
            max_index: Index(0),
            msg_index_map: HashMap::<MessageHash, Index>::new(),
        };
        comp.msg_index_map.insert(msg_hash, Index(0));
        comp
    }

    // returns a current maximal history branch index of the component
    fn get_index(&self) -> Index {
        self.max_index.clone()
    }

    // checks if the given message hash is a leaf of a message history branch
    fn is_leaf(&self, msg: &MessageHash) -> bool {
        self.msg_index_map.contains_key(msg)
    }

    // updates the component with a new message hash and return an index of the new message hash in the component
    fn update(&mut self, msg_hash: MessageHash, prev_msg_hash: MessageHash) -> Index {
        if self.is_leaf(&prev_msg_hash) {
            // the previous message is a leaf -- replace it with the given message
            let (_, index) = self.msg_index_map.remove_entry(&prev_msg_hash).unwrap();
            self.msg_index_map.insert(msg_hash, index.clone());
            index
        } else {
            // the previous message is not a leaf -- register a new branch and update the current
            // maximal index of the component
            let new_index = self.max_index.next();
            debug_assert!(
                !self.msg_index_map.contains_key(&msg_hash),
                "message hash exists in the component"
            );
            self.msg_index_map.insert(msg_hash, new_index.clone());
            self.max_index = new_index.clone();
            new_index
        }
    }
}

#[derive(Debug)]
struct MessageHistoryTable(HashMap<AcceptorId, MessageHistoryTableComponent>);

impl MessageHistoryTable {
    fn new() -> Self {
        MessageHistoryTable(HashMap::<AcceptorId, MessageHistoryTableComponent>::new())
    }

    // adds a new component for the given acceptor id and return an index of the given message hash in the component
    fn add_component(&mut self, acc: AcceptorId, msg_hash: MessageHash) -> Index {
        debug_assert!(
            !self.0.contains_key(&acc),
            "component for the given acceptor id already exists"
        );
        self.0
            .insert(acc.clone(), MessageHistoryTableComponent::new(msg_hash));
        self.0.get(&acc).unwrap().get_index()
    }

    // input: a well-formed (relative to the correct acceptor state) message
    // TODO improve comment
    fn update_and_get_index(
        &mut self,
        msg: &HPaxosMessage,
        prev_msg: Option<(MessageHash, AcceptorId)>,
    ) -> Index {
        // case 1a: early return a default value
        if msg.is_1a().is_some() {
            return Index::default();
        }

        // case 1b / 2a
        if let Some((prev_msg_hash, prev_msg_sender)) = prev_msg {
            // if the previous message (of the sender) exists, `msg` must be known

            // since the previous message is referenced by `msg`, it must have been processed and thus,
            // a message component for the message sender must exists
            let comp = self.0.get_mut(&prev_msg_sender).unwrap(); // cannot fail

            comp.update(msg.hash(), prev_msg_hash)
        } else {
            // if the previous message (of the sender) does not exist,
            // the message sender is not known -- create a new component
            self.add_component(msg.sender().unwrap(), msg.hash())
        }
    }
}

#[derive(Debug)]
pub struct AcceptorState {
    // processed well-formed messages
    known_msgs: HashMap<MessageHash, MessageInfo>,

    // set of senders of the processed well-formed messages
    known_acceptor_id: HashSet<AcceptorId>,

    // contains a list of most recent messages which will be included as references in the next
    // message sent by this acceptor
    // Invariant: `recent_msgs` is a subset of `known_msgs`
    recent_msgs: HashSet<MessageHash>,

    // queued message issued by the acceptor, which must be processed before any other message
    queued_msg: Option<MessageHash>,

    // stores branch leaves of 1b / 2a message history per acceptor
    message_history_table: MessageHistoryTable,

    // a set of caught acceptors
    // Invariant: `caught` is a subset of `known_acceptor_id`
    caught: HashSet<AcceptorId>,
}

pub enum MessageParseError {
    // the message references unknown messages
    UnknownRef,

    // the message contains invalid references and can be discarded
    InvalidRefs,

    // the message contains invalid sender information and can be discarded
    InvalidSender,
}

impl AcceptorState {
    pub fn new() -> AcceptorState {
        Self {
            known_msgs: HashMap::new(),
            known_acceptor_id: HashSet::new(),
            recent_msgs: HashSet::<MessageHash>::new(),
            queued_msg: None,
            message_history_table: MessageHistoryTable::new(),
            caught: HashSet::<AcceptorId>::new(),
        }
    }

    // The following is invariant:
    // Inv_0. `known_acceptor_id` contains exactly all sender ids of messages belonging to `known_msgs`.
    //
    // We say that message m is _known_ if it belongs to `known_msgs`.
    // Given message m, we say that its sender is _known_ if its id belongs to `known_acceptor_id`.
    //
    // We say that message m is _caught_ if it belongs to `caught_msgs`.
    // 1. For every known message m, either its sender is caught or there is an entry in `message_history_table`.
    // TODO formulate invariants for `message_history_table`

    // checks that every reference of the message is known
    // pub fn is_proper(&self, msg: &HPaxosMessage) -> bool {
    //     let refs = msg.refs(); // TODO return iterator
    //     refs.iter().any(|r| self.known_msgs.contains_key(r))
    // }

    pub fn is_known_sig(&self, id: &AcceptorId) -> bool {
        self.known_acceptor_id.contains(id)
    }

    // checks if the message (hash) is known
    pub fn is_known_msg(&self, hash: MessageHash) -> bool {
        self.known_msgs.get(&hash).is_some()
    }

    // checks if the acceptor is known to be caught
    fn is_caught(&self, id: &AcceptorId) -> bool {
        self.caught.get(id).is_some()
    }

    // checks if the message contains valid and known references
    // - Well-formed 1a message must not contain any references.
    // - Well-formed 1b or 2a message must reference other messages.
    //   The message passes the check if
    //   (1) it contains only references to known messages
    //   (2) if the message sender is known, the message must contain exactly one
    //       reference to a previous message of the sender.
    //
    // Property (2) implies the following property
    // (3) for the message `msg` that has passed the check, the sender of `msg` is not known
    //     iff `msg` references no messages sent by the sender.
    // "Only if". Indeed, assume that the message sender, `msg_sender`, is not known.
    // Suppose that there exists another message m1 sent by `msg_sender` and referenced by `msg`.
    // Since all the references of `msg` are known by (1), m1 is known and hence the sender of m1 is known by invariant Inv_0.
    // Contradiction.
    // "If". Assume that the list of `msg` references contains no message sent by `msg_sender`.
    // Suppose to the contrary that `msg_sender` is known.
    // From (2), there exists a previous message sent by `msg_sender` and referenced `msg`. Contradiction.
    fn check_refs(&self, msg: &HPaxosMessage) -> Result<(), MessageParseError> {
        // case 1a: return error if the 1a message contains any references
        if msg.is_1a().is_some() {
            return msg
                .refs()
                .is_empty()
                .then_some(())
                .ok_or(MessageParseError::InvalidRefs);
        }

        // case 1b / 2a
        let msg_refs = msg.refs();
        if msg_refs.is_empty() {
            return Err(MessageParseError::InvalidRefs);
        }

        // 1b / 2s message must contain a sender -- otherwise, the message is invalid
        let msg_sender = unwrap_some_or!(msg.sender(), {
            return Err(MessageParseError::InvalidSender);
        });

        // count known references originating from the same sender
        let mut num_refs_same_sender: u32 = 0;
        for ref_hash in msg_refs {
            let ref_msg = unwrap_some_or!(self.known_msgs.get(&ref_hash), {
                // the reference is unknown -- return error according to condition (1)
                return Err(MessageParseError::UnknownRef);
            });
            if ref_msg.sender() == Some(msg_sender.clone()) {
                num_refs_same_sender += 1;
            }
        }

        if !self.is_known_sig(&msg_sender) {
            // Since the message sender is not known, the message cannot reference
            // another message issued by the same sender, by the argument above.
            assert_eq!(
                num_refs_same_sender, 0,
                "the message cannot contain a known reference originating from the same sender"
            );
            Ok(())
        } else {
            // condition (2)
            (num_refs_same_sender == 1)
                .then_some(())
                .ok_or(MessageParseError::InvalidRefs)
        }
    }

    // compute ballot id of the given well-formed message
    fn compute_msg_ballot(&self, msg: &HPaxosMessage) -> BallotId {
        // assume that msg is well-formed
        debug_assert!(
            self.check_refs(msg).is_ok(),
            "the message is not well-formed"
        );

        // case 1a:      the message contains no references;
        //               max_ballot is Some initially and will not by altered since a well-formed
        //               1a message contains no references, i.e., `msg.refs()` is empty.
        // case 1b / 2a: since the message is well-formed, it must contain at least one reference;
        //               max_ballot is None initially, but will be reassigned to Some value in the loop below,
        //               since all the message references are known and every processed message is assigned a respective ballot id.
        let mut max_ballot: Option<BallotId> = msg.is_1a();

        for ref_hash in msg.refs() {
            let ref_msg = self.known_msgs.get(&ref_hash).unwrap();
            let ref_msg_bal = ref_msg.ballot.clone();
            max_ballot = Some(max_ballot.map_or_else(|| ref_msg_bal, |b| cmp::max(b, ref_msg_bal)));
        }
        max_ballot.unwrap() // should never panic
    }

    // construct joined message history leaves table for all references of the given message,
    // along with a set of caught senders of the conflicting messages
    // TODO rename if we are not interested in actual leaves, i.e., the most recent messages per each sender
    fn compute_joined_referenced_leaves_table(
        &self,
        msg: &HPaxosMessage,
    ) -> (HashMap<AcceptorId, Index>, HashSet<AcceptorId>) {
        // assume that `msg` is well-formed
        debug_assert!(
            self.check_refs(msg).is_ok(),
            "the message is not well-formed"
        );

        // 1a messages contain no references -- return empty structures
        if msg.is_1a().is_some() {
            return (HashMap::new(), HashSet::new());
        }

        let mut joined_ref_leaves_table = HashMap::<AcceptorId, Index>::new();
        let mut new_caught_acceptors = HashSet::<AcceptorId>::new();

        fn update_structures(
            joined_ref_leaves_table: &mut HashMap<AcceptorId, Index>,
            caught_acceptors: &mut HashSet<AcceptorId>,
            acc: AcceptorId,
            idx: Index,
        ) {
            if let Some(joined_leaf_index) =
                joined_ref_leaves_table.insert(acc.clone(), idx.clone())
            {
                // If the sender is already contained in the joined table,
                // check if the existing leaf index agrees with the given index idx.
                if idx != joined_leaf_index {
                    // in the case of conflict, the sender is caught
                    caught_acceptors.insert(acc.clone());
                    // remove the sender entry from the joined table
                    joined_ref_leaves_table.remove(&acc);
                }
            }
        }

        // For the given message `msg`, every message m1 referenced by `msg` is known and hence is itself a well-formed message.
        // Therefore, each m1 contains a reference to not more than one previous message m2 (of the same sender).
        // If m1 is a 1b / 2a message, it has already received an index relative to its sender.
        // Moreover, since m1 is well-formed (contains at most one reference to the sender's previous message),
        // the index of the message m1 cannot conflict with the index of the message m2.

        // join leaf tables of all the referenced messages
        for ref_hash in msg.refs() {
            let ref_msg = self.known_msgs.get(&ref_hash).unwrap();

            // 1a message does not reference any messages -- continue
            if ref_msg.is_1a().is_some() {
                continue;
            }

            // first, process the referenced message itself, if its sender is not yet caught
            let ref_sender = ref_msg.sender().unwrap(); // cannot fail
            if !self.is_caught(&ref_sender) && !new_caught_acceptors.contains(&ref_sender) {
                update_structures(
                    &mut joined_ref_leaves_table,
                    &mut new_caught_acceptors,
                    ref_sender,
                    ref_msg.branch_index.clone(),
                );
            }

            // second, process the reference leaf table of the referenced message, if its sender is not yet caught
            for (sender, idx) in ref_msg.referenced_leaves.iter() {
                if !self.is_caught(sender) && !new_caught_acceptors.contains(sender) {
                    update_structures(
                        &mut joined_ref_leaves_table,
                        &mut new_caught_acceptors,
                        sender.to_owned(),
                        idx.to_owned(),
                    );
                }
            }
        }
        (joined_ref_leaves_table, new_caught_acceptors)
    }

    // compute the previous message, i.e., a unique message referenced by the given well-formed message
    // and originating from the same sender
    // returns the previous message hash and sender id, if it exists
    // returns None if the given message is 1a message or the given message is not known
    fn sender_prev_message(&self, msg: &HPaxosMessage) -> Option<(MessageHash, AcceptorId)> {
        // assume that `msg` is well-formed
        debug_assert!(
            self.check_refs(msg).is_ok(),
            "the message is not well-formed"
        );

        // 1a message does not have a previous message -- return None
        if msg.is_1a().is_some() {
            return None;
        }

        // 1b and 2a messages must have a sender
        let msg_sender = msg.sender().unwrap(); // cannot fail

        if self.is_known_sig(&msg_sender) {
            // If the message sender is known, by property (2) of `check_refs` function,
            // the message must contain exactly one reference to a previous message sent by the sender.
            for ref_hash in msg.refs() {
                let ref_msg = self.known_msgs.get(&ref_hash).unwrap(); // cannot fail
                if let Some(sender) = ref_msg.sender() {
                    if msg_sender == sender {
                        return Some((ref_msg.hash(), sender));
                    }
                }
            }
        }

        // The message sender is not known and hence, by property (3) of `check_refs`,
        // the message does not contain a reference to the sender's previous message.
        None
    }

    pub fn store(&mut self, msg: HPaxosMessage) {
        // assume that msg is well-formed
        debug_assert!(
            self.check_refs(&msg).is_ok(),
            "the message is not well-formed"
        );

        let msg_ballot = self.compute_msg_ballot(&msg);

        let (joined_ref_leaves_table, new_caught_acceptors) =
            self.compute_joined_referenced_leaves_table(&msg);

        // record new caught acceptors
        self.caught.extend(new_caught_acceptors);

        // compute a previous message hash / sender id
        let prev_msg = self.sender_prev_message(&msg);

        // update the message history table with the new message
        let msg_branch_index = self
            .message_history_table
            .update_and_get_index(&msg, prev_msg);

        // learn the message and its sender
        self.add_to_known(MessageInfo {
            msg,
            ballot: msg_ballot,
            // prev: prev_msg.map(|p| p.0),
            referenced_leaves: joined_ref_leaves_table,
            branch_index: msg_branch_index,
        });
    }

    // adds given parsed message to the list of known messages
    fn add_to_known(&mut self, msg: MessageInfo) {
        if let Some(sender) = msg.sender() {
            self.known_acceptor_id.insert(sender);
        }
        self.known_msgs.insert(msg.hash(), msg);
    }

    pub fn add_to_recent(&mut self, msg: HPaxosMessage) {
        self.recent_msgs.insert(msg.hash());
    }

    pub fn clear_recent(&mut self) {
        self.recent_msgs.clear();
    }

    // enqueued message are always well-formed
    pub fn dequeue(&mut self) -> Option<MessageHash> {
        let hash = self.queued_msg.clone();
        self.queued_msg = None;
        hash
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_acceptor_state() {
        let s = AcceptorState::new();
        assert!(!s.is_known_msg(MessageHash { hash: 0 }));
        assert!(!s.is_caught(&AcceptorId { id: 0 }));
    }
}
