## Formalizaton of Heterogeneous Paxos 2.0

This folder contains the formalization of the [Heterogeneous Paxos 2.0 algorithm](https://doi.org/10.5281/zenodo.12572557)
in TLA+.

We formally prove the Agreement property of the algorithm in TLAPS, establishing
that decisions made by entangled learners are equal.
This consistency is a key safety properry of the algorithm.

To simplify the formalization and avoid the complications of dealing with
mutually recursive definitions in TLA+, we assume that the protocol messages
explicitely convey information about their types (1a, 1b or 2a), as well as a
list of learner values for 2a-messages.
Consequently, we adjust the definition of well-formed messages to ensure that
the conveyed information is valid.

