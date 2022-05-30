------------------------------ MODULE Narwhal -------------------------------
EXTENDS Integers, FiniteSets, Functions

-----------------------------------------------------------------------------

(* This is the specification of the Narwhal mempool *)
(* as described by *)
(* George Danezis, Eleftherios Kokoris Kogias, *)
(* Alberto Sonnino, and Alexander Spiegelman *)
(* in their paper [https://arxiv.org/abs/2105.11827]*)


-----------------------------------------------------------------------------

(* For the purposes of the formal verification, *)
(* batches and their hashes are arbitrary sets: `Batch` and `Hash`. *)
(* We use an injective hash function from Batches to hashes, called `hash`. *)

(* -------------------------------------------------------------------------------- *)
(* ATTENTION: TLC will not like this ! *)
(* For the purposes of TLC, we might have sth like *)
(* hash(x) == [ "hash" |-> x ] *)
(* -------------------------------------------------------------------------------- *)


(* Note *)
(* The treatment of single transaction is at a finer level of granularity, *)
(* i.e., the full specification that takes into account *)
(* the arrival of single transactions from the wallet/matchmakers/... *)
(* will be a _refined_ specification. *)




(* The set of batches. *)
CONSTANT Batch

(* The set of Hashes of batches. *)
CONSTANT Hash

(* The following is essentially a non-operational definition of *)
(* a unique hash function. *)
(* `CHOOSE always assigns the same value given equivalent predicates` *)
(* [https://pron.github.io/posts/tlaplus_part2] *)
(* Hopefully, this specific choice is as good as any other choice ... *)
(* ... in theory, one would have to show that any other choice works as well *)
hash == CHOOSE v : v \in Injection(Batch, Hash)



--------------------------------------------------------------------------------

(* Narwhal makes the usual assumption about Byzantine failures. *)
(* That is, besides a partially synchronous network, we have *)
(* - a total number of validators of the form N >= 3f+1 where *)
(* - at most f validators are erroneous *)
(* Moreoer,
(* - a _quorum_ is any set that contains more than 2/3-rds of all nodes *)
(* - a _weak quorum_ is a set of nodes s.t. it intersection with any quorum is non-empty *)

CONSTANT f

ASSUME f \in Int /\ F >= 1

N == 3f + 1

CONSTANT Validator

ASSUME IsFiniteSet(Validator) /\ Cardinality(S) >= N

CONSTANTS Quorum, WQuorum

ASSUME QuorumAssumptions == /\ \A Q \in Quorum :
                                /\ Q \subseteq Validator 
                                /\ Cardinality(Q) > ((2/3) * Cardinality(Validator))
                            /\ \A W \in WQuorum :
                                /\ W \subseteq Validator
                                /\ \A Q in Quorum W \cap Q # {}

CONSTANT BYZANTINE

ASSUME ByzantineAssumption == /\ BYZANTINE \subseteq Validator
                              /\ Cardinality(BYZANTINE) <= f









