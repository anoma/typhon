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
(* a hash function. *)
(* `CHOOSE always assigns the same value given equivalent predicates` *)
(* [https://pron.github.io/posts/tlaplus_part2] *)
hash == CHOOSE v : v \in Injection(Batch, Hash)

--------------------------------------------------------------------------------





