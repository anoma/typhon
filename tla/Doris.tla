                        ---- MODULE Doris ----
(***************************************************************************)
(* This is the TLA-specification of the Doris mempool.  The Doris mempool  *)
(* is based on the Narwhal mempool with Tusk as consensus as described by  *)
(* George Danezis, Eleftherios Kokoris Kogias, Alberto Sonnino, and        *)
(* Alexander Spiegelman in their                                           *)
(* `^\href{https://arxiv.org/abs/2105.11827}{paper}^'.  Further            *)
(* inspiration is taken from                                               *)
(* `^\href{https://arxiv.org/abs/2102.08325}{DAG-rider}^', which in turn   *)
(* is a precursor to Narwhal.                                              *)
(***************************************************************************)
EXTENDS Functions 

\* For the module "Functions", we rely on the
\* `^\href{https://raw.githubusercontent.com/tlaplus/CommunityModules/master/modules/Functions.tla}{Community Module}̂'

-----------------------------------------------------------------------------

(***************************************************************************)
(*                             GENERAL SETUP                               *)
(***************************************************************************)

\* The set of batches
CONSTANT Batch

\* Assume there are some batches (for the purpose of liveness)
ASSUME Batch # {}

\* The following fct. "hash" is convenient to model a hash function.

hash == [
         b \in Batch
         |-> 
         [h \in {"hash"} |-> b]
         ] \* <- emacs has some "funny" indentation in tla-mode

\* The set hof hashes of any possibly batch is the range of "hash".
BatchHash == Range(hash)

====
