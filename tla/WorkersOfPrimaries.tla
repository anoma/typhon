---------------------- MODULE WorkersOfPrimaries ----------------------------

(***************************************************************************)
(*                     WORKER-PRIMARY DISTINCTION                          *)
(***************************************************************************)

(***************************************************************************)
(* One idea of Narwhal is explicit parallelism via a number of workers.    *)
(* Each worker of a correct validator will have a "mirror" worker at every *)
(* other validator.  We use a public parameter, typically finite, which    *)
(* serves to index workers such that mirror workers share the same index.  *)
(* There is no point of using invalid indices by bad validators as these   *)
(* would be ignored.                                                       *)
(***************************************************************************)


CONSTANT 
  \* @type: Set(WORKER_INDEX);
  WorkerIndex \* a publicy known set of indices

\* A specific worker has a worker index and serves a (Byzantine) validator 
\* @type: Set({ index : WORKER_INDEX, val : BYZ_VAL });
Worker == [index : WorkerIndex, val : ByzValidator] 


(***************************************************************************)
(* There is a bijection between ByzValidators and Primaries.  For the sake *)
(* of simplicity, we identify them in the specification.                   *)
(***************************************************************************)

\* @type: Set(BYZ_VAL);
Primary == ByzValidator \* no need to distinguish in the TLA-spec

=============================================================================
