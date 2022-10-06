------------------------- MODULE ByzantineDoris -----------------------------

\* 
\*  Specyfing additional Byzantine behaviour for Doris. 
\* 

\* list of assumptions

\* no invalid batches 
\*   using invalid batches is a problem for DoS 
\*   (which can only be modelled using a _quantiative_ spec) 
\* 

EXTENDS 
  Doris 

\* @type: BYZ_VAL => Bool;
isFake(validator) == 
 validator \in FakeValidator

\* @type: BYZ_VAL => Bool;
isCorrect(validator) == 
  ~isFake(validator)

allBUTbatchPoolNnextHxNstoredHx == 
  <<msgs, rndOf, storedBlx>>

\* ACTION "SpontaneousBatchBCBatchBCpreparation":
\*   gathering a batch and have it available wherever possible
\*   so fake validators can actually get their hands at 
\*   ᴀɴʏ batch
\* 
\* ¡batchPool, ¡nextHx, ¡storedHx
\* @type: (BATCH, $worker) => Bool; 
SpontaneousBatchBCBatchBCpreparation(batch, worker) ==
  LET
    \* @type: BATCH;
    b == batch 
    \* @type: $worker;
    w == worker
    \* @type: BYZ_VAL;
    p == worker.val 
  IN
  \* type checking
  /\ b \in Batch
  /\ w \in Worker
  \* pre-condition
     \* only for fake workers
  /\ isFake(w.val)
  \* post-condition: 
     \* add the batch `b` the the batch pool of `w`
  /\ batchPool' = \* ¡batchPool
       [batchPool EXCEPT ![w] = @ \cup {b}] 
     \* add the hash of the batch to the primary's next hashes
  /\ nextHx' = \* ¡nextHx
       [nextHx EXCEPT ![p] = @ \cup {hash(b)}] 
     \* also add the hash of the primary's stored hashes
  /\ storedHx' = \* ¡storedHx
       [storedHx EXCEPT ![p] = @ \cup {hash(b)}] 
     \* nothing else changes
  /\ UNCHANGED allBUTbatchPoolNnextHxNstoredHx

\* "FakeWorker":
\*   the set of all fake workers
\*
\* @type: Set($worker);
FakeWorker == 
  { w \in Worker : isFake(w.val) }

\* "allFakeBatches":
\*   the set of all batches collected by fake validators
\* 
\* @type: Set(BATCH);
allFakeBatches == 
  UNION { batchPool[w] 
          \cup 
          { h.batch : h \in nextHx[w.val] }
          \cup 
          { h.batch : h \in storedHx[w.val] } : w \in FakeWorker
        }


\* ACTION "SpontaneousBatchBC":
\*   broadcasting a batch, previously received
\* 
\* ¡msgs
\* @type: (BATCH, $worker) => Bool; 
SpontaneousBatchBC(batch, worker) ==
 \* pre-condition
    \* only Fake validators
 /\ isFake(worker.val) 
    \* "only" Fake batches
 /\ batch \in allFakeBatches
 \* broadcast the batch 
 /\ Send(batchMsg(batch, worker)) \* ¡msgs
     \* nothing else changes
 /\ UNCHANGED allBUTmsgs

\* Note: SpontaneousBatchBC could be changed to sending 
\*       _any_ batch

=============================================================================
