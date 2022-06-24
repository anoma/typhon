# Narwhal-Rider: Δωρίς

We specify an instantiation of Narwhal with optional usage of DAG-rider's weak links of limited depth. 
The latter allow to widen the causal history of nodes in presence of a small number of Byznatine nodes beyond Narwhal's ⅔-rds ratio.
Finally, 
garbage collection is only for blocks that 
are provbly orphaned (to at least one honest validator). 
In the first version, 
the role of consensus for leader block selection is via  pure non-deterministic choice, reminiscent of Tusk. 

The first envisioned safety property
is the partition of transaction batches at honest validators into pairwise disjoints sets whose element are ① committed, 
② in progress, or ③ provably orphaned. 
The first liveness property is that every (honest) validator will advance their rounds. 
