# Narwhal-Rider: Δωρίς / Doris

We specify an instantiation of Narwhal, replacing garbage collection with DAG-rider's weak links. 
Most importantly, Doris provides two mechanisms to avoid bash flooding by Byzantine validators, 
each one tailored for a common class of transactions: 

1.  Now or never (v1):  
    Some transactions might become useless if latency is large (cf. cross-chain MEV). 
    Thus, batches of this kind of transactions are stamped with a "best before" stamp, 
    which specifies until which DAG height the batch needs to be kept. 
    Such perishable batches can be dumped after they have turned bad, 
    i.e., as soon as the commited DAG has surpassed the specified height. 
    
2.  Slow but sure (v2):  
    Some transaction do not care about a block or two of additional latency. 
    Here, batch signatures are included directly within blocks, 
    and **a batch** is ordered for execution
    as soon as a there is a quorum of commited blocks that contain batch signatures. 

Weak links are preferable over the re-injection strategy of Narwhal & Tusk for at least two reasons.
First, there is a risk of repeated need for re-injection, such that some batches actually might be pushed back so far 
that doubts about censorship resistnance arise, rightfully so. 
Second, as soon as a batch appears in a block, they will eventually be executed;
in other words, we are back to the world of qulitatively relialbe broadcast
(and not only reliable broadcast with high probability). 

Last but not least, as a side effect, we can widen the causal history
of nodes in presence of a small number of Byznatine nodes beyond
Narwhal's ⅔-rds ratio.  We assume a general consensus for leader block
selection is via pure non-deterministic choice, reminiscent of Tusk.

