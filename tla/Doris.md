# Narwhal-Rider: Δωρίς / Doris

We specify an instantiation of Narwhal, replacing garbage collection with DAG-rider's weak links. 
Most importantly, Doris provides two mechanisms to avoid bash flooding by Byzantine validators, 
each one tailored for a common class of transactions: 

1. Now or never (v1):  
    Some transactions might become useless
    if latency is large (cf. cross-chain MEV).
    Thus, batches that consist of such fast paced transactions
    are stamped with a _due height_. 
    The latter specifies a DAG height such that 
    the batch cannot be inculded into the DAG after 
    the _due height_. 
    Such “perishable” batches can be garbage collected 
    after they have “turned bad”. 
    In other words, 
    when a qourum of validator has broadcast 
    certificates of availability for the round after the _due height_, 
    the batch is obsolete. 
    
2. Slowly but surely (v2):  
    Some transaction do not care about a block or two of additional latency
    but instead need a stronger guarantee of eventual execution
    than fast paced but perishable batches. 
    We propose the following _announcment mechanism_ to 
    serve transactions execution guarantee: 
    validators can _announce_ batch hashes within a block
    *before* the batch has been broadcast; 
    we can limit the number of such commitment slots per validator. 
    Leveraging the power of reliable broadcast, 
    the corresponding batches will be broadcast as usual, 
    without any due date. 
    Thus, 
    a correct validator might reserve space for the batch
    when signing the batch announcement, 
    but not necessarily; 
    similarly, 
    announced batches could be given higher priority.

Weak links are preferable over the re-injection strategy of Narwhal & Tusk for at least two reasons.
First, there is a risk of repeated need for re-injection, 
such that some batches actually might be pushed back so far 
that doubts about censorship resistnance arise, rightfully so. 
Second, 
as soon as a batch appears in a block, 
they will eventually be executed;
in other words, we are back to the world of qulitatively relialbe broadcast
(and not only reliable broadcast with high probability). 

This fits well with the the ideas of the batch announcement:
announced batches also will eventually be included
(in case the validator functions properly). 

Last but not least, as a side effect, we can widen the causal history
of nodes in presence of a small number of Byznatine nodes beyond
Narwhal's ⅔-rds ratio.  We assume a general consensus for leader block
selection is via pure non-deterministic choice, reminiscent of Tusk. 

In summary, 
we have a garbage collection mechanism at the granularity of batches, 
the possibility to reliably include batches (by correct validators). 



