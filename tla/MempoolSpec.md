# Mempool Specification 

We give a short description of 
the properties a mempool should satisfy abstractly, 
along the lines of Lamport's
[TLA+ spec](https://lamport.azurewebsites.net/tla/Consensus.tla) of consensus. 
A closely related idea is 
[`Set Byzantine Consensus`
](https://ieeexplore.ieee.org/abstract/document/9519440/).
A related problem is [byzantine set-union consensus
(BSC)](https://link.springer.com/article/10.1186/s13635-017-0066-3),
which is presented such that it can be seen as an instance of the
Byzantine consensus problem where validity is only assumed to be
_weak_. 
We refer to the [latter
paper](https://link.springer.com/article/10.1186/s13635-017-0066-3)
as~[BSC]
and [the former
](https://ieeexplore.ieee.org/abstract/document/9519440/) as [SBC].



