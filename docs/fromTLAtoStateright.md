---
title: "From TLA+ to “stateright” … and back again"
author: "Tobias Heindel"
---

# Generalities

The problem at hand is the matching 
of (formal) specifications with 
their implementation—‍in 
general, and in 
particular for the Typhon project at Heliax/Anoma. 
The good news is that
there are approaches that 
allow to update _either one_ of the two, 
and get the “least fix” of the other side. 


## Absolute generalities: `bx` frameworks

There is a whole research field concerning [bi-directional transofmations](https://en.wikipedia.org/wiki/Bidirectional_transformation) of (meta-)models. 
See, e.g., these [lecture notes](https://link.springer.com/book/10.1007/978-3-319-79108-1).
We have lenses (also featuring in Juvix), 
and triple graph grammars, 
which might actually be useful for
formal specifications of the system in terms of 
graph grammars—think Petri nets on steroids.
In fact, 
TLA+ specifications can be written in a graph transformation style,
using pre- and post-conditions 
(which in turn generalize pre- and post-sets of Petri nets).

## Untyped Sets vs. “actual”  data-types
As TLA+ does not have any types (since everything is a set), 
one probably has to add type annotations, 
which allow to derive the corresponding types in rust. 
A restrictive way to do this is to enforce the type system 
of [apalache-mc](https://apalache.informal.systems/docs/apalache/index.html).
A less restrictive approach, 
which “even” Lamport is consistently following,
is a (set of) `TypeOK`-predicates. 
The latter specify what it means for a variable do have the proper type. 
E.g., a certain variable has to be of function type between two (not necessarily constant) sets.

One might be tempted to say that one could just use hash-sets as everything is sets. 
However, then one still has to provide types for the elements of those…  
…and moreover, 
there are typically more natural choices than hash-sets; 
just think of natural numbers!

## Message passing style

For the case of _stateright_, 
there are some hurdles, 
due to the use of UDP, 
which does not fit the usual assumptions, 
_viz._

1. eventual delivery
2. message authentication. 

**‼**
“stateright” uses UDP, so we can only hope for safety of a "direct" implementation, because liveness is down the drain because auf message loss ‽

**‼**
similary, what about authentication of message senders?


## The state of the system, as contents of variables

It is non-trivial to divide the state of a TLA+-spec. 
In fact, 
[Hewitt states](http://lambda-the-ultimate.org/node/5181?from=200&comments_per_page=200) even claims that

> TLA+ incorrectly treats state as global,
 
although this [might actually be exaggerated](https://pron.github.io/posts/tlaplus_part1).
The take away is, 
_some care needs to be taken to “decompose” a system_
such that
we generate a natural set of _actors_ that communicate 
via message passing. 

In most protocols, 
it makes sense to separate out several message “pools”, 
which are sets consisting of all messages that have been sent. 


# The example from [Building Distributed Systems With Stateright](https://www.stateright.rs/title-page.html)

Let us see how the above generalities look like in 
some specific examples. 

## The “resource managers” example 


### The fixed set of ressource managers

The specification mentions only a set of ressource managers, 
called `RM`. 

```tla 
CONSTANT RM 
```

This is implicitly a finite set. 
In the concrete implementation, 
it is convenient to represent is as 
the initial segment of the natural numbers 
of the same cardinality. 
In short, this is a range of number (starting fro $0$).


```rust
type R = usize; // RM in 0..N

#[derive(Clone)]
struct TwoPhaseSys { pub rms: Range<R> } 
//Range is std::ops::Range
```

Interestingly, 
we don't have a constant here, 
instead 
‽


## Message “queues” and local state of resource managers

In the example, 
the `TypeOK`-predicate provides some information about
which state is local to the resource managers.

…

<!--

# The here and now (short term perspectives)
-->

# Long term persepctives

In the long term, 
we are looking to map back and forth between

1. a fully formal spec, e.g. in TLA+, in principle executable---model checkable is enough!

2. a (protoype) implementation. 

## model options for the formal spec

There might actually be better modelling languages than TLA+. 
One simple example that comes to mid is Communicating Machines

[McScMc: {[…]} Verification of Communicating Machines](https://link.springer.com/chapter/10.1007/978-3-642-28756-5_34)

These are intuitively much close to what Typhon is using.

## Back and forth translations

A buzzword that needs to be dropped again are bi-directional transformations,
a general idea. 
It comes in several flavours, 
e.g., so-called [lenses](https://bryceclarke.github.io/The_Double_Category_Of_Lenses_Phd_Thesis.pdf).
