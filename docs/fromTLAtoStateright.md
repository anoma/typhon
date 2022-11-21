---
title: "From TLA+ to “stateright” … and back again"
author: "Tobias Heindel"
---

# Generalities

The problem at hand is 
making
(formal) specifications “match” 
their implementation—‍in 
general, and in 
particular for [Typhon](https://specs.anoma.net/main/architecture/consensus/typhon.html); 
the is—_very roughyly_—the underlying L1 of [Anoma](https://anoma.net/),
developed by [Heliax](https://heliax.dev/)/. 
The good news is that
there are approaches that 
allow to update _either one_ of the two, 
and get the “least fix” of the other side. 

## Some theory: `bx` frameworks

There is a whole research field concerning [bi-directional transofmations](https://en.wikipedia.org/wiki/Bidirectional_transformation) of (meta-)models; 
see, e.g., these [lecture notes](https://link.springer.com/book/10.1007/978-3-319-79108-1).
Most notably, 
we have [lenses](https://ncatlab.org/nlab/show/delta+lens) (also featuring in Juvix) 
and [triple graph grammars](https://de.wikipedia.org/wiki/Tripel-Graph-Grammatik).[^1] 
In fact, 
actions in TLA+ specifications can be written in 
a pre-/post-condition style, 
mimicking the pre- and post-sets of Petri nets.[^2] 


# Comparison of TLA+ and stateright, general

We start with short lists of similarities and differences. 

## Similarities between TLA+ and stateright 

Both define [transition systems](https://en.wikipedia.org/wiki/Transition_system), 
and each transition between states is the effect of _actions_. 


### State

In TLA+, 
the state of the system is described by the “contents” of variables. 
In stateright, 
`State` is a type to be provided by any implementation of stateright `Model`-trait. 

### Actions

In TLA+, 
actions are described by formulæ 
that describe relations between states; 
these can but are not necessarily (partial) functions. 
In stateright, 
each state comes with a list[^3] of actions 
where each action has at most one unique “target” state. 

## Differences between TLA+ and stateright 

In TLA+, actions are allowed to be (proper) relations between states. 
This allows to have very general system specifications 
with a tree of refinements 
where leaves would ideally be implementations. 
In stateright, 
actions are essentially a proxy for transitions: 
each action can have at most one effect. 

## “Symmetric differences”: stuff that might cause trouble

Each of the two formalism provides functionality  
the other has not. 

### TLA+ extra functionality

TLC provided liveness checking. This feature is at best experimental in stateright. 

### Extra functionality of stateright 

Stateright provides arbitrary `rust`-function calls. 

## Summary

For the purpose of translation, 
going from TLA+ to stateright should in principle be always an option, 
as soon as the involved sets are finite. 
<!--In principle, 
the TLC model check
-->



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

One might be tempted to say that one could just use hash-sets as everything is a set. 
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
Moreover, 
actions should only access local state in their pre-codition. 
Thus, 
as soon as two TLA+ actions access the same (“slice” of a) variable, 
the two actions belong to the same actor. 
This will become clearer by looking at an example. 

# Examples 

Let us see how the above generalities look like in 
some specific examples, namely: 

- the “resource managers” example from [Building Distributed Systems With Stateright](https://www.stateright.rs/title-page.html)

-

## The “resource managers” example 

### The fixed set of ressource managers

The specification mentions only a set of ressource managers, 
called `RM`. 

[comment_one]: # https://www.uv.es/wikibase/doc/cas/pandoc_manual_2.7.3.wiki?174

[comment_two]: # https://packagecontrol.io/packages/TLAPlus 

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
instead a struct that 
‽


## Message “queues” vs. local state of resource managers vs. X

In the example, 
the `TypeOK`-predicate provides some information about
which state is local to the resource managers.

…

## Actions



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


# misc 

[rebeca](https://content.iospress.com/articles/fundamenta-informaticae/fi63-4-05)

---

[^1]: Triple graph grammars might actually be useful 
    in that they allow to specify the protocol using [graph transformation](https://en.wikipedia.org/wiki/Graph_rewriting), which vastly generalize [Petri nets](https://en.wikipedia.org/wiki/Petri_net). 

[^2]: There is a subset of TLA+ specifications, which actually mimick simple graph transformation. 

[^3]: It is a vector, to be precise. 

