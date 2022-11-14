---
title: "From TLA+ to “stateright” … and back again"
author: "Tobias Heindel" 
---

# Generalities

## Absolute generalities: the `bx`

This document is putting on goggles of [bi-directional transofmations](https://en.wikipedia.org/wiki/Bidirectional_transformation)
of (meta-)models. 

## Untyped Sets vs. actual rust data-types

As TLA+ does not have any types (since everything is a set), 
one probably has to add type annotations, 
which allow to derive the corresponding types in rust. 
A restrictive way to do this is to enforce the type system 
of [apalache-mc](https://apalache.informal.systems/docs/apalache/index.html).

One might be tempted to say that one could just use hash-sets. 
However, then one still has to provide types for the elements of those! 

## Message passing style

**‼**
“stateright” uses UDP, so we can only hope for safety of a "direct" implementation, because liveness is down the drain because auf message loss ‽

**‼**
similary, what about authentication of message senders?


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

A buzzword that needs to be dropped is bi-directional transformations,
a general idea. 
It comes in several flavours, 
e.g., so-called [lenses](https://bryceclarke.github.io/The_Double_Category_Of_Lenses_Phd_Thesis.pdf).
