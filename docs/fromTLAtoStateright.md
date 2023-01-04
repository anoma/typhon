---
title: "From TLA⁺ to “stateright” … or the other way around"
author: ᚦ
---

# Generalities

The problem at hand is 
“matching” (formal) specifications with their implementation—‍‍in general, 
and in particular for 
[Typhon](https://specs.anoma.net/main/architecture/consensus/typhon.html); 
the latter is—_very roughyly_—the 
underlying L1 of [Anoma](https://anoma.net/),
developed by [Heliax](https://heliax.dev/). 
The good news is that there are approaches that allow to update 
_either one_ of the specification or the code, 
which then determines candidates for “best fixes” on the other end. 
However, 
even a uni-directional transformation 
from stateright code to TLA⁺ specifications
is non-trivial. 

## Some theory: `bx` frameworks

There is a whole research field concerning
[bi-directional transofmations](https://en.wikipedia.org/wiki/Bidirectional_transformation) 
of (meta-)models 
(see, e.g., these [lecture notes](https://link.springer.com/book/10.1007/978-3-319-79108-1)).
Most notably, we have
[lenses](https://ncatlab.org/nlab/show/delta+lens) (also featuring in Juvix) and 
[triple graph grammars](https://de.wikipedia.org/wiki/Tripel-Graph-Grammatik).[^1] 
In fact, 
actions in TLA⁺ specifications can be written in 
a pre-/post-condition style, 
mimicking the pre- and post-sets of Petri nets.[^2] 

## Actor model/models and [ᴀᴄᴛᴏʀꜱ](https://dspace.mit.edu/handle/1721.1/6952)

We will give a short review of the actor model, 
as developped by [Agha](https://dspace.mit.edu/handle/1721.1/6952). 
Following _op. cit._, each actor is specified by three entities:

1. a finite set of communications sent to other actors;
2. a new behavior 
   (which will govern the response to the next communication processed); 
   and,
3. a finite set of new actors created.

Interestingly, 

> the behavior of an actor can be _history sensitive_.



# Comparison of TLA⁺ and stateright

We start with short lists of similarities and differences.
Despite being (very) incomplete, 
the comparison already motivate the challenge 
that a general bi-directional transformation would face. 

## Similarities between TLA⁺ and stateright 

Both define [transition systems](https://en.wikipedia.org/wiki/Transition_system), 
and each transition between states is the effect of _actions_. 


### State

In TLA⁺, 
the state of the system is described by the “contents” of variables. 
In stateright, 
`State` is a type to be provided by any implementation of stateright `Model`-trait. 

### Actions

In TLA⁺, 
actions are described by formulæ 
that describe relations between states; 
these relations can be (partial) functions, 
but nothing requires this. 
In contrast, 
stateright enforces that each state has a list[^3] of _actions_,
each of which has at most one unique “target” state. 
Thus, 
stateright-actions are effectively _names_ 
for transitions in stateright.

## Differences between TLA⁺ and stateright 

In TLA⁺, actions are arbitrary relations on the set of states. 
In stateright, 
actions are essentially a proxy for transitions: 
each action can have at most one effect. 

<!-- 
TLA⁺ allows for rather general system specifications, 
supplemented with a tree of refinements 
where leaves would ideally be implementations 
and paths from the top level spec to the leaves 
one possibility to gradually add implementation detail to a specification. 
-->

## “Symmetric difference”: possible causes for issues

Each of the two frameworks provides some features 
that the other one lacks. 

### TLA⁺ extra functionality

TLA⁺ has a “built in” model checker, viz. TLC, 
which provides liveness checking. 
This model checking feature is at best experimental in stateright. 

### Extra functionality of stateright 

Stateright provides arbitrary `rust`-function calls. 


## Summary of the comparison of `stateright` and TLA⁺

Concerning translating formal specifications into code 
and _vice versa_: 

- going from TLA⁺ to stateright is in theory always possible 
  (as soon as the involved sets are finite);

- translation  `stateright`-code, i.e., `Actor`-implementations, to TLA⁺ models
  has to deal with arbitrary rust calls. 

The action of the arbitrary rust calls are of course an issue, 
which one needs to be aware of. 
However, 
the code generation approach is likely to suffer a lot of issues, 
including the usefulness and performance of the code. 
We thus approach the _prima facie_ more difficult approach:
generating TLA⁺ specs from `stateright` code. 

# Sketching the _image_ of _actor-based_ `stateright` in TLA⁺

Even if rust function calls are an obvious challenge,
in theory, 
we have valid over-approximations of the behaviour of a stateright model.
<!--
This becomes quite natural in the actor model, 
as function calls should only change the local state of an actor. 
-->
This is particularly natural for stateright models 
that follow the actor-based approach, 
as each function call of an actor _should_ only be able 
to change the actors state. 

‼ 
the `latest` version is `0.29.0` 
⇒ replace `latest` with `0.29.0` in the code references below and elsewhere
¡

## Reviewing actors in stateright 
The
[`Actor`-trait](https://docs.rs/stateright/latest/src/stateright/actor.rs.html#243-286)
(see also the excerpt below)
in stateright requires that each actor 

- has a specific type of messages it can process (called `Msg`);

- has a state type (called `State`);

- implements the `on_start`-function, 
  which is called on instances after spawning, 
  e.g., to initialize the state;

- implements the `on_msg`-function, 
  which specifies the reactions of an actor to received messages, 
  such as state changes, sending responses, and setting timers.

```rust
pub trait Actor: Sized {
    /// The type of messages sent and received by the actor.
    type Msg: Clone + Debug + Eq + Hash;

    /// The type of state maintained by the actor.
    type State: Clone + Debug + PartialEq + Hash;

    /// Indicates the initial state and commands. 
    fn on_start(&self, id: Id, o: &mut Out<Self>) -> Self::State;

    /// Indicates the next state and commands when a message is received. See [`Out::send`].
    fn on_msg(&self, id: Id, state: &mut Cow<Self::State>, src: Id, msg: Self::Msg, o: &mut Out<Self>) {
        // no-op by default
    }

    /// Indicates the next state and commands when a timeout is encountered. See [`Out::set_timer`].
    fn on_timeout(&self, id: Id, state: &mut Cow<Self::State>, o: &mut Out<Self>) {
        // no-op by default
    }
}
```

Let us go in more detail over this code, 
making the connection to the actor model along the way. 
Each actor implementation must define 

- a static type for message it can send and receive, 
  namely `Msg`; 
- a static type for the private state 
  that the actor can be at any point in time;
- ‼ how are we “supposed” to use the initialization ¡



‼ _explanation for `&mut`s_ 

The use of mutable references seems to break 
the actor model; 
however, 

¡

### Operational semantics of actor models in `stateright`

The operational semantics is in terms of 
a  labelled transitions system (ʟᴛꜱ), 
which, roughly, is the least common denominator of TLA⁺ and `stateright`.
A ʟᴛꜱ consists of

- a set of states, and

- a family of transition relations, which is indexed over 

- a set of labels. 

A _transition_ is an element of some transition relation, 
i.e., a triple $(x,l,y)$ 
consisting of 

- $x$, the state in which the transition is enabled;
- $y$, the state that the transition leads to; and
- $l$, the transition label $l$.






#### The state of an actor model in `stateright` 


The transition system of an `ActorModel` is defined by the 
[`next_state`](https://docs.rs/stateright/latest/src/stateright/actor/model.rs.html#241-308). 
As can be seen from the signature
```rust
fn next_state(&self, x: &Self::State, a: Self::Action) -> Option<Self::State>
```
it is a function, which maps a state and an action to _the_ next state
(if the action is enabled). 
Thus, `stateright` assumes that all transition relations are partial functions. 
Each action is either 
1. [message delivery](https://docs.rs/stateright/0.29.0/stateright/actor/enum.ActorModelAction.html#variant.Deliver);
2. [timeout](https://docs.rs/stateright/0.29.0/stateright/actor/enum.ActorModelAction.html#variant.Timeout); or
3. [message loss](https://docs.rs/stateright/0.29.0/stateright/actor/enum.ActorModelAction.html#variant.Drop). 
We now describe 
how `stateright` handles each of these cases. 


#### [Message delivery](https://docs.rs/stateright/latest/src/stateright/actor/model.rs.html#248-287)

The crucial point of message delivery is 
[calling](https://docs.rs/stateright/latest/src/stateright/actor/model.rs.html#259)
the receiving actor's `on_msg` function. 
It is called with a “empty” output signal, 
i.e., the output is essentially a return value of the `on_msg`-function. 
Moreover, 
the actor's state is 




1. https://docs.rs/stateright/0.29.0/stateright/actor/enum.ActorModelAction.html




We can then automatically generate a TLA⁺ spec (with lots of spurious behaviour). 
Still, 
this lets us extract conceptual model of 
the stateright implementation. 
In fact, 
here, we are re-using ideas 
from the [_ReActor_ Specification Language, §3](https://cs.emis.de/LNI/Proceedings/Proceedings213/127.pdf),
which provides TLA⁺ semantics for 
(a specific class of) actor systems. 
For a quick  intro to actors, 
see e.g., [this blog post](https://bbengfort.github.io/2018/08/actor-model/)
by Benjamin Bengfort, 
or [here](https://berb.github.io/diploma-thesis/original/054_actors.html), 
and many [other ressources](https://en.wikipedia.org/wiki/Actor_model#Further_reading). 

> The Actor Model is a ~~solution~~ [model] for ~~reasoning about~~ concurrency in distributed systems that helps eliminate unnecessary synchronization. In the actor model, we consider our system to be composed of _actors_, computational ~~primitives~~ [processes] that have a private state, can send and receive messages, and perform computations based on those messages. The key [idea] is that a system is composed of many actors and actors do not share memory, they have to communicate with messaging.



## Types of actors


## State of each actor 




```rust
/// An actor initializes internal state optionally emitting [outputs]; then it waits for incoming
/// events, responding by updating its internal state and optionally emitting [outputs].
///
/// [outputs]: Out
pub trait Actor: Sized {
    /// The type of messages sent and received by the actor.
    ///
    /// # Example
    ///
    /// ```
    /// use serde::{Deserialize, Serialize};
    /// #[derive(Clone, Debug, Eq, Hash, PartialEq)]
    /// #[derive(Serialize, Deserialize)]
    /// enum MyActorMsg { Msg1(u64), Msg2(char) }
    /// ```
    type Msg: Clone + Debug + Eq + Hash;

    /// The type of state maintained by the actor.
    ///
    /// # Example
    ///
    /// ```
    /// #[derive(Clone, Debug, Eq, Hash, PartialEq)]
    /// struct MyActorState { sequencer: u64 }
    /// ```
    type State: Clone + Debug + PartialEq + Hash;

    /// Indicates the initial state and commands.
    fn on_start(&self, id: Id, o: &mut Out<Self>) -> Self::State;

    /// Indicates the next state and commands when a message is received. See [`Out::send`].
    fn on_msg(
        &self,
        id: Id,
        state: &mut Cow<Self::State>,
        src: Id,
        msg: Self::Msg,
        o: &mut Out<Self>,
    ) {
        // no-op by default
        let _ = id;
        let _ = state;
        let _ = src;
        let _ = msg;
        let _ = o;
    }

    /// Indicates the next state and commands when a timeout is encountered. See [`Out::set_timer`].
    fn on_timeout(&self, id: Id, state: &mut Cow<Self::State>, o: &mut Out<Self>) {
        // no-op by default
        let _ = id;
        let _ = state;
        let _ = o;
    }
}
```


<!--In principle, 
the TLC model check
-->


## Untyped Sets vs. “actual”  data-types 
As TLA⁺ does not have any types (since everything is a set), 
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

It is non-trivial to divide the state of a TLA⁺-spec. 
In fact, 
[Hewitt states](http://lambda-the-ultimate.org/node/5181?from=200&comments_per_page=200) even claims that

> TLA⁺ incorrectly treats state as global,
 
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
as soon as two TLA⁺ actions access the same (“slice” of a) variable, 
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

1. a fully formal spec, e.g. in TLA⁺, in principle executable---model checkable is enough!

2. a (protoype) implementation. 

## model options for the formal spec

There might actually be better modelling languages than TLA⁺. 
One simple example that comes to mid is Communicating Machines

[McScMc: {[…]} Verification of Communicating Machines](https://link.springer.com/chapter/10.1007/978-3-642-28756-5_34)

These are intuitively much close to what Typhon is using.

## Back and forth translations

A buzzword that needs to be dropped again are bi-directional transformations,
a general idea. 
It comes in several flavours, 
e.g., so-called [lenses](https://bryceclarke.github.io/The_Double_Category_Of_Lenses_Phd_Thesis.pdf).

# misc 

## further reading

[rebeca](https://content.iospress.com/articles/fundamenta-informaticae/fi63-4-05)

## food for thought

[Concurrency in vertical vs. horizontal sclaing](https://www.section.io/blog/scaling-horizontally-vs-vertically/) 
mentions the actor model for vertical scaling. 


---

[^1]: Triple graph grammars might actually be useful 
    in that they allow to specify the protocol using [graph transformation](https://en.wikipedia.org/wiki/Graph_rewriting), which vastly generalize [Petri nets](https://en.wikipedia.org/wiki/Petri_net). 

[^2]: There is a subset of TLA⁺ specifications, which actually mimick simple graph transformation. 

[^3]: It is a vector, to be precise.

