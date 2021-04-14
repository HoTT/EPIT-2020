# Day 3: Cubical and simplicial models of HoTT

Lecturer: Christian Sattler

## Overview and prerequisites

We will give an introduction to simplicial and cubical models of homotopy type theory.
We asume basic familiarity with category theory (e.g., universal properties, adjunctions, Yoneda lemma).

You do not have to be familiar with models of type theory or simplicial or cubical sets, although it will make some lectures easier to follow.

## Schedule

The online lectures will take place 14:00–18:30 on Wednesday, April 14, 2021.
All times are in UTC+2.

| Time        | Topic                                                |
|:------------|:-----------------------------------------------------|
| 14:00–14:15 | Part 0: Introduction                                 |
| 14:15–14:35 | Part 1: What is a model of type theory?              |
| 14:35–14:45 | (break)                                              |
| 14:45–15:00 | Part 2: Presheaf models                              |
| 15:00–15:30 | Exercise session 1                                   |
| 15:30–15:45 | (break)                                              |
| 15:45–16:20 | Part 3: The simplicial model of HoTT                 |
| 16:20–16:30 | (break)                                              |
| 16:30–16:45 | Part 4: Cubical models and open questions            |
| 16:45–17:15 | Exercise session 2                                   |
| 17:15–17:30 | (break)                                              |
| 17:30–18:30 | Valery Isaev: Arend proof assistant                  |

*The above is a rough schedule. If we run overtime in the lectures, we will shorten the exercise sessions.*

Due to the tight schedule, we might have to skip over some aspects.
We can certainly not go into all the details.
I will be available 10:00–13:00 on Thursday on Discord for in-depth discussions.

## Contents

[Lecture notes](notes-start.pdf)

### Part 0: Introduction

* Overview of existing models
* Connections with ∞-toposes

### Part 1: What is a model of type theory?

* Category of contexts and substitutions
* Presheaves and discrete fibrations
* Our notion of model: categories with families
* Contextuality/democracy
* Algebraicity vs. categoricity
* Types and display maps
* Type formers:
  - `Σ`/`Π`-types via adjoints to substitution on types
  - `Id`-types via lifting
  - Universe `U` via reflection
* Examples: sets, groupoids

### Part 2: Presheaf models

* Coreflection of discrete fibrations
* `Π`-types (via coreflection)
* Hofmann-Streicher universe (via coreflection)
* Type formers internally to presheaves over contexts
* Presheaf models as bootstrappers for simplicial/cubical models

### Part 3: The simplicial model of HoTT

* Simplicial sets
* Homotopical structure on simplicial sets
* Weak factorization systems
* Pushout/pullback constructions
* Interpretation of HoTT
* Constructivity problems

### Part 4: Cubical models and open questions

* Cubical models:
  - the connection approach
  - the Cartesian approach
* Right adjoint to exponentiation with interval
* Construction from extensional model with dependent right adjoint
* Open questions

## Additional material and literature pointers

This list does not attempt to be complete.

### Simplicial sets

* [A leisurely introduction to simplicial sets](http://www.math.jhu.edu/~eriehl/ssets.pdf)

* [An elementary illustrated introduction to simplicial sets](https://arxiv.org/abs/0809.4221)

* A standard textbook on simplicial sets and their use in homotopy theory: Simplicial Homotopy Theory by Goerss and Jardine.
  You can google for it.

### Simplicial models

* The original simplicial set model: [The Simplicial Model of Univalent Foundations (after Voevodsky)](https://arxiv.org/abs/1211.2851).

* Breakthrough result: HoTT (minus HITs) can be interpreted in all (∞, 1)-toposes: [All (∞,1)-toposes have strict univalent universes](https://arxiv.org/abs/1904.07004)
  Shulman has an extension of this to HITs forthcoming.

* Categorical presentation of fibrancy of Π-types (right properness): [The Frobenius Condition, Right Properness, and Uniform Fibrations](https://arxiv.org/abs/1510.00669)

* Categorical presentation of equivalence extension (univalence): [The Equivalence Extension Property and Model Structures](https://arxiv.org/abs/1704.06911) (under revision)

### Cubical models

* The original connection-style model: [Cubical Type Theory: a constructive interpretation of the univalence axiom](https://arxiv.org/abs/1611.02108)

* development using "extensional" type theory (ETT) as internal language of presheaves: [Axioms for Modelling Cubical Type Theory in a Topos](https://arxiv.org/abs/1712.04864)

* using ETT with modalities to develop the universe internally: [Internal Universes in Models of Homotopy Type Theory](https://arxiv.org/abs/1801.07664)

* Canonicity results using a semantic technique (gluing): [Canonicity and homotopy canonicity for cubical type theory](https://arxiv.org/abs/1902.06572)

* Cartesian-style model: [Syntax and Models of Cartesian Cubical Type Theory](http://www.cs.cmu.edu/~./cangiuli/papers/abcfhl.pdf)
