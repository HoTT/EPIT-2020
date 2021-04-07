# Cubical Type Theory and Cubical Agda

Lecturer: [Anders Mörtberg](https://staff.math.su.se/anders.mortberg/)

## Installation of Cubical Agda and agda/cubical

In order to follow the course one needs a recent release of Agda (version >=2.6.1): https://wiki.portal.chalmers.se/agda/Main/Download

One also needs to download and build v0.2 of the agda/cubical library: https://github.com/agda/cubical/releases/tag/v0.2

If one has installed Agda (2.6.3) and have the `agda` executable in ones path then building v0.2 of the library should work by running `make` in the cubical-0.2 directory after unpacking the v0.2 package. If one wants to use the agda/cubical library in another directory one has to register it by following: https://github.com/agda/cubical/blob/master/INSTALL.md#registering-the-cubical-library

Students with the intention to contribute to the library will need to install the development version of Agda and the latest version of the [agda/cubical](https://github.com/agda/cubical) library. Detailed instructions can be found at: https://github.com/agda/cubical/blob/master/INSTALL.md

It can be a bit complicated to install the development version of Agda and Anders uses the "cabal sandbox install instructions" solution, but other solutions might work better on other systems.

## Schedule

The online lectures will take place on Thursday, April 15, 2021.
All times are in UTC+2.

| Time        | Topic                                      |
|:------------|:-------------------------------------------|
| 14:00–14:15 | Part 1: Introduction                       |
| 14:15–14:45 | Part 2: The interval and path types        |
| 14:45–15:00 | (break)                                    |
| 15:00–15:30 | Part 3: Transport and composition          |
| 15:30–16:00 | Part 4: Univalence and the SIP             |
| 16:00–16:15 | (break)                                    |
| 16:15–17:00 | Part 5: Higher inductive types             |
| 17:00–17:15 | (break)                                    |
| 17:15–18:30 | Exercise session                           |

## Contents

### Part 1: Introduction

#### Lecture

* Why Cubical Type Theory?
* Cubical Agda demo

#### Exercises

* TODO

### Part 2: The interval and path types

#### Lecture

* The interval in Cubical Agda
* Path and PathP types
* Function extensionality
* Equality in Sigma types

#### Exercises

* TODO

### Part 3: Transport and composition

#### Lecture

* Cubical transport
* Subst as a special case of cubical transport
* Path induction from subst?
* Homogeneous composition (hcomp)
* Binary composition of paths as special case of hcomp

#### Exercises

* TODO

### Part 4: Univalence and the SIP

#### Lecture

* Univalence from ua and uabeta
* Transporting with ua (examples: `ua not : Bool = Bool`, `ua suc : Z = Z`, ...)
* Subst using ua
* The SIP as a consequence of ua
* Examples of using the SIP for math and programming (algebra, data structures, etc.)

#### Exercises

* TODO

### Part 5: Higher inductive types

#### Lecture

* Quotients via HITs
* Propositional truncation for logic?
* CS example using quotients (maybe finite multisets or queues)
* Synthetic homotopy theory (maybe `Torus = S^1 * S^1`, `pi_1(S^1) = Z`, `pi_1(Torus) = Z * Z`)

#### Exercises

* TODO

## Additional material

Here are some pointers to further reading about Cubical Agda and examples of programming and proving in cubical type theory:

- [Cubical Agda: A dependently typed programming language with univalence and higher inductive types](https://staff.math.su.se/anders.mortberg/papers/cubicalagda2.pdf) - Paper about Cubical Agda. Contains quite a few examples and explains how the system is implemented.
- [Internalizing Representation Independence with Univalence](https://arxiv.org/abs/2009.05547) - Paper about proving representation independence results in Cubical Agda. This paper contains examples of reasoning cubically about datastructures and other CS examples.
- [Cubical Synthetic Homotopy Theory](https://staff.math.su.se/anders.mortberg/papers/cubicalsynthetic.pdf) and [Synthetic Cohomology Theory in Cubical Agda](https://staff.math.su.se/anders.mortberg/papers/zcohomology.pdf) - Synthetic algebraic topology in Cubical Agda. These papers contain various results from HoTT ported to Cubical Agda which led to some proofs becoming substantially shorter. There are also some new constructions and computations which rely on univalence and HITs not being axiomatic.
- [Three Equivalent Ordinal Notation Systems in Cubical Agda](https://arxiv.org/abs/1904.10759) - Some classical proof theory and ordinals in Cubical Agda.
- [Cubical Methods in Homotopy Type Theory and Univalent Foundations](https://staff.math.su.se/anders.mortberg/papers/cubicalmethods.pdf) - Lecture notes for the 2019 HoTT Summer School. The focus is more on cubical models and not so much on practical formalization in cubical type theory. Contains exercises and lots of background material. The reference list is quite extensive and contains pointers to further background material (a lot of it aimed at experts).
