# Day 1: Introduction to homotopy type theory

Lecturer: [Andrej Bauer](http://www.andrej.com/)

## Schedule

The online lectures will take place on Monday, April 12, 2021.
All times are in UTC+2.

| Time        | Topic                                      |
|:------------|:-------------------------------------------|
| 14:00–14:10 | Opening & Introduction                     |
| 14:10–14:50 | Part 1: Dependent type theory              |
| 14:50–15:05 | (break)                                    |
| 15:05–15:45 | Part 2: Identity types                     |
| 15:45–16:00 | (break)                                    |
| 16:00–16:40 | Part 3: Homotopy levels                    |
| 16:40–16:55 | (break)                                    |
| 17:55–17:35 | Part 4: Equivalences                       |
| 17:35–17:50 | (break)                                    |
| 17:50–18:30 | Part 5: Univalence                         |

We shall keep a strict schedule. Each part will consist of a short lecture, followed by exercises and a discussion.


## Background reading

On the first day we shall learn the basics of homotopy type theory. It is quite impossible to teach or learn the topic
thoroughly and in detail in just a single day. We shall therefore give an overview of the main concepts and ideas, but
will have to skip many details. We *highly* recommend that the attendees take the time to do some background reading
*ahead of time*.

You can start by looking over the slides of the lecture [Spartan Martin-Löf Type
Theory](https://github.com/UniMath/Schools/raw/master/2019-04-Birmingham/Part1_Spartan_Type_Theory/Spartan-Type-Theory.pdf)
by Andrej Bauer, delivered at the [School and Workshop on Univalent Mathematics
2019](https://unimath.github.io/bham2019/).

Next, we recommend a combination of Chapter 1 of [Homotopy type theory: Univalent Foundations of
Mathematics](https://homotopytypetheory.org/book/), and the [video lectures on homotopy type
theory](https://github.com/andrejbauer/homotopy-type-theory-course#homotopy-type-theory), given by Andrej Bauer in 2019
at the Faculty of Mathematics and Physics, at the University of Ljubljana.

It is not necessary to actually learn all of the above material. However, at least reviewing it will help you follow the
accelerated pace of the lectures.


## Contents

[Lecture notes](./Introduction to HoTT (EPIT 2020 school).pdf) are now available.

### Part 1: Dependent type theory

* Type theory as a theory of constructions
* The notion of a dependent type
* Judgement forms: types, terms, and equalities
* Types as spaces, dependent types as fibrations
* Basic constructions:
    * dependent sum `Σ`
    * dependent product `Π`
    * function type `→` and simple products `×` as special cases of `Σ` and `Π`
    * universe `U`, dependent type as a map into the universe
    * basic types `unit`, `empty`, `bool`
    * natural numbers `N`


### Part 2: Identity types

* Identity types as path objects
* Path induction
* Iterated identity types
* The action of a map on a path, transport


### Part 3: Homotopy levels

* Contractible spaces
* Propositions, sets, and `n`-Types
* Truncation
* The embedding of logic into type theory (using propositional truncation)
* Structure vs. property in mathematics
* Basic homotopy-theoretic constructions in terms of truncation:
    * loop space vs. fundamental group
    * path-connectedness vs. contractibility
    * surjectivity vs. split epimorphism


### Part 4: Equivalences

* Notions of equivalence of types
* Homotopy equivalences
* Universal property stated as an equivalence


### Part 5: Univalence

* The idea that equivalent structures are equal
* Univalence axiom
* Some consequences of the univalence axiom
