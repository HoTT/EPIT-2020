# Day 1: Introduction to homotopy type theory

Lecturer: [Andrej Bauer](http://www.andrej.com/)

## Schedule

The online lectures will take place on Monday, April 12, 2021.
All times are in UTC+2.

| Time        | Topic                                      |
|:------------|:-------------------------------------------|
| 14:00–14:05 | Opening & Introduction                     |
| 14:05–14:35 | Part 1: Dependent type theory              |
| 14:40–15:10 | Part 2: Identity types                     |
| 15:10–15:40 | (break)                                    |
| 15:40–16:10 | Part 3: Homotopy levels                    |
| 16:15–16:55 | Part 4: Equivalences                       |
| 16:55–17:25 | (break)                                    |
| 17:25–17:55 | Part 5: Higher-inductive types             |
| 18:00–18:30 | Part 6: Univalence                         |

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

### Part 1: Dependent type theory

#### Lecture

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

#### Exercises

* Given a type family `P : A → B → U`, inhabit the type `(Π (x : A) Σ (y : B) P x y) → Σ (f : A → B) Π (x : A) P x (f x)`.
* Define addition and multiplication on `N` using recursion

### Part 2: Identity types

#### Lecture

* Identity types as path objects
* Path induction
* Iterated identity types
* The action of a map on a path, transport

#### Exercises

* Inahbit the type `Π (u v : A × B) u = v → (fst u = fst v) × (snd u = snd v)`
* Inahbit the type `Π (u v : A × B) (fst u = fst v) × (snd u = snd v) → u = v`
* Given `a b : A` and `p : a = b` inhabit the type `(a, refl a) = (b, p)`
* Can we use path induction to inhabit `Π (x : A) (p : x = x) p = refl x`?


### Part 3: Homotopy levels

#### Lecture

* Contractible spaces
* Propositions, sets, and h-levels
* Truncation as a type-theoretic construction
* The embedding of logic into type theory (using propositional truncation)
* Basic homotopy-theoretic constructions in terms of truncation:
    * loop space vs. fundamental group
    * path-connectedness vs. contractibility
    * surjectivity vs. split epimorphism

#### Exercises

* The difference between `∃`, `∨` and `Σ`, `+`.
* `N` is a set


### Part 4: Equivalences

#### Lecture

* Structure vs. property in mathematics
* Having an inverse is not a property
* Homotopy equivalences
* Example: universal property stated as an equivalence

#### Exercises

* Use equivalence to state the universal property of `×`
* Constructing `Id (A, B) → Equiv (A, B)`



### Part 5: Higher-inductive types

#### Lecture

* Inductive types, examples
* Higher-inductive types (HITs)
* Examples: circle, interval, suspension
* Truncations as HITs

#### Exercises


### Part 6: Univalence

#### Lecture

* The idea that equivalent structures are equal
* Univalence axiom
* Some consequences of the univalence axiom

#### Exercises

* Isomorphic groups are equal
