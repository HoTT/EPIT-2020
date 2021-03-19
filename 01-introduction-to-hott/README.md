# Introduction to homotopy type theory

Lecturer: [Andrej Bauer](http://www.andrej.com/)

## Schedule

The online lectures will take place on Monday, April 12, 2021.
All times are in UTC+2.

| Time        | Topic                                      |
|:=-----------|:-------------------------------------------|
| 14:00–14:30 | Part 1: Dependent type theory              |
| 14:30–15:00 | Part 2: Dependent sums and products        |
| 15:30–16:00 | (break)                                    |
| 16:00–16:30 | Part 3: Identity types                     |
| 16:30–17:00 | Part 4: Homotopy levels                    |
| 17:00–17:30 | (break)                                    |
| 17:30–18:00 | Part 5: Equivalences & isomorphism         |
| 18:00–18:30 | Part 6: Univalence                         |

## Contents

### Part 1: Dependent type theory

#### Lecture

* Type theory as a theory of constructions
* Geometric picture of types and type families
* The type-theoretic judgements: contexts, types, terms, judgemental equality
* Inference rules
* Types as elements of a universe

#### Exercises

* Discuss the rules for `unit`, `empty`, `bool`.
* Discuss the rules for `ℕ`


### Part 2: Dependent sums and products

#### Lecture

* Dependent sum `Σ`
* Dependent product `Π`
* Function type `→` and product type `×`

#### Exercises

* Dependent currying
* Formulate the types for `+`

### Part 3: Identity types

#### Lecture

* Identity type as a type of paths
* Path induction
* Why we cannot prove UIP by path induction
* Basic properties of identity types, including transport

#### Exercises

* Inhabitation of `Π (u : Σ (x : A) Id (x, y)) Id ((x, refl x), u)`


### Part 4: Homotopy levels

#### Lecture

* Contractible type
* Proposition
* Propositional truncation
* Structure versus property
* The idea of homotopy level

#### Exercises

* The difference between `∃`, `∨` and `Σ`, `+`.
* `N` is a set

### Part 5: Equivalences & isomorphism

#### Lecture

* Equivalence of types
* Being an equivalence is a property
* Use equivalence to state the universal property of pullback

#### Exercises

* Use equivalence to state the universal property of `×`
* Constructing `Id (A, B) → Equiv (A, B)`

### Part 6: Univalence

#### Lecture

* Analying the structure of `Id`
* The statement of Univalence
* Consequences of Univalence: function extensionality

#### Exercises

* Isomorphic groups are equal
