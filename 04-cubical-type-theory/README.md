# Cubical Type Theory

Lecturer: [Anders Mörtberg](https://staff.math.su.se/anders.mortberg/)

Installation instructions for Cubical Agda and the agda/cubical library
can be found [here](https://github.com/agda/cubical/blob/master/INSTALL.md).

If you want to use Agda 2.6.1 instead of the latest development version,
you can check out the tag v0.2 of the agda/cubical library.

## Additional material


- [Cubical Methods in Homotopy Type Theory and Univalent Foundations](https://staff.math.su.se/anders.mortberg/papers/cubicalmethods.pdf) - Lecture notes for the 2019 HoTT Summer School. 
- [Cubical Agda: A dependently typed programming language with univalence and higher inductive types](https://www.doi.org/10.1017/S0956796821000034) - Paper about Cubical Agda.

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
