# The HoTT library in Coq

Lecturer: [Bas Spitters](https://www.cs.au.dk/~spitters/)

## Schedule

The online lectures will take place on Tuesday, April 13, 2021.
All times are in UTC+2.

| Time        | Topic                                         |
|:------------|:----------------------------------------------|
| 14:00–14:45 | Part 1: Introduction to Coq and HoTT          |
| 14:45-15:10 | Exercises                                     |
| 15:10–15:30 | (break)                                       |
| 15:30–16:15 | Part 2: h-Levels, type classes and HITs       |
| 16:15–16:40 | Exercises                                     |
| 16:40–17:00 | (break)                                       |
| 17:00–17:45 | Part 3: Quotients and impredicativity, Axioms |
| 17:45–18:30 | Exercises                                     |

We shall keep a strict schedule. Each block of two parts will consist of a lecture, followed by exercises and a discussion.

# Background reading
On the second day we shall dive deeper into HoTT and, in particular, its formalization in a proof assistant.
We will use the [Coq](coq.inria.fr/) implementation of type theory, and specifically the [HoTT](https://github.com/HoTT/HoTT) library.
There is much [tutorial](https://coq.inria.fr/documentation) material available for Coq.
Andrej Bauers's [video tutorials](http://math.andrej.com/2011/02/22/video-tutorials-for-the-coq-proof-assistant/) 
are perhaps the most accessible. [Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/) can also be useful.

Please make sure you have Coq with the HoTT library [installed](https://github.com/HoTT/EPIT-2020/blob/main/Coq-Playground/README.md).

## Contents

This second lecture series will partially follow the structure of the first lecture, 
but show how to formalize these aspects in HoTT.

### Part 1: Inroduction to Coq and HoTT library
### Part 2: h-Levels, type classes and HITs
### Part 3: Quotients and impredicativity, Axioms

## Exercises
Formalize the Exercises of day 1 using the HoTT library.

Optional exercises: 
- Prove that the truncated logic from day1 (see part2.v) satisfies the (or some) rules of intuitionistic FOL.
- Advanced: Prove that the truncation HIT is equivalent to [impredicative trunction](https://github.com/HoTT/HoTT/blob/master/theories/PropResizing/ImpredicativeTruncation.v). This uses resizing.
- Advanced: Prove the equivalence of [quotients](https://github.com/HoTT/HoTT/blob/master/theories/HIT/quotient.v#L214). This uses resizing.


There are also more advanced challenges in the text.

If you are a beginner, you will learn a lot by finding and replaying the existing lemmas.
More experienced users are encouraged to write the statements and proofs from scratch.
