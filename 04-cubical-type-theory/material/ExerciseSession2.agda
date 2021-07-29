-- Exercises for session 2
--
-- If unsure which exercises to do start with those marked with *
--
{-# OPTIONS --cubical --allow-unsolved-metas #-}
module ExerciseSession2 where

open import Part1
open import Part2
open import ExerciseSession1

open import Cubical.Foundations.Equiv

-- Exercises about Part 2:

-- Exercise* 1: prove that the computation rule for J on refl
-- holds up to a path.
-- (hint: normalize the goal using C-u C-u C-c C-,)
JEq : {x : A} (P : (z : A) → x ≡ z → Type ℓ'')
      (d : P x refl) → J P d refl ≡ d
JEq P p d = {!!}


-- Exercise* 2: prove that isContr implies isProp
isContr→isProp : isContr A → isProp A
isContr→isProp = {!!}


-- Exercise 3: prove that isProp implies isProp'
-- (hint: use isProp→isSet from the Part2)
isProp→isProp' : isProp A → isProp' A
isProp→isProp' = {!!}


-- Exercise 4: prove the following lemma
-- (hint: use the solutions to exercises 2 and 3)
isContr→isContr≡ : isContr A → (x y : A) → isContr (x ≡ y)
isContr→isContr≡ = {!!}


-- Exercise 5: use transp to turn a PathP into a transport
fromPathP : {A : I → Type ℓ} {x : A i0} {y : A i1}
          → PathP A x y
          → transport (λ i → A i) x ≡ y
fromPathP {A = A} p i = {!!}


-- The converse is harder to prove so we give it:
toPathP : {A : I → Type ℓ} {x : A i0} {y : A i1}
        → transport (λ i → A i) x ≡ y
        → PathP A x y
toPathP {A = A} {x = x} p i =
  hcomp (λ j → λ { (i = i0) → x
                 ; (i = i1) → p j })
        (transp (λ j → A (i ∧ j)) (~ i) x)


-- Exercise* 6: prove that two Σ-types where the second component is a
-- proposition is equal if the first projections are equal.
-- (hint: use ΣPathP and toPathP)
Σ≡Prop : {B : A → Type ℓ'} {u v : Σ A B} (h : (x : A) → isProp (B x))
       → (p : fst u ≡ fst v) → u ≡ v
Σ≡Prop {B = B} {u = u} {v = v} h p = {!!}

-- Exercice 7 (harder): prove that being contractible is a proposition.
-- (hint: the second component can be given by a suitable higher
-- dimensional hcomp)
isPropIsContr : isProp (isContr A)
isPropIsContr = {!!}




-- Exercises about Part 3:

-- Exercise* 8: compose sucPathInt with itself n times. Transporting
-- along this will be addition, transporting with it backwards will be
-- subtraction.

open import Cubical.Data.Nat
open import Cubical.Data.Int hiding (addEq ; subEq)

-- a) Define a path "addEq n" by composing sucPathInt with itself n times.
addEq : ℕ → ℤ ≡ ℤ
addEq n = {!!}

-- b) Define another path "subEq n" by composing "sym sucPathℤ" with
-- itself n times.
subEq : ℕ → ℤ ≡ ℤ
subEq n = {!!}

-- c) Define addition on integers by pattern-matching and transporting
-- along addEq/subEq appropriately.
_+ℤ_ : ℤ → ℤ → ℤ
m +ℤ n = {!!}

-- d) Do some concrete computations using _+ℤ_ (this would not work
-- in HoTT as the transport would be stuck!)

-- e) Use isEquivTransport from

open import Cubical.Foundations.Transport

-- to prove that +ℤ with a fixed number is an equivalence.
--
-- Note that proving this for the usual _+_ function would be a lot
-- longer, but now we get it for free as addition is defined using
-- transport which we already know is an equivalence.

-- Exercise* 9 (harder): prove that hSet is not a set

-- Let's import Bool instead so that we get it from the library
open import Cubical.Data.Bool renaming (notEq to notPath)

-- The empty type ⊥ (written \bot)
open import Cubical.Data.Empty

-- Just define hSets of level 0 for simplicity
hSet : Type₁
hSet = Σ[ A ∈ Type₀ ] isSet A

-- Bool is an hSet
BoolSet : hSet
BoolSet = Bool , isSetBool

-- (hint: use a suitable nested transport)
notPath≢refl : (notPath ≡ refl) → ⊥
notPath≢refl e = true≢false {!!}

-- (hint: use notPath≢refl and define two elements of BoolSet ≡
-- BoolSet, one based on notPath and one based on refl. Σ≡Prop and
-- isPropIsSet is probably handy)
¬isSet-hSet : isSet hSet → ⊥
¬isSet-hSet h = {!!}



-- Exercise 10 (more work): prove that FinData and Fin are equivalent
-- and hence equal. Transport some functions and proofs between the
-- two.

-- Orderings on ℕ
open import Cubical.Data.Nat.Order

data FinData : ℕ → Type₀ where
  zero : {n : ℕ} → FinData (suc n)
  suc  : {n : ℕ} (i : FinData n) → FinData (suc n)

Fin : ℕ → Type₀
Fin n = Σ[ k ∈ ℕ ] k < n
