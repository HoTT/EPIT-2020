{-# OPTIONS --cubical --allow-unsolved-metas #-}
module ExerciseSession3 where

open import Part3
open import Part4
open import ExerciseSession1 hiding (B)

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Int hiding (neg)

-- Exercise 1: prove associativity of _++_ for FMSet.
-- (hint: mimic the proof of unitr-++)

-- Exercise 2: define the integers as a HIT with a pos and neg
-- constructor each taking a natural number as well as a path
-- constructor equating pos 0 and neg 0.

-- Exercise 3 (a little longer, but not very hard): prove that the
-- above definition of the integers is equal to the ones in
-- Cubical.Data.Int. Deduce that they form a set.

-- Exercise 4: we can define the notion of a surjection as:
isSurjection : (A → B) → Type _
isSurjection {A = A} {B = B} f = (b : B) → ∃ A (λ a → f a ≡ b)

-- The exercise is now to:
--
-- a) prove that being a surjection is a proposition
--
-- b) prove that the inclusion ∣_∣ : A → ∥ A ∥ is surjective
--    (hint: use rec for ∥_∥)


-- Exercise 5: define

intLoop : Int → ΩS¹
intLoop = {!!}

-- which given +n return loop^n and given -n returns loop^-n. Then
-- prove that:

windingIntLoop : (n : Int) → winding (intLoop n) ≡ n
windingIntLoop = {!!}

-- (The other direction is much more difficult and relies on the
-- encode-decode method. See Egbert's course on Friday!)


-- Exercise 6 (harder): the suspension of a type can be defined as

data Susp (A : Type ℓ) : Type ℓ where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south

-- Prove that the circle is equal to the suspension of Bool
S¹≡SuspBool : S¹ ≡ Susp Bool
S¹≡SuspBool = {!!}

-- Hint: define maps back and forth and prove that they cancel.



