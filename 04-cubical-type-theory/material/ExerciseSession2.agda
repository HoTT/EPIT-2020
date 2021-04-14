{-# OPTIONS --cubical --allow-unsolved-metas #-}
module ExerciseSession2 where

open import Part2
open import ExerciseSession1 hiding (B)

-- Exercise 1 (easy): prove that the computation rule for J on refl
-- holds up to a path.
-- (hint: normalize the goal using C-u C-u C-c C-,)
JEq : {x : A} (P : (z : A) → x ≡ z → Type ℓ'')
      (d : P x refl) → J P d refl ≡ d
JEq P p d = {!!}


-- Exercise 2 (easy): prove that isContr implies isProp
isContr→isProp : isContr A → isProp A
isContr→isProp = {!!}


-- Exercise 3 (easy): prove that isProp implies isProp'
-- (hint: use isProp→isSet from the Part2)
isProp→isProp' : isProp A → isProp' A
isProp→isProp' = {!!}


-- Exercise 4 (easy): prove the following lemma
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


-- Exercise 6: prove that two Σ-types where the second component is a
-- proposition is equal if the first projections are equal.
-- (hint: use ΣPathP and toPathP)
Σ≡Prop : {B : A → Type ℓ'} {u v : Σ A B} (h : (x : A) → isProp (B x))
       → (p : fst u ≡ fst v) → u ≡ v
Σ≡Prop {B = B} {u = u} {v = v} h p = {!!}


-- Exercice 7 (harder): prove that being contractible is a proposition.
-- (hint: the second component can be given by a suitable higher
-- dimensional hcomp)
isPropIsContr : isProp (isContr A)
isPropIsContr z0 z1 j = {!!}
