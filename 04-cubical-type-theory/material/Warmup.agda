-- Some very simple problems just to test that things work properly.
-- Solutions to all problems is written at the bottom of the file.
{-# OPTIONS --cubical #-}
module Warmup where

open import Part1

variable
  A B C : Type ℓ

-- Cong/ap satisfies a lot of nice equations:

congRefl : (f : A → B) {x : A} → cong f (refl {x = x}) ≡ refl
congRefl f = {!!}

congId : {x y : A} (p : x ≡ y) → cong id p ≡ p
congId p = {!!}

_∘_ : (g : B → C) (f : A → B) → A → C
(g ∘ f) x = g (f x)

congComp : (f : A → B) (g : B → C) {x y : A} (p : x ≡ y) →
           cong (g ∘ f) p ≡ cong g (cong f p)
congComp f g x = {!!}


-- Sym is an involution:

symInv : {x y : A} (p : x ≡ y) → sym (sym p) ≡ p
symInv p = {!!}





































-- Solution: replace all holes by refl
