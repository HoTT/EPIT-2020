{-

Part 3: Transport and composition

- Cubical transport
- Subst as a special case of cubical transport
- Path induction from subst?
- Homogeneous composition (hcomp)
- Binary composition of paths as special case of hcomp

-}

{-# OPTIONS --cubical #-}
module Part3 where

open import Cubical.Foundations.Prelude
open import Part2

-- Transport is more complex as ≡ isn't inductively defined (so we
-- can't define it by pattern-matching on p)
transport' : {A B : Type} → A ≡ B → A → B
transport' p a = transp (λ i → p i) i0 a

-- This lets us define subst (which is called "transport" in the HoTT book)
subst' : {A : Type} (P : A → Type) {x y : A} (p : x ≡ y) → P x → P y
subst' P p pa = transport (λ i → P (p i)) pa

-- The transp operation reduces differently for different types
-- formers. For paths it reduces to another primitive operation called
-- hcomp.

-- We can also define the J eliminator (aka path induction)
J' : {A : Type} {B : A → Type} {x : A}
     (P : (z : A) → x ≡ z → Type)
     (d : P x refl) {y : A} (p : x ≡ y) → P y p
J' P d p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

-- So J is provable, but it doesn't satisfy computation rule
-- definitionally. This is almost never a problem in practice as the
-- cubical primitives satisfy many new definitional equalities.


