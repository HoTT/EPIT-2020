{-

Part 3: Transport and composition

- Cubical transport
- Subst as a special case of cubical transport
- Path induction from subst?
- Homogeneous composition (hcomp)
- Binary composition of paths as special case of hcomp

-}

{-# OPTIONS --cubical #-}
module Part2 where

open import Part1 public

-- Transport is more complex as ≡ isn't inductively defined (so we
-- can't define it by pattern-matching on p)
transport : {A B : Type ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

-- This lets us define subst (which is called "transport" in the HoTT book)
subst : {A : Type ℓ} (P : A → Type ℓ') {x y : A} (p : x ≡ y) → P x → P y
subst P p pa = transport (λ i → P (p i)) pa

-- The transp operation reduces differently for different types
-- formers. For paths it reduces to another primitive operation called
-- hcomp.

-- We can also define the J eliminator (aka path induction)
-- TODO: rewrite using subst?
-- TODO: talk about ∧
J : {A : Type ℓ} {B : A → Type ℓ'} {x : A}
    (P : (z : A) → x ≡ z → Type ℓ'')
    (d : P x refl) {y : A} (p : x ≡ y) → P y p
J P d p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

-- So J is provable, but it doesn't satisfy computation rule
-- definitionally. This is almost never a problem in practice as the
-- cubical primitives satisfy many new definitional equalities.
