{-

Part 5: Higher inductive types

- Quotients via HITs
- Propositional truncation for logic?
- CS example using quotients (maybe finite multisets or queues)
- Synthetic homotopy theory (probably Torus = S^1 * S^1, pi_1(S^1) =
  Z, pi_1(Torus) = Z * Z)

-}

{-# OPTIONS --cubical #-}
module Part5 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Int
open import Cubical.Data.Prod

open import Part4


-----------------------------------------------------------------------------
-- Higher inductive types

-- The following definition of finite multisets is due to Vikraman
-- Choudhury and Marcelo Fiore.

infixr 5 _∷_

data FMSet (A : Type) : Type where
  [] : FMSet A
  _∷_ : (x : A) → (xs : FMSet A) → FMSet A
  comm : (x y : A) (xs : FMSet A) → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
--  trunc : (xs ys : FMSet A) (p q : xs ≡ ys) → p ≡ q

-- We need to add the trunc constructor for FMSets to be sets, omitted
-- here for simplicity.

_++_ : ∀ {A : Type} (xs ys : FMSet A) → FMSet A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys
comm x y xs i ++ ys = comm x y (xs ++ ys) i
-- trunc xs zs p q i j ++ ys =
--   trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) i j

unitr-++ : {A : Type} (xs : FMSet A) → xs ++ [] ≡ xs
unitr-++ [] = refl
unitr-++ (x ∷ xs) = cong (x ∷_) (unitr-++ xs)
unitr-++ (comm x y xs i) j = comm x y (unitr-++ xs j) i
-- unitr-++ (trunc xs ys x y i j) = {!!}


-- This is a special case of set quotients! Very useful for
-- programming and set level mathematics

data _/_ (A : Type) (R : A → A → Type) : Type where
  [_] : A → A / R
  eq/ : (a b : A) → R a b → [ a ] ≡ [ b ]
  trunc : (a b : A / R) (p q : a ≡ b) → p ≡ q

-- Proving that they are effective ((a b : A) → [ a ] ≡ [ b ] → R a b)
-- requires univalence for propositions.


-------------------------------------------------------------------------
-- Topological examples of things that are not sets

-- We can define the circle as the following simple data declaration:
data S¹ : Type where
  base : S¹
  loop : base ≡ base

-- We can write functions on S¹ using pattern-matching equations:
double : S¹ → S¹
double base = base
double (loop i) = (loop ∙ loop) i

helix : S¹ → Type
helix base     = Int
helix (loop i) = sucPathInt i

ΩS¹ : Type
ΩS¹ = base ≡ base

winding : ΩS¹ → Int
winding p = subst helix p (pos 0)

_ : winding (λ i → double ((loop ∙ loop) i)) ≡ pos 4
_ = refl


-- We can define the Torus as:
data Torus : Type where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2

-- And prove that it is equivalent to two circle:
t2c : Torus → S¹ × S¹
t2c point        = (base , base)
t2c (line1 i)    = (loop i , base)
t2c (line2 j)    = (base , loop j)
t2c (square i j) = (loop i , loop j)

c2t : S¹ × S¹ → Torus
c2t (base   , base)   = point
c2t (loop i , base)   = line1 i
c2t (base   , loop j) = line2 j
c2t (loop i , loop j) = square i j

c2t-t2c : (t : Torus) → c2t (t2c t) ≡ t
c2t-t2c point        = refl
c2t-t2c (line1 _)    = refl
c2t-t2c (line2 _)    = refl
c2t-t2c (square _ _) = refl

t2c-c2t : (p : S¹ × S¹) → t2c (c2t p) ≡ p
t2c-c2t (base   , base)   = refl
t2c-c2t (base   , loop _) = refl
t2c-c2t (loop _ , base)   = refl
t2c-c2t (loop _ , loop _) = refl

-- Using univalence we get the following equality:
Torus≡S¹×S¹ : Torus ≡ S¹ × S¹
Torus≡S¹×S¹ = isoToPath' (iso t2c c2t t2c-c2t c2t-t2c)


windingTorus : point ≡ point → Int × Int
windingTorus l = ( winding (λ i → proj₁ (t2c (l i)))
                 , winding (λ i → proj₂ (t2c (l i))))

_ : windingTorus (line1 ∙ sym line2) ≡ (pos 1 , negsuc 0)
_ = refl

-- We have many more topological examples, including Klein bottle, RP^n,
-- higher spheres, suspensions, join, wedges, smash product:
open import Cubical.HITs.KleinBottle
open import Cubical.HITs.RPn
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Susp
open import Cubical.HITs.Join
open import Cubical.HITs.Wedge
open import Cubical.HITs.SmashProduct

-- There's also a proof of the "3x3 lemma" for pushouts in less than
-- 200LOC. In HoTT-Agda this took about 3000LOC. For details see:
-- https://github.com/HoTT/HoTT-Agda/tree/master/theorems/homotopy/3x3
open import Cubical.HITs.Pushout

-- We also defined the Hopf fibration and proved that its total space
-- is S³ in about 300LOC:
open import Cubical.HITs.Hopf

-- There is also some integer cohomology:
open import Cubical.ZCohomology.Everything
-- To compute cohomology groups of various spaces we need a bunch of
-- interesting theorems: Freudenthal suspension theorem,
-- Mayer-Vietoris sequence...
open import Cubical.Homotopy.Freudenthal
open import Cubical.ZCohomology.MayerVietorisUnreduced
