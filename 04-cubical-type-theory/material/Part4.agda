{-

Part 4: Higher inductive types

- Set quotients via HITs
- Propositional truncation
- A little synthetic homotopy theory

-}

{-# OPTIONS --cubical #-}
module Part4 where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Prod hiding (map)

open import Part1
open import Part2
open import Part3

-- Another thing that Cubical Agda adds is the possibility to define
-- higher inductive types. These are just like normal Agda datatypes,
-- but they have also "higher" constructors specifying non-trivial
 -- paths, square, cubes, etc. in a type. These give a nice way of
-- defining set quotiented types as well as higher dimensional types
-- quotiented by some relations.

-- The following definition of finite multisets is due to Vikraman
-- Choudhury and Marcelo Fiore.

infixr 5 _∷_

data FMSet (A : Type ℓ) : Type ℓ where
  [] : FMSet A
  _∷_ : (x : A) → (xs : FMSet A) → FMSet A
  comm : (x y : A) (xs : FMSet A) → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : (xs ys : FMSet A) (p q : xs ≡ ys) → p ≡ q

infixr 30 _++_

_++_ : ∀ (xs ys : FMSet A) → FMSet A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys
comm x y xs i ++ ys = comm x y (xs ++ ys) i
trunc xs zs p q i j ++ ys =
  trunc (xs ++ ys) (zs ++ ys) (λ k → p k ++ ys) (λ k → q k ++ ys) i j

unitl-++ : (xs : FMSet A) → [] ++ xs ≡ xs
unitl-++ xs = refl

unitr-++ : (xs : FMSet A) → xs ++ [] ≡ xs
unitr-++ [] = refl
unitr-++ (x ∷ xs) = cong (x ∷_) (unitr-++ xs)
unitr-++ (comm x y xs i) j = comm x y (unitr-++ xs j) i
unitr-++ (trunc xs ys p q i k) j =
  trunc (unitr-++ xs j) (unitr-++ ys j)
        (λ k → unitr-++ (p k) j) (λ k → unitr-++ (q k) j) i k


-- Filling the goals for comm and trunc quickly gets tiresome and
-- useful lemmas are proved in Cubical.HITs.FiniteMultiset. The idea
-- is to prove a general lemma about eliminating into propositions. As
-- we're proving an equality of a set truncated type we can prove the
-- trunc and comm cases once and for all so that we only have to give
-- cases for [] and _∷_. This is a very common pattern when working
-- with set truncated HITs: first define the HIT, then prove special
-- purpose recursors and eliminators for eliminating into types of
-- different h-levels. All definitions are then written using these
-- recursors and eliminators and one get very short proofs.


-- A more efficient version of finite multisets based on association
-- lists open import Cubical.HITs.AssocList.Base

data AssocList (A : Type ℓ) : Type ℓ where
  ⟨⟩ : AssocList A
  ⟨_,_⟩∷_ : (a : A) (n : ℕ) (xs : AssocList A) → AssocList A
  per : (a b : A) (m n : ℕ) (xs : AssocList A)
      → ⟨ a , m ⟩∷ ⟨ b , n ⟩∷ xs ≡ ⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs
  agg : (a : A) (m n : ℕ) (xs : AssocList A)
      → ⟨ a , m ⟩∷ ⟨ a , n ⟩∷ xs ≡ ⟨ a , m + n ⟩∷ xs
  del : (a : A) (xs : AssocList A) → ⟨ a , 0 ⟩∷ xs ≡ xs
  trunc : (xs ys : AssocList A) (p q : xs ≡ ys) → p ≡ q

-- Programming and proving is more complicated with AssocList compared
-- to FMSet. This kind of example occurs everywhere in programming and
-- mathematics: one representation is easier to work with, but not
-- efficient, while another is efficient but difficult to work with.
-- Using the SIP we can get the best of both worlds.

-- Another nice example of a HITs in CS can be found in
-- Cubical.Data.Queue where we define a Queue datastructure based on
-- two lists as a HIT. These examples are all special cases of set
-- quotients. Very useful for programming and set level mathematics.
-- We can define the general form as:

data _/_ (A : Type ℓ) (R : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  [_] : A → A / R
  eq/ : (a b : A) → R a b → [ a ] ≡ [ b ]
  trunc : (a b : A / R) (p q : a ≡ b) → p ≡ q

-- It's sometimes easier to work directly with _/_ instead of defining
-- special HITs as one can reuse lemmas for _/_ instead of reproving
-- things. For example general lemmas about eliminating into
-- propositions have already been proved for _/_.

-- Proving that _/_ is "effective", i.e. that
--
--    ((a b : A) → [ a ] ≡ [ b ] → R a b)
--
-- requires univalence for propositions (hPropExt).

-- Set quotients let us define things like in normal math:
ℤ : Type₀
ℤ = (ℕ × ℕ) / rel
  where
  rel : (ℕ × ℕ) → (ℕ × ℕ) → Type₀
  rel (x₀ , y₀) (x₁ , y₁) = x₀ + y₁ ≡ x₁ + y₀


-- Another useful class of HITs are truncations, especially
-- propositional truncation:

data ∥_∥ (A : Type ℓ) : Type ℓ where
  ∣_∣ : A → ∥ A ∥
  squash : ∀ (x y : ∥ A ∥) → x ≡ y

-- This lets us define mere existence:
∃ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃ A B = ∥ Σ A B ∥
-- Very useful to specify things where existence is weaker than Σ.
-- This lets us define things like surjective functions or the image
-- of a map.

-- We can define the recursor by pattern-matching
rec : {P : Type ℓ} → isProp P → (A → P) → ∥ A ∥ → P
rec Pprop f ∣ x ∣ = f x
rec Pprop f (squash x y i) = Pprop (rec Pprop f x) (rec Pprop f y) i

-- And the eliminator then follows easily:
elim : {P : ∥ A ∥ → Type ℓ} → ((a : ∥ A ∥) → isProp (P a)) →
       ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
elim {P = P} Pprop f a =
  rec (Pprop a) (λ x → transport (λ i → P (squash ∣ x ∣ a i)) (f x)) a

-- A very important point is that propositional truncation is proof
-- relevant, so even though the elements are all equal one can still
-- extract interesting information from them. A fun example is the
-- "cost monad" which can be found in Cubical.HITs.Cost. There we pair
-- A with ∥ ℕ ∥ and use the truncated number to count the number of
-- recursive calls in functions. As the number is truncated it doesn't
-- affect any properties of the functions, but by running concrete
-- computations we can extract the number of calls.


-------------------------------------------------------------------------
-- Another source of HITs are inspired by topology

-- We can define the circle as the following simple data declaration:
data S¹ : Type₀ where
  base : S¹
  loop : base ≡ base

-- We can write functions on S¹ using pattern-matching equations:
double : S¹ → S¹
double base = base
double (loop i) = (loop ∙ loop) i

helix : S¹ → Type₀
helix base     = Int
helix (loop i) = sucPathInt i

ΩS¹ : Type₀
ΩS¹ = base ≡ base

winding : ΩS¹ → Int
winding p = subst helix p (pos 0)

_ : winding (λ i → double ((loop ∙ loop) i)) ≡ pos 4
_ = refl

-- We can in fact prove that this is an equivalence, this relies on
-- the encode-decode method and Egbert will go through the proof in
-- detail. For details about how this proof looks in Cubical Agda see:
--
--   Cubical.HITs.S1.Base

-- Complex multiplication on S¹, used in the Hopf fibration
_⋆_ : S¹ → S¹ → S¹
base   ⋆ x = x
loop i ⋆ base = loop i
loop i ⋆ loop j =
  hcomp (λ k → λ { (i = i0) → loop (j ∨ ~ k)
                 ; (i = i1) → loop (j ∧ k)
                 ; (j = i0) → loop (i ∨ ~ k)
                 ; (j = i1) → loop (i ∧ k) })
        base

-- We can define the Torus as:
data Torus : Type₀ where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2

-- The square corresponds to the normal folding diagram

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
Torus≡S¹×S¹ = isoToPath (iso t2c c2t t2c-c2t c2t-t2c)

-- We can also directly compute winding numbers on the torus
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
-- open import Cubical.HITs.Wedge
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

