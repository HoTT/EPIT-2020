{-

Part 3: Univalence and the SIP

- Univalence from ua and uaβ
- Transporting with ua (examples: ua not : Bool = Bool, ua suc : Z = Z, ...)
- Subst using ua
- The SIP as a consequence of ua
- Examples of using the SIP for math and programming (algebra, data
  structures, etc.)

-}

{-# OPTIONS --cubical #-}
module Part3 where

open import Cubical.Foundations.Prelude hiding (refl ; transport ; subst)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Int

open import Part2 public


-- Another key concept in HoTT/UF is the Univalence Axiom. In Cubical
-- Agda this is provable, we hence refer to it as the Univalence
-- Theorem.

-- The univalence theorem: equivalences of types give paths of types
ua' : {A B : Type ℓ} → A ≃ B → A ≡ B
ua' = ua

-- Any isomorphism of types gives rise to an equivalence
isoToEquiv' : {A B : Type ℓ} → Iso A B → A ≃ B
isoToEquiv' = isoToEquiv

-- And hence to a path
isoToPath' : {A B : Type ℓ} → Iso A B → A ≡ B
isoToPath' e = ua' (isoToEquiv' e)

-- ua satisfies the following computation rule
-- This suffices to be able to prove the standard formulation of univalence.
uaβ' : {A B : Type ℓ} (e : A ≃ B) (x : A)
     → transport (ua' e) x ≡ fst e x
uaβ' e x = transportRefl (equivFun e x)



-- Time for an example!

-- Booleans
data Bool : Type₀ where
  false true : Bool

not : Bool → Bool
not false = true
not true  = false

notPath : Bool ≡ Bool
notPath = isoToPath' (iso not not rem rem)
  where
  rem : (b : Bool) → not (not b) ≡ b
  rem false = refl
  rem true  = refl

_ : transport notPath true ≡ false
_ = refl


-- Another example, integers:

sucPath : Int ≡ Int
sucPath = isoToPath' (iso sucInt predInt sucPred predSuc)

_ : transport sucPath (pos 0) ≡ pos 1
_ = refl

_ : transport (sucPath ∙ sucPath) (pos 0) ≡ pos 2
_ = refl

_ : transport (sym sucPath) (pos 0) ≡ negsuc 0
_ = refl



-------------------------------------------------------------------------
-- The structure identity principle

-- A more efficient version of finite multisets based on association lists
open import Cubical.HITs.AssocList.Base

-- data AssocList (A : Type) : Type where
--  ⟨⟩ : AssocList A
--  ⟨_,_⟩∷_ : (a : A) (n : ℕ) (xs : AssocList A) → AssocList A
--  per : (a b : A) (m n : ℕ) (xs : AssocList A)
--      → ⟨ a , m ⟩∷ ⟨ b , n ⟩∷ xs ≡ ⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs
--  agg : (a : A) (m n : ℕ) (xs : AssocList A)
--      → ⟨ a , m ⟩∷ ⟨ a , n ⟩∷ xs ≡ ⟨ a , m + n ⟩∷ xs
--  del : (a : A) (xs : AssocList A) → ⟨ a , 0 ⟩∷ xs ≡ xs
--  trunc : (xs ys : AssocList A) (p q : xs ≡ ys) → p ≡ q


-- Programming and proving is more complicated with AssocList compared
-- to FMSet. This kind of example occurs everywhere in programming and
-- mathematics: one representation is easier to work with, but not
-- efficient, while another is efficient but difficult to work with.

-- Solution: substitute using univalence
substIso : {A B : Type ℓ} (P : Type ℓ → Type ℓ') (e : Iso A B) → P A → P B
substIso P e = subst P (isoToPath e)

-- Can transport for example Monoid structure from FMSet to AssocList
-- this way, but the achieved Monoid structure is not very efficient
-- to work with. A better solution is to prove that FMSet and
-- AssocList are equal *as monoids*, but how to do this?

-- Solution: structure identity principle (SIP)
-- This is a very useful consequence of univalence
open import Cubical.Foundations.SIP

{-
sip' : {ℓ : Level} {S : Type ℓ → Type ℓ} {ι : StrEquiv S ℓ}
       (θ : UnivalentStr S ι) (A B : TypeWithStr ℓ S) → A ≃[ ι ] B → A ≡ B
sip' = sip
-}
-- The tricky thing is to prove that (S,ι) is a univalent structure.
-- Luckily we provide automation for this in the library, see for example:
-- open import Cubical.Algebra.Monoid.Base

-- Another cool application of the SIP: matrices represented as
-- functions out of pairs of Fin's and vectors are equal as abelian
-- groups:
open import Cubical.Algebra.Matrix
