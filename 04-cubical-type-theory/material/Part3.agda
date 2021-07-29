{-

Part 3: Univalence and the SIP

• Univalence from ua and uaβ
• Transporting with ua
• The SIP as a consequence of ua

-}
{-# OPTIONS --cubical #-}
module Part3 where

open import Cubical.Core.Glue public
  using ( Glue ; glue ; unglue ; lineToEquiv )

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Part1
open import Part2

-- A key concept in HoTT/UF is univalence. As we have seen earlier in
-- the week this is assumed as an axiom in HoTT. In Cubical Agda it is
-- instead provable and has computational content. This means that
-- transporting with paths constructed using univalence reduces as
-- opposed to HoTT where they would be stuck. This simplifies some
-- proofs and make it possible to actually do concrete computations
-- using univalence.

-- The part of univalence which is most useful for our applications is
-- to be able to turn equivalences (written _≃_ and defined as a Σ-type
-- of a function and a proof that it has contractible fibers) into
-- paths:
ua : {A B : Type ℓ} → A ≃ B → A ≡ B
ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                   ; (i = i1) → (B , idEquiv B) })

-- This term is defined using "Glue types" which were introduced in
-- the CCHM paper. We won't have time to go into details about them
-- today, but for practical applications one can usually forget about
-- them and use ua as a black box. There are multiple useful lemmas in
-- Cubical.Foundations.Univalence and Cubical.Foundations.Transport
-- which are helpful when reasoning about ua which don't require
-- knowing what Glue types are.

-- The important point is that transporting along the path constructed
-- using ua applies the function underlying the equivalence. This is
-- easily proved using transportRefl:
uaβ : (e : A ≃ B) (x : A) → transport (ua e) x ≡ fst e x
uaβ e x = transportRefl (equivFun e x)

-- Note that for concrete types this typically hold definitionally,
-- but for an arbitrary equivalence e we have to prove it.

-- The fact that we have both ua and uaβ suffices to be able to prove
-- the standard formulation of univalence. For details see:
--
--   Cubical.Foundations.Univalence

-- The standard way of constructing equivalences is to start with an
-- isomorphism and then improve it into an equivalence. The lemma in
-- the library which does this is
--
--   isoToEquiv : {A B : Type ℓ} → Iso A B → A ≃ B

-- Composing this with ua lets us directly turn isomorphisms into paths:
--
--   isoToPath : {A B : Type ℓ} → Iso A B → A ≡ B



-- Time for an example!

-- Booleans
data Bool : Type₀ where
  false true : Bool

not : Bool → Bool
not false = true
not true  = false

notPath : Bool ≡ Bool
notPath = isoToPath (iso not not rem rem)
  where
  rem : (b : Bool) → not (not b) ≡ b
  rem false = refl
  rem true  = refl

_ : transport notPath true ≡ false
_ = refl


-- Another example, integers:

open import Cubical.Data.Int hiding (_+_)

sucPath : ℤ ≡ ℤ
sucPath = isoToPath (iso sucℤ predℤ sucPred predSuc)

_ : transport sucPath (pos 0) ≡ pos 1
_ = refl

_ : transport (sucPath ∙ sucPath) (pos 0) ≡ pos 2
_ = refl

_ : transport (sym sucPath) (pos 0) ≡ negsuc 0
_ = refl


-------------------------------------------------------------------------
-- The structure identity principle

-- Combining subst and ua lets us transport any structure on A to get
-- a structure on an equivalent type B
substEquiv : (S : Type ℓ → Type ℓ') (e : A ≃ B) → S A → S B
substEquiv S e = subst S (ua e)

-- Example with binary numbers:

open import Cubical.Data.BinNat.BinNat renaming (ℕ≃binnat to ℕ≃Bin ; binnat to Bin)
open import Cubical.Data.Nat

T : Set → Set
T X = Σ[ _+_ ∈ (X → X → X) ] ((x y z : X) → x + (y + z) ≡ (x + y) + z)

TBin : T Bin
TBin = substEquiv T ℕ≃Bin (_+_ , +-assoc)

_+Bin_ : Bin → Bin → Bin
_+Bin_  = fst TBin

+Bin-assoc : (m n o : Bin) → m +Bin (n +Bin o) ≡ (m +Bin n) +Bin o
+Bin-assoc = snd TBin


-- This is however not always what we want as _+Bin_ will translate
-- its input to unary numbers, add, and then translate back. Instead
-- we want to use efficient addition on binary numbers, but get the
-- associativity proof for free. So what we really want is to
-- characterize the equality of T-structured types, i.e. we want a
-- proof that two types equipped with T-structures are equal if there
-- is a T-structure preserving equivalence between them. This is the
-- usual meaning of the *structure identity principle* (SIP). This
-- implies in particular that the type of paths of
-- monoids/groups/rings/R-modules/... is equivalent to the type of
-- monoid/group/ring/R-module/... preserving equivalences.

-- We formalize this and much more using a cubical version of the SIP in:
--
-- Internalizing Representation Independence with Univalence
-- Carlo Angiuli, Evan Cavallo, Anders Mörtberg, Max Zeuner
-- https://arxiv.org/abs/2009.05547
--
-- The binary numbers example with efficient addition is spelled out
-- in detail in Section 2.1.1 of:
--
-- https://www.doi.org/10.1017/S0956796821000034
-- (Can be downloaded from: https://staff.math.su.se/anders.mortberg/papers/cubicalagda2.pdf)
