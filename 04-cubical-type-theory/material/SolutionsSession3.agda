-- Solutions to ExerciseSession3
{-# OPTIONS --cubical #-}
module SolutionsSession3 where

open import Part1
open import Part2
open import Part3
open import Part4 hiding (ℤ')
open import ExerciseSession1 hiding (B)

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Int hiding (neg)

-- Exercise 1
assoc-++ : (xs ys zs : FMSet A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc-++ []       ys zs = refl
assoc-++ (x ∷ xs) ys zs j = x ∷ assoc-++ xs ys zs j
assoc-++ (comm x y xs i) ys zs j = comm x y (assoc-++ xs ys zs j) i
assoc-++ (trunc xs xs' p q i k) ys zs j =
  trunc (assoc-++ xs ys zs j) (assoc-++ xs' ys zs j)
        (λ l → assoc-++ (p l) ys zs j)
        (λ l → assoc-++ (q l) ys zs j) i k

-- Exercise 2
data ℤ' : Type₀ where
  pos    : (n : ℕ) → ℤ'
  neg    : (n : ℕ) → ℤ'
  posneg : pos 0 ≡ neg 0

-- Exercise 3
ℤ→ℤ' : ℤ → ℤ'
ℤ→ℤ' (pos n) = pos n
ℤ→ℤ' (negsuc n) = neg (suc n)

ℤ'→ℤ : ℤ' → ℤ
ℤ'→ℤ (pos n) = pos n
ℤ'→ℤ (neg zero) = pos 0
ℤ'→ℤ (neg (suc n)) = negsuc n
ℤ'→ℤ (posneg _) = pos 0

ℤ'→ℤ→ℤ' : ∀ (n : ℤ') → ℤ→ℤ' (ℤ'→ℤ n) ≡ n
ℤ'→ℤ→ℤ' (pos n) _       = pos n
ℤ'→ℤ→ℤ' (neg zero) i    = posneg i
ℤ'→ℤ→ℤ' (neg (suc n)) _ = neg (suc n)
ℤ'→ℤ→ℤ' (posneg j) i    = posneg (j ∧ i)

ℤ→ℤ'→ℤ : ∀ (n : ℤ) → ℤ'→ℤ (ℤ→ℤ' n) ≡ n
ℤ→ℤ'→ℤ (pos n) _ = pos n
ℤ→ℤ'→ℤ (negsuc n) _ = negsuc n

ℤ≡ℤ' : ℤ ≡ ℤ'
ℤ≡ℤ' = isoToPath (iso ℤ→ℤ' ℤ'→ℤ ℤ'→ℤ→ℤ' ℤ→ℤ'→ℤ)

isSetℤ' : isSet ℤ'
isSetℤ' = subst isSet ℤ≡ℤ' isSetℤ

-- Exercise 4
isSurjection : (A → B) → Type _
isSurjection {A = A} {B = B} f = (b : B) → ∃ A (λ a → f a ≡ b)

isPropIsSurjection : (f : A → B) → isProp (isSurjection f)
isPropIsSurjection f = isPropΠ (λ _ → squash)

isSurjectionInc : isSurjection {A = A} ∣_∣
isSurjectionInc x = rec squash (λ y → ∣ (y , squash ∣ y ∣ x) ∣) x

-- Exercise 5
intLoop : ℤ → ΩS¹
intLoop (pos zero)       = refl
intLoop (pos (suc n))    = intLoop (pos n) ∙ loop
intLoop (negsuc zero)    = sym loop
intLoop (negsuc (suc n)) = intLoop (negsuc n) ∙ sym loop

windingIntLoop : (n : ℤ) → winding (intLoop n) ≡ n
windingIntLoop (pos zero)       = refl
windingIntLoop (pos (suc n))    = cong sucℤ (windingIntLoop (pos n))
windingIntLoop (negsuc zero)    = refl
windingIntLoop (negsuc (suc n)) = cong predℤ (windingIntLoop (negsuc n))


-- Exercise 6

data Susp (A : Type ℓ) : Type ℓ where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south

SuspBool→S¹ : Susp Bool → S¹
SuspBool→S¹ north = base
SuspBool→S¹ south = base
SuspBool→S¹ (merid false i) = loop i
SuspBool→S¹ (merid true i)  = base

S¹→SuspBool : S¹ → Susp Bool
S¹→SuspBool base     = north
S¹→SuspBool (loop i) = (merid false ∙ sym (merid true)) i

SuspBool→S¹→SuspBool : (x : Susp Bool) → Path _ (S¹→SuspBool (SuspBool→S¹ x)) x
SuspBool→S¹→SuspBool north = refl
SuspBool→S¹→SuspBool south = merid true
SuspBool→S¹→SuspBool (merid false i) j = hcomp (λ k → (λ { (j = i1) → merid false i
                                                         ; (i = i0) → north
                                                         ; (i = i1) → merid true (j ∨ ~ k)}))
                                               (merid false i)
SuspBool→S¹→SuspBool (merid true i) j = merid true (i ∧ j)

S¹→SuspBool→S¹ : (x : S¹) → SuspBool→S¹ (S¹→SuspBool x) ≡ x
S¹→SuspBool→S¹ base       = refl
S¹→SuspBool→S¹ (loop i) j = hfill (λ k → λ { (i = i0) → base
                                           ; (i = i1) → base })
                                  (inS (loop i)) (~ j)

S¹≡SuspBool : S¹ ≡ Susp Bool
S¹≡SuspBool = isoToPath (iso S¹→SuspBool SuspBool→S¹ SuspBool→S¹→SuspBool S¹→SuspBool→S¹)
