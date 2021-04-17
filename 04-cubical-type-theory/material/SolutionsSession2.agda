-- Solutions to ExerciseSession2
{-# OPTIONS --cubical #-}
module SolutionsSession2 where

open import Part1
open import Part2
open import ExerciseSession1

-- Exercise 1
JEq : {x : A} (P : (z : A) → x ≡ z → Type ℓ'')
      (d : P x refl) → J P d refl ≡ d
JEq P p d = transportRefl p d


-- Exercise 2
isContr→isProp : isContr A → isProp A
isContr→isProp (x , p) a b = sym (p a) ∙ p b


-- Exercise 3
isProp→isProp' : isProp A → isProp' A
isProp→isProp' p x y = p x y , isProp→isSet p _ _ (p x y)


-- Exercise 4
isContr→isContr≡ : isContr A → (x y : A) → isContr (x ≡ y)
isContr→isContr≡ h = isProp→isProp' (isContr→isProp h)


-- Exercise 5
fromPathP : {A : I → Type ℓ} {x : A i0} {y : A i1}
          → PathP A x y
          → transport (λ i → A i) x ≡ y
fromPathP {A = A} p i = transp (λ j → A (i ∨ j)) i (p i)


-- The converse is harder to prove so we give it:
toPathP : {A : I → Type ℓ} {x : A i0} {y : A i1}
        → transport (λ i → A i) x ≡ y
        → PathP A x y
toPathP {A = A} {x = x} p i =
  hcomp (λ j → λ { (i = i0) → x
                 ; (i = i1) → p j })
        (transp (λ j → A (i ∧ j)) (~ i) x)


-- Exercise 6
Σ≡Prop : {B : A → Type ℓ'} {u v : Σ A B} (h : (x : A) → isProp (B x))
       → (p : fst u ≡ fst v) → u ≡ v
Σ≡Prop {B = B} {u = u} {v = v} h p =
  ΣPathP (p , toPathP (h _ (transport (λ i → B (p i)) (snd u)) (snd v)))


-- Exercice 7 (thanks Loïc for the slick proof!)
isPropIsContr : isProp (isContr A)
isPropIsContr (c0 , h0) (c1 , h1) j =
  h0 c1 j , λ y i → hcomp (λ k → λ { (i = i0) → h0 (h0 c1 j) k;
                                     (i = i1) → h0 y k;
                                     (j = i0) → h0 (h0 y i) k;
                                     (j = i1) → h0 (h1 y i) k}) c0


-- Exercises about Part 3:

-- Exercise 8 (a bit longer, but very good):

open import Cubical.Data.Nat
open import Cubical.Data.Int hiding (addEq ; subEq)

-- Compose sucPathInt with itself n times. Transporting along this
-- will be addition, transporting with it backwards will be subtraction.

-- a) Define a path "addEq n" by composing sucPathInt with itself n
-- times.
addEq : ℕ → Int ≡ Int
addEq zero = refl
addEq (suc n) = (addEq n) ∙ sucPathInt

-- b) Define another path "subEq n" by composing "sym sucPathInt" with
-- itself n times.
subEq : ℕ → Int ≡ Int
subEq zero = refl
subEq (suc n) = (subEq n) ∙ sym sucPathInt


-- c) Define addition on integers by pattern-matching and transporting
-- along addEq/subEq appropriately.
_+Int_ : Int → Int → Int
m +Int pos n    = transport (addEq n) m
m +Int negsuc n = transport (subEq (suc n)) m

-- d) Do some concrete computations using _+Int_ (this would not work
-- in HoTT as the transport would be stuck!)


-- Exercise 9: prove that hSet is not an hSet

open import Cubical.Data.Bool renaming (notEq to notPath)
open import Cubical.Data.Empty

-- Just define hSets of level 0 for simplicity
hSet : Type₁
hSet = Σ[ A ∈ Type₀ ] isSet A

-- Bool is an hSet
BoolSet : hSet
BoolSet = Bool , isSetBool

notPath≢refl : (notPath ≡ refl) → ⊥
notPath≢refl e = true≢false (transport (λ i → transport (e i) true ≡ false) refl)

¬isSet-hSet : isSet hSet → ⊥
¬isSet-hSet h = notPath≢refl (cong (cong fst) (h BoolSet BoolSet p refl))
 where
 p : BoolSet ≡ BoolSet
 p = Σ≡Prop (λ A → isPropIsSet {A = A}) notPath


-- Exercise 10: squivalence between FinData and Fin

-- Thanks to Elies for the PR with the code. On the development
-- version of the library there is now:
--
-- open import Cubical.Data.Fin using (FinData≡Fin)

