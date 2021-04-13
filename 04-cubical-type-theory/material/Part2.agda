{-

Part 2: The interval and path types

    The interval in Cubical Agda
    Path and PathP types
    Function extensionality
    Equality in Σ-types

-}


-- To make Agda cubical add the following options
{-# OPTIONS --cubical #-}
module Part2 where

-- The "Foundations" package contain a lot of important results (in
-- particular the univalence theorem)
open import Cubical.Foundations.Prelude


-- The interval in Cubical Agda is written I and the endpoints i0 and i1.

apply0 : (A : Type) (p : I → A) → A
apply0 A p = p i0

-- We omit the universe level ℓ for simplicity in this talk. In the
-- library everything is maximally universe polymorphic.


-- We can write functions out of the interval using λ-abstraction:
refl' : {A : Type} (x : A) → x ≡ x
refl' x = λ i → x
-- In fact, x ≡ y is short for PathP (λ _ → A) x y

refl'' : {A : Type} (x : A) → PathP (λ _ → A) x x
refl'' x = λ _ → x

-- In general PathP A x y has A : I → Type, x : A i0 and y : A i1
-- PathP = Dependent paths (Path over a Path)

-- We cannot pattern-match on interval variables as I is not inductively defined
-- foo : {A : Type} → I → A
-- foo r = {!r!}   -- Try typing C-c C-c

-- cong has a direct proof
cong' : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong' f p i = f (p i)

-- function extensionality also has a direct proof.
-- It also has computational content: swap the arguments.
funExt' : {A B : Type} {f g : A → B} (p : (x : A) → f x ≡ g x) → f ≡ g
funExt' p i x = p x i
