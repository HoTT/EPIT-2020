{-# OPTIONS --cubical #-}
module SolutionsSession1 where

open import Part1 hiding (B)

variable
  B : A → Type ℓ

-- Solutions to ExerciseSession1

-- Exercise 1:
funExtDep : {f g : (x : A) → B x}
          → ((x : A) → f x ≡ g x)
          → f ≡ g
funExtDep p i x = p x i

-- Exercise 2:
congP : {x y : A} {B : A → Type ℓ'}
        (f : (a : A) → B a) (p : x ≡ y) →
        PathP (λ i → B (p i)) (f x) (f y)
congP f p i = f (p i)

-- Exercise 3:
isContrInhProp : isProp A → A → isContr A
isContrInhProp p x = x , p x


-- We could have stated isProp as follows:
isProp' : Type ℓ → Type ℓ
isProp' A = (x y : A) → isContr (x ≡ y)

-- Exercise 4:
isProp'→isProp : isProp' A → isProp A
isProp'→isProp h = λ x y → h x y .fst

-- Exercise 5:
isPropΠ : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
isPropΠ h p q i x = h x (p x) (q x) i

-- Exercise 6:
funExt⁻ : {f g : (x : A) → B x} → f ≡ g → ((x : A) → f x ≡ g x)
funExt⁻ eq x i = eq i x

-- Exercise 7:
isSetΠ : (h : (x : A) → isSet (B x)) → isSet ((x : A) → B x)
isSetΠ h f g p q i j x = h x (f x) (g x) (funExt⁻ p x) (funExt⁻ q x) i j


-- We could have defined the type of singletons as follows
singl' : {A : Type ℓ} (a : A) → Type ℓ
singl' {A = A} a = Σ[ x ∈ A ] x ≡ a

-- Exercise 8:
isContrSingl' : (x : A) → isContr (singl' x)
isContrSingl' x = ctr , prf
  where
  ctr : singl' x
  ctr = x , refl

  prf : (s : singl' x) → ctr ≡ s
  prf (y , pax) i = (pax (~ i)) , λ j → pax (~ i ∨ j)
