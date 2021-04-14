{-# OPTIONS --cubical #-}
module ExerciseSession2 where

open import Part1
open import Part2
open import Part3
open import Part4


    -- (* Construct a point if isContr A → Π (x y : A) . isContr (x = y) *)



isProp→isSet : isProp A → isSet A
isProp→isSet h a b p q j i =
  hcomp (λ k → λ { (i = i0) → h a a k
                 ; (i = i1) → h a b k
                 ; (j = i0) → h a (p i) k
                 ; (j = i1) → h a (q i) k }) a

foo : isProp A → isProp' A
foo h = λ x y → (h x y) , λ q → isProp→isSet h _ _ (h x y) q



-- hProp : {ℓ : Level} → Type (ℓ-suc ℓ)
-- hProp {ℓ = ℓ} = Σ[ A ∈ Type ℓ ] isProp A

-- foo : isContr (Σ[ A ∈ hProp {ℓ = ℓ} ] (fst A))
-- foo = ({!!} , {!!}) , {!!}





-- Σ≡Prop : ((x : A) → isProp (B x)) → {u v : Σ A B}
--        → (p : u .fst ≡ v .fst) → u ≡ v


