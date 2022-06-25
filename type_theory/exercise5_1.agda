{-# OPTIONS --guardedness --type-in-type #-}
{-
OPLSS 22 : Introduction to Type Theory
Thursday Exercises
-}

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import friday 


p-unique : (a : A) -> (x : Σ A (\ x -> x ≡ a)) -> x ≡ (a , refl)
p-unique a (.a , refl) = refl

≡→≃ : (A ≡ B) → (A ≃ B)
≡→≃ refl = (λ a → a) , \b -> (b , refl) , \a≃b -> sym (p-unique b a≃b)

-- complete this function

postulate
  ua : {A B : Set} → isEquiv (≡→≃ {A} {B})
