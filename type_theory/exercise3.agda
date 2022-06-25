{-# OPTIONS --guardedness #-}
{-
OPLSS 22 : Introduction to Type Theory
Wednesday Exercises
-}

open import mylib4

{-
_*_ : ℕ → ℕ → ℕ
zero * n = 0
suc m * n = m * n + n

fac : ℕ → ℕ
fac zero = 1
fac (suc n) = (suc n) * fac n
-}

{- Define both functions using only the iterator It-ℕ -}

_∘_ : (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

_*-it_ : ℕ → ℕ → ℕ
_*-it_ = It-ℕ (\ n -> zero) \ m* n -> n + m* n

fac-it-aux : ℕ -> ℕ × ℕ
fac-it-aux = It-ℕ (1 , 0) (\ x -> ((proj₁ x) *-it suc (proj₂ x)) , suc (proj₂ x))

fac-it : ℕ → ℕ
fac-it = proj₁ ∘ fac-it-aux

{-
from : ℕ → Stream ℕ
head (from n) = n
tail (from n) = from (suc n)

mapS : (A → B) → Stream A → Stream B
head (mapS f as) = f (head as)
tail (mapS f as) = mapS f (tail as)

-}


{-
Define these functions only using CoIt-Stream
-}


from-co : ℕ → Stream ℕ
from-co = CoIt-Stream (\n -> n) suc

mapS-co : (A → B) → Stream A → Stream B
mapS-co f = CoIt-Stream (f ∘ Stream.head) Stream.tail

{-
_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred (m +∞ n) with pred m
... | nothing = pred n
... | just m' = just (m' +∞ n)
-}

{-
Define this functions using only CoIt-ℕ
CoIt-ℕ∞ : (M → Maybe M) → M → ℕ∞
pred (CoIt-ℕ∞ f m) with f m
... | nothing = nothing
... | just m = just (CoIt-ℕ∞ f m)

-}

CoRℕ∞ : {W : Set} → (W → ℕ∞ ⊎ Maybe W) → W → ℕ∞
ℕ∞.pred (CoRℕ∞ {W} g s) with (g s)
... | inj₁ n = just n
... | inj₂ nothing = nothing
... | inj₂ (just s') = just (CoRℕ∞ g s')

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x           


-- let m be a function type 
_+∞-co_ : ℕ∞ → ℕ∞ → ℕ∞
m +∞-co n = CoIt-ℕ∞  (\ (m , n) -> 
    case ℕ∞.pred m of 
    \ { nothing -> case ℕ∞.pred n of 
        \ { nothing  -> nothing
           ; (just n') -> just (m , n')
          }
      ; (just m') -> just (m' , n)
    }
    ) (m , n)
{-
Define multiplication for conatural numbers
using copattern matching and guarded corecursion.
-}

_*∞_∘_ : ℕ∞ → ℕ∞ -> ℕ∞  → ℕ∞
ℕ∞.pred (m *∞ acc ∘ n) with ℕ∞.pred m
... | nothing = ℕ∞.pred acc
... | just m' = just (m' *∞ (n +∞ acc) ∘ n)

-- _*∞_∘_ actually computes m + m * n, so we call it with m * (n - 1)
_*∞_ : ℕ∞ → ℕ∞ → ℕ∞
m *∞ n with ℕ∞.pred n 
... | nothing = zero∞
... | just n-1 = m *∞ zero∞ ∘ n-1

2∞ : ℕ∞
2∞ = suc∞ (suc∞ zero∞)

3∞ : ℕ∞
3∞ = suc∞ 2∞

4∞ : ℕ∞
4∞ = suc∞ 3∞

{-# NON_TERMINATING #-}
ℕ∞->ℕ : ℕ∞ -> ℕ
ℕ∞->ℕ n* with ℕ∞.pred n*
... | nothing = 0
... | just x = suc (ℕ∞->ℕ x)

8∞ = 2∞ *∞ 4∞

6∞ = 2∞ +∞-co 4∞ 