{-# OPTIONS --cubical --guardedness #-}
{-
OPLSS 22 : Introduction to Type Theory
Thursday Exercises
-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Data.Nat hiding (pred)

open import friday2


open Stream public

-- prove coinduction for streams

coind : (R : Stream A → Stream A → Set)
       → ({xs ys : Stream A}
           → R xs ys → hd xs ≡ hd ys)
       → ({xs ys : Stream A}
           → R xs ys → R (tl xs) (tl ys))
       → {xs ys : Stream A} → R xs ys → xs ≡ ys
hd (coind r rxy→hx≡hy rxy→rtxty rxy i) = rxy→hx≡hy rxy i
tl (coind r rxy→hx≡hy rxy→rtxty rxy i) = coind r rxy→hx≡hy rxy→rtxty (rxy→rtxty rxy) i

{- HITs -}

{- We can define ℤ has a HIT: -}

data ℤ : Set where
  zero : ℤ
  succ : ℤ → ℤ
  pred : ℤ → ℤ
  predsucc : ∀ {i} → pred (succ i) ≡ i
  succpred : ∀ {i} → succ (pred i) ≡ i
  isSetℤ : (x y : ℤ)(p q : x ≡ y) → p ≡ q

{- Derive addition for ℤ -}

_+ℤ_ : ℤ → ℤ → ℤ
zero +ℤ y = y
succ x +ℤ y = succ (x +ℤ y)
pred x +ℤ y = pred (x +ℤ y)
predsucc {x} i +ℤ y = predsucc {x +ℤ y} i
succpred {x} i +ℤ y = succpred {x +ℤ y} i
-- helped by trebor
isSetℤ x x′ p q i i′ +ℤ y = isSetℤ (x +ℤ y) (x′ +ℤ y) (\u -> p u +ℤ y) (\u -> q u +ℤ y)i i′