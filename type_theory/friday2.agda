{-# OPTIONS --cubical --guardedness #-}
{-
OPLSS 22 : Introduction to Type Theory (5-2)
-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Data.Nat hiding (pred)

record Stream (A : Set) : Set where
  constructor _∷_
  coinductive
  field
    hd : A
    tl : Stream A

open Stream public

from : ℕ → Stream ℕ
hd (from n) = n
tl (from n) = from (suc n)

mapStream : {A B : Set} → (A → B) → Stream A → Stream B
hd (mapStream f xs) = f (hd xs)
tl (mapStream f xs) = mapStream f (tl xs)

{-
I -- the interval, [i0 .. i1]
equality is path
a b : A, p : a ≡ b
p : I → A, p i0 = a, p i1 = b
-}

variable A B : Set

refl' : (a : A) → a ≡ a
refl' a i = a

fun-ext : (f g : A → B) → ((a : A) → f a ≡ g a) → f ≡ g
fun-ext f g p i a = p a i

lemma : (n : ℕ) → mapStream suc (from n) ≡ from (suc n)
hd (lemma n i) = suc n
tl (lemma n i) = lemma (suc n) i

{-
duality:
proof by induction
=> pattern matching and structural recursion
proof by coinduction
=> copattern matching and guarded corecursion
-}

trans : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans {a = a} {b = b} {c = c} p q i =
      hcomp (λ j → λ { (i = i0) → a
                     ; (i = i1) → q j }) (p i)

-- hcomp , transp (comp)
-- univalence: glue type => univalence
-- HITs (generalisation of quotient types)

-- cubical type theory close model
-- higher observational type theory (w Kaposi, Shulmann)

