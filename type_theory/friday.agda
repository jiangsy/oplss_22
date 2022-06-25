{-# OPTIONS --guardedness --type-in-type #-}
{-
OPLSS 22 : Introduction to Type Theory (5)
-}
open import Relation.Binary.PropositionalEquality
open import Data.Product

variable A B C : Set

{-
Eℕ : (M : ℕ → Set) → M zero
        → ((m : ℕ) → M m → M (suc m))
        → (m : ℕ) → M m

data _≡_ : A → A → Set where
  refl : {a : A} → a ≡ a
-}

-- Eliminator for equality

E≡ : (M : (a b : A) → a ≡ b → Set)
     → ((a : A) → M a a refl )
     → (a b : A)(p : a ≡ b) → M a b p
E≡ M m-r a .a refl = m-r a

-- J by Per Martin-Loef
-- K proposed Thomas Streicher

-- uip : (a b : A)(p q : a ≡ b) → p ≡ q
-- uip = E≡ (λ a b p → (q : a ≡ b) → p ≡ q) {!!}

--uip a .a refl refl = refl

{-
Is uip not derivable from J (E≡) ?
Martin Hofmann & Thomas Streicher
countermodel, groupoid model, types are groupoids
groupoid = category where all morphisms are isomorphisms.
group of ℤ, not all integers are equal
=> uip cannot be provable.
90ies : Ok we need K.
isomorphism of types is equality.
2008 : Valdimir Voevodsky (Field medallist)
algebraic topology,
spaces in the sense of homotopy theory
type theory : univalence principle 
ω-groupoids, ??? 

what is equality of types?

a function f : A → B is an isomorphism if
for all b : B, there is a unique a : A st f a ≡ b
(b : B) → ∃![ a ∈ A ] f a ≡ b

a function f : A → B is an equivalence if 
for all b : B, there is a unique a : A and p : f a ≡ b

a type with exactly one element is called contractible
-}

isContr : Set → Set
isContr A = Σ[ a ∈ A ] ((x : A) → a ≡ x)

-- isContr ⊤

isEquiv : (A → B) → Set
isEquiv {A} {B} f =
  (b : B) → isContr (Σ[ a ∈ A ] (f a ≡ b))

_≃_ : Set → Set → Set
A ≃ B = Σ[ f ∈ (A → B)] (isEquiv f)


-- postulate
--   ua : {A B : Set} → isEquiv (≡→≃ {A} {B})

{-
isomorphic types are equal: binary ℕ = unary ℕ
isomorphic structures are equal
structural properties are stable under isomorphism
category theory: universal properties have unique solutions

the type of hsets

contractible types = -2-types
is-n-type
is-(-2)-type A = isContractible A
is-(n+1)-type A = (a b : A) → is-n-type (a ≡ b)

propositional types = -1-type
isProp A = (a b : A) → a ≡ b

Prop = Set
Prop = HProp = {A : Set | isProp A}

_∨_ , ∃ not closed HProp
propositional truncation
||_|| : Set → Set
isProp || A || - black bag 
P ∨ Q = || P ⊎ Q ||
∃ A P  = || Σ A P ||

HSet = 0-type
= a type whose equality is a propsoition
HSets = ordinary types

HSet = { A : Type | isHSet A }

(Bool ≡ Bool) ≃ (Bool ≃ Bool) = Bool
id , negation

HSet : 1-type (Groupoids)
...

elephant in the room?

Coquand & Team CCHM
cubical sets , constructive model of type theory
with univalence
cubical type theory

-}
