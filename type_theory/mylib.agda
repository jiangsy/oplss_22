{-# OPTIONS --guardedness #-}
{- small library for OOPLS 22 -}

{- products and sums -}

infix 10 _×_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_ public

variable
  A B C : Set

curry : (A × B → C) → (A → B → C)
curry f a b = f (a , b) -- C-c C-,
uncurry : (A → B → C) → (A × B → C)
uncurry f (a , b) = f a b

infix 5 _⊎_
data _⊎_(A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case : (A → C) → (B → C) → (A ⊎ B → C)
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

uncase : (A ⊎ B → C) → (A → C) × (B → C)
uncase f = (λ a → f (inj₁ a)) , λ b → f (inj₂ b)

--case' : (A → C) × (B → C) → (A ⊎ B → C)
--case' = uncurry case

record ⊤ : Set where
  constructor tt

open ⊤ public

data ⊥ : Set where

case⊥ : ⊥ → A
case⊥ ()

data Bool : Set where
  true : Bool
  false : Bool

if_then_else_ : Bool → A → A → A
if true then x else y = x
if false then x else y = y

{- bool logic -}

_&_ : Bool → Bool → Bool
true & y = y
false & y = false

{- ∣ = \mid -}

_∣_ : Bool → Bool → Bool
true ∣ y = true
false ∣ y = y

!_ : Bool → Bool
! true = false
! false = true

_⇒b_ : Bool → Bool → Bool
true ⇒b y = y
false ⇒b y = true

{- prop logic -}

prop = Set

variable
  P Q R : prop

infix 3 _∧_
_∧_ : prop → prop → prop
P ∧ Q = P × Q

infix 2 _∨_
_∨_ : prop → prop → prop
P ∨ Q = P ⊎ Q

infixr 1 _⇒_
_⇒_ : prop → prop → prop
P ⇒ Q = P → Q

False : prop
False = ⊥

True : prop
True = ⊤

¬_ : prop → prop
¬ P = P ⇒ False

infix 0 _⇔_
_⇔_ : prop → prop → prop
P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

efq : False ⇒ P
efq = case⊥

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infix 2 _+_
_+_ : ℕ → (ℕ → ℕ)
zero + n = n
suc m + n = suc (m + n)

infix 4 _*_
_*_ : ℕ → ℕ → ℕ
zero * n = 0
suc m * n = m * n + n

variable M : Set

It-ℕ : M → (M → M) → ℕ → M
It-ℕ m-0 m-S zero = m-0
It-ℕ m-0 m-S (suc n) = m-S (It-ℕ m-0 m-S n)

record Stream (A : Set) : Set where
  constructor _∷_
  coinductive
  field
    head : A
    tail : Stream A

open Stream public

CoIt-Stream : (M → A) → (M → M) → M → Stream A
head (CoIt-Stream m-h m-t m) = m-h m
tail (CoIt-Stream m-h m-t m) =
     CoIt-Stream m-h m-t (m-t m)

{- conatural numbers -}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

record ℕ∞ : Set where
  coinductive
  field
    pred : Maybe ℕ∞

open ℕ∞
zero∞ : ℕ∞
pred zero∞ = nothing

suc∞ : ℕ∞ → ℕ∞
pred (suc∞ n) = just n

∞ : ℕ∞
pred ∞ = just ∞

CoIt-ℕ∞ : (M → Maybe M) → M → ℕ∞
pred (CoIt-ℕ∞ f m) with f m
... | nothing = nothing
... | just m = just (CoIt-ℕ∞ f m)

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred (m +∞ n) with pred m
... | nothing = pred n
... | just m' = just (m' +∞ n)
