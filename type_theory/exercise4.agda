{-# OPTIONS --guardedness #-}
{-
OPLSS 22 : Introduction to Type Theory
Wednesday Exercises
-}

open import mylib

{- Finite Sets -}

variable l m n : ℕ

data Fin : ℕ → Set where
  zero : Fin (suc n)
  suc : Fin n → Fin (suc n)

{- define the following functions on Fin -}

max : {n : ℕ} → Fin (suc n)
max {zero} = zero
max {suc n} = suc (max {n}) -- computes the maximal element of a finite type

emb : {n : ℕ} → Fin n → Fin (suc n)
emb zero = zero
emb (suc n) = suc (emb n) --embeds Fn n into Fin (suc n) without changing the value

rev : {n : ℕ} → Fin n → Fin n
rev zero = max
rev (suc n) = emb (rev n)-- reverse the ordering

{- Isos -}

Π : (A : Set)(B : A → Set) → Set
Π A B = (x : A) → B x

{- A → B = Π A (λ _ → B) -}

record Σ(A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
    
_⊎'_ : Set → Set → Set 
A ⊎' B = Σ Bool AorB
  where AorB : Bool → Set
        AorB true = A
        AorB false = B

_×'_ : Set → Set → Set 
A ×' B = Π Bool AorB
  where AorB : Bool → Set
        AorB true = A
        AorB false = B

{- Construct the functions witnessing isomorphisms
A ⊎' B ≅ A ⊎ B
A ×' B ≅ A × B
You can also prove the isomorphisms but you may need
to assume fun-ext
-}

{- Predicate logic -}


All : (A : Set)(P : A → prop) → prop
All A P = Π A P

Ex : (A : Set)(P : A → prop) → prop
Ex A P = Σ A P

syntax All A (λ x → P)  = ∀[ x ∈ A ] P  
infix 0 All
syntax Ex A (λ x → P) = ∃[ x ∈ A ] P
infix 0 Ex

variable PP QQ : A → prop

taut₁ : (∀[ x ∈ A ] (PP x ∧ QQ x)) ⇔ (∀[ x ∈ A ] PP x) ∧ (∀[ x ∈ A ] QQ x)
proj₁ taut₁ ∀px∧qx = (\ x -> proj₁ (∀px∧qx x)) , (\ x -> proj₂ (∀px∧qx x))
proj₂ taut₁ ∀px∧∀qx = \ x -> ((proj₁ ∀px∧∀qx) x , (proj₂ ∀px∧∀qx) x)

taut₂ : (∃[ x ∈ A ] (PP x ∧ QQ x)) ⇒ (∃[ x ∈ A ] PP x) ∧ (∃[ x ∈ A ] QQ x)
taut₂ (x , px∧qx) = ( (x , proj₁ px∧qx) , (x , proj₂ px∧qx))

taut₃ : ((∃[ x ∈ A ] PP x) ⇒ R) ⇔ (∀[ x ∈ A ] PP x ⇒ R)
proj₁ taut₃ ex = \x -> \px -> ex (x , px)
proj₂ taut₃ ∀xpx→r = \(x , px) -> ∀xpx→r x px

{- definition of equality and properties -}

infix 0 _≡_

data _≡_ : A → A → Set where
  refl : {a : A} → a ≡ a

-- what are the basic properties of equality?
-- It is an equivalence relation
-- (actually a congruence)

sym : {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q

cong : (f : A → B) → {a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl

{- prove commutativity of addition using pattern matching
   and structural recursion.
   Hint : it is useful to prove some lemmas first
-}

n+0=0 : (n : ℕ) -> n ≡ n + 0
n+0=0 zero = refl
n+0=0 (suc n) = cong suc (n+0=0 n)

sm+n=sn+m : (n m : ℕ) -> n + suc m ≡ suc (n + m)
sm+n=sn+m zero m = refl
sm+n=sn+m (suc n) m = cong suc (sm+n=sn+m n m)

comm : (m n : ℕ) → m + n ≡ n + m
comm zero n = n+0=0 n
comm (suc m) n = trans (cong suc (comm m n)) (sym (sm+n=sn+m n m))

{- coinduction -}

from : ℕ → Stream ℕ
head (from n) = n
tail (from n) = from (suc n)

mapS : (A → B) → Stream A → Stream B
head (mapS f as) = f (head as)
tail (mapS f as) = mapS f (tail as)

postulate
  CoInd : (R : Stream A → Stream A → Set)
          → ({as bs : Stream A} → R as bs
             → ((head as ≡ head bs)
              × (R (tail as) (tail bs))))
          → {as bs : Stream A} → R as bs → as ≡ bs

{- Using CoInd prove the following equation -}

nth-head : ℕ -> Stream A -> A 
nth-head zero s = head s
nth-head (suc n) s = nth-head n (tail s)

nth-head-eq : (n m : ℕ) -> nth-head n (mapS suc (from m)) ≡ nth-head n (from (suc m))
nth-head-eq zero m = refl
nth-head-eq (suc n) m = nth-head-eq n (suc m)

thm : (n : ℕ) → mapS suc (from n) ≡ from (suc n)
thm n = CoInd (\as -> \bs -> Π ℕ (\n -> nth-head n as ≡ nth-head n bs)) (\ x -> x 0 , \n -> x (suc n)) (\m -> nth-head-eq m n)
