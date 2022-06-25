{-# OPTIONS --guardedness #-}

{-
OPLSS 22 : Introduction to Type Theory
Tuesday Exercises

Try to prove the following propositions.
Warning: not all of them may be provable!

C-c C-l load
\<=> ⇔
\and ∧
...
\neg ¬

In the shed.
C- C-, see goal and givens
C-c C-, like C-c C-. but also shows the type of your partial solution.
C-c C-SPC  check solution, and remove shed
C-c C-r    refine, use function or do lambdas
C-c C-c    pattern matching (if you give a parameter) or copatternmatching (no par).
-}
open import mylib4

p1 : P ⇔ P ∧ P
proj₁ p1 p = p , p
proj₂ p1 (p , p') = p

p2 : P ∨ ¬ P ⇒ (¬ (P ∧ Q) ⇔ ¬ P ∨ ¬ Q)
proj₁ (p2 (inj₁ p)) ¬pq = inj₂ \q -> ¬pq (p , q)
proj₂ (p2 (inj₁ p)) (inj₁ np) pq = np p
proj₂ (p2 (inj₁ p)) (inj₂ ¬q) = \pq -> ¬q (proj₂ pq)
proj₁ (p2 (inj₂ ¬p)) ¬pq = inj₁ ¬p
proj₂ (p2 (inj₂ ¬p)) ¬p∨¬q pq = ¬p (proj₁ pq)

p3 : ¬ (P ∧ ¬ P)
p3 (p , ¬p) = ¬p p

p4 : ¬ (P ⇔ ¬ P)
p4 (p→¬p , ¬p→p) = p→¬p (¬p→p (\ p -> p→¬p p p)) (¬p→p (\ p -> p→¬p p p)) 

p5 : ¬ ¬ (P ∨ ¬ P)
p5 ¬p∨¬p = ¬p∨¬p (inj₂ \p -> ¬p∨¬p (inj₁ p))

p6 : ¬ P ⇔ ¬ ¬ ¬ P
proj₁ p6 ¬p ¬¬p = ¬¬p ¬p
proj₂ p6 ¬¬¬p p = ¬¬¬p (\ ¬p -> ¬p p)

-- p7 : (¬ ¬ P ⇒ P) ⇒ (P ∨ ¬ P)
-- p7 ¬¬p→p = inj₂ ({!   !})

p8 : (P ∨ ¬ P) ⇒ ¬ ¬ P ⇒ P
p8 (inj₁ p) ¬¬p = p
p8 (inj₂ ¬p) ¬¬p = efq (¬¬p ¬p)
