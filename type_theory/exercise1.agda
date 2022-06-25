{-
OPLSS 22 : Introduction to Type Theory
Monday Exercises
-}

open import Data.Nat -- we are using ℕ for examples.
variable -- we use A B C as variables for Set = Types.
  A B C : Set

{-

1. Checking and reducing λ-terms

We are using the following functions:
-}

add3 : ℕ → ℕ
add3 = λ x → x + 3

tw : (A → A) → A → A
tw = λ f n → f (f n)

{- Consider the term
tw tw add3 1

What is its type and what does it evaluate to?

First use agda to find the answers, using
C-c C-d (deduce type)
C-c C-n (normalize term)

However, to get the points you need to show (in a comment) how to
normalize the term by doing an equational calculation, using only
 
- expansion of definitions
- β-reduction
- arithmetic calculations (e.g. 2 + 1 = 3)

See the lecture files for examples.
-}



{-
2. Constructing functions

Derive functions of the given type using only λ and application. 
If you think there isn't such a function then comment it out.

You can type in your solution into the "shed", that is {..}.
and then ask agda to type check using C-C C-space.
Inside a shed you can use C-C C-, to see the surrent goal and assumptions (variables) you can use.
You can also type in a function and type C-c C-r to use the function and create new sheds for the arguments. 
To type a lambda symbol use \Gl (λ).

Outside a shed C-c C-l (re)loads a file.
For more see the link to the agda manual on moodle.
-}


f1 : (A → B) → (A → A → B)
f1 = \f -> \x -> f

f2 : (A → A → B) → (A → B)
f2 = \f -> \x -> f x x

f3 : A → ((A → B) → B)
f3 = \x -> \f -> f x

-- f4 : ((A → B) → B) → A
-- f4 = \f -> ?

f5 : (A → B) → ((A → C) → C) → ((B → C) → C)
f5 = \f -> \g -> \h -> g (\x -> h (f x))


{-
3. Combinatory Logic (20/100)

Derive a implementations of f1 - f5 using only S, K and show in a
comment how you have come up with your solution.
-}

K : A → B → A
K = λ a b → a

S : (A → B → C) → (A → B) → A → C
S = λ f g x → f x (g x)

I : A → A
I {A} = S K (K {B = A})

{- As an example I derive a combinator version of tw -}

{-
λ f n → f (f n)
= λ f → λ n → f (f n)
= λ f → S (λ n → f) (λ n → f n)
= λ f → S (K f) f
= S (λ f → S (K f)) (λ f → f)
= S (S (λ f → S) (λ f → (K f)) I
= S (S (K S) K) I
-}

tw-c : (A → A) → A → A
tw-c = S (S (K S) K) I

{- Now you do the combinator versions of the functions you have defined in the previous section. 
   Again comment out lines which you thin are impossible.
-}

f1-c : (A → B) → (A → A → B)
f1-c = K


f2-c : (A → A → B) → (A → B)
f2-c = S (S (K S) (S (S (K S) K) (K I))) (K I)

{-
= \f -> \x -> f x x
= \f -> S (\x -> f x) (\x -> x)
= \f -> S (S (\x -> f) (\x -> x)) I
= \f -> S (S (K f) I) I
= S (\f -> S (S (K f) I)) (\f -> I)
= S (?) (K I)

\f -> S (S (K f) I)
= S (\f -> S) (\f -> S (K f) I)
= S (K S) (S (\f -> S (K f)) (K I))
= S (K S) (S (S (\f -> S) (\f -> K f)) (K I))
-}

f3-c : A → ((A → B) → B)
f3-c = S (S (K S) (K I)) K

{-
= \x -> S (\f -> f) (\f -> x)
= \x -> S I (K x)
= S (\x -> S I) (\x -> K x)

S (\x -> S) K

-}

-- f4-c : ((A → B) → B) → A
-- f4-c = {!   !}

f5-c : (A → B) → ((A → C) → C) → ((B → C) → C)
f5-c = S (S (K S) (K (S (K S) K))) (S (K K) (S (K (S (S (K S) K))) K))

{-
\f -> \g -> \h -> g (\x -> h (f x))
= \f -> \g -> \h -> g (S (K h) f)
= \f -> \g -> S (K g) (\h -> S (K h) f)

(\h -> S (K h) f)

S (\h -> S (K h)) (K f)

\f -> \g -> S (K g) ((S (S (K S) K)) (K f))
\f -> S (\g -> S (K g)) (K ((S (S (K S) K)) (K f)))
\f -> S (S (K S) K) (K ((S (S (K S) K)) (K f)))
S (S (S (S (K S) K)))
-}