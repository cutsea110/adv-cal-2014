module test where

open import Data.List hiding (filter; drop)
open import Data.Nat hiding (_<_)
open import Data.Bool

_<_ : ℕ → ℕ → Bool
zero < zero = false
zero < suc y = true
suc x < zero = false
suc x < suc y = x < y

min : ℕ → ℕ → ℕ
min x y with x < y
min x y | true = x
min x y | false = y

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
filter p (x ∷ xs) | true = x ∷ filter p xs
filter p (x ∷ xs) | false = filter p xs

infix 20 _⊆_
data _⊆_ {A : Set} : List A → List A → Set where
  stop : [] ⊆ []
  drop : ∀ {xs x ys} → xs ⊆ ys → xs ⊆ (x ∷ ys)
  keep : ∀ {xs x ys} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)

lem-filter : {A : Set}(p : A → Bool)(xs : List A) → filter p xs ⊆ xs
lem-filter p [] = stop
lem-filter p (x ∷ xs) with p x
lem-filter p (x ∷ xs) | true = keep (lem-filter p xs)
lem-filter p (x ∷ xs) | false = drop (lem-filter p xs)

data _==_ {A : Set}(x : A) : A → Set where
  refl : x == x

lem-plus-zero : (n : ℕ) → (n + zero) == n
lem-plus-zero zero = refl
lem-plus-zero (suc n) with n + zero | lem-plus-zero n
lem-plus-zero (suc n) | .n | refl = refl
