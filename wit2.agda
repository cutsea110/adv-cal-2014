module wit2 where

-- parameter vs indices

open import Data.Bool hiding (_<_; _≤_)
open import Data.Nat using (ℕ; zero; suc)

-- parameter
data P (A : Set) : Set where
  scon : P A  -- A is visible
  bcon : Bool → P A
  ncon : ℕ → P A

-- indices
data I : (A : Set) → Set where
--  scon : I A -- A is invisible
  bcon : I Bool
  ncon : I ℕ

-- examples
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data Fin : (n : ℕ) → Set where
  zero : ∀ {n} → Fin (suc n)
  succ : ∀ {n} → Fin n → Fin (suc n)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  m≤n : ∀ {m n} → m ≤ n → suc m ≤ suc n

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

record Test : Set where
  open import Data.Empty

  f : Fin 0 → ⊥
  f ()

  f' : Fin 1 → ⊥
  f' zero = {!!}
  f' (succ ())

  f'' : Fin 2 → ⊥
  f'' zero = {!!}
  f'' (succ zero) = {!!}
  f'' (succ (succ ()))

  f''' : Fin 3 → ⊥
  f''' zero = {!!}
  f''' (succ zero) = {!!}
  f''' (succ (succ zero)) = {!!}
  f''' (succ (succ (succ ())))

  g : 0 ≤ 1 → ⊥
  g z≤n = {!!}

  g' : 0 ≤ 2 → ⊥
  g' z≤n = {!!}

  g'' : 1 ≤ 3 → ⊥
  g'' (m≤n z≤n) = {!!}
