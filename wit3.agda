module wit3 where

record Endo (A : Set) : Set where
  field
    appEndo : A → A

record Dual (A : Set) : Set where
  field
    getDual : A

record Functor (F : Set₀ → Set₀) : Set₀ where

record Functor₁ (F : Set₀ → Set₀) : Set₁ where
  field
    fmap : ∀ {A B : Set₀} → (A → B) → F A → F B

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data Bool : Set where
  true : Bool
  false : Bool
