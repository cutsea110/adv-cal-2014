module View.Decidability where

open import Data.Nat using (ℕ; zero; suc; pred; _+_; _≤_; s≤s; z≤n; _<_; _>_)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using (const; _$_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; inspect; [_])

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : ¬ A → Dec A

1<2 : Dec (1 < 2)
1<2 = yes (s≤s (s≤s z≤n))

1≡1 : Dec (1 ≡ 1)
1≡1 = yes refl

1≡2 : Dec (1 ≡ 2)
1≡2 = no (λ ())

1>2 : Dec (1 > 2)
1>2 = no ¬1>2
  where
    ¬1>2 : 3 ≤ 1 → ⊥
    ¬1>2 (s≤s ())

_≟_ : (a b : ℕ) → Dec (a ≡ b)
zero ≟ zero = yes refl
zero ≟ suc b = no (λ ())
suc a ≟ zero = no (λ ())
suc a ≟ suc b with a ≟ b
suc a ≟ suc .a | yes refl = yes refl
suc a ≟ suc b | no prf = no (λ x → prf (cong pred x))

_≤?_ : (a b : ℕ) → Dec (a ≤ b)
zero ≤? zero = yes z≤n
zero ≤? suc b = yes z≤n
suc a ≤? zero = no (λ ())
suc a ≤? suc b with a ≤? b
suc a ≤? suc b | yes x = yes (s≤s x)
suc a ≤? suc b | no prf = no (λ x → prf (cong≤-pred a b x))
  where
    cong≤-pred : ∀ a b → suc a ≤ suc b → a ≤ b
    cong≤-pred zero b prf = z≤n
    cong≤-pred (suc a) zero (s≤s ())
    cong≤-pred (suc a) (suc b) (s≤s prf) = prf

⌊_⌋ : {P : Set} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no _ ⌋ = false

decidable : {A : Set} → (p : A → Bool) → (x : A) → Dec (p x ≡ true)
decidable p x with p x
decidable p x | true = yes refl
decidable p x | false = no (λ ())
