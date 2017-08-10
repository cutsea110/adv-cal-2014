module View where

open import Data.Nat using (ℕ; zero; suc; _<_; _>_; s≤s; z≤n; _+_; _*_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Even : ℕ → Set
data Odd : ℕ → Set

data Even where
  zero : Even zero
  odd : ∀ {n} → Odd n → Even (suc n)

data Odd where
  even : ∀ {n} → Even n → Odd (suc n)

parity : ∀ n → Even n ⊎ Odd n
parity zero = inj₁ zero
parity (suc n) with parity n
parity (suc n) | inj₁ x = inj₂ (even x)
parity (suc n) | inj₂ y = inj₁ (odd y)

ordering : ∀ n m → n < m ⊎ n ≡ m ⊎ n > m
ordering zero zero = inj₂ (inj₁ refl)
ordering zero (suc m) = inj₁ (s≤s z≤n)
ordering (suc n) zero = inj₂ (inj₂ (s≤s z≤n))
ordering (suc n) (suc m) with ordering n m
ordering (suc n) (suc m) | inj₁ x = inj₁ (s≤s x)
ordering (suc n) (suc .n) | inj₂ (inj₁ refl) = inj₂ (inj₁ refl)
ordering (suc n) (suc m) | inj₂ (inj₂ y) = inj₂ (inj₂ (s≤s y))

data Parity : ℕ → Set where
  even : ∀ n → Parity (n * 2)
  odd : ∀ n → Parity (1 + n * 2)

parity' : ∀ n → Parity n
parity' zero = even zero
parity' (suc n) with parity' n
parity' (suc .(n * 2)) | even n = odd n
parity' (suc .(suc (n * 2))) | odd n = even (suc n)

data Ordering : ℕ → ℕ → Set where
  less  : ∀ m k → Ordering m (suc (m + k))
  equal : ∀ m   → Ordering m m
  great : ∀ m k → Ordering (suc (m + k)) m

compare : ∀ m n → Ordering m n
compare zero zero = equal zero
compare zero (suc n) = less zero n
compare (suc m) zero = great zero m
compare (suc m) (suc n) with compare m n
compare (suc m) (suc .(suc (m + k))) | less .m k = less (suc m) k
compare (suc m) (suc .m) | equal .m = equal (suc m)
compare (suc .(suc (n + k))) (suc n) | great .n k = great (suc n) k

⌊_/2⌋ : ℕ → ℕ
⌊ n /2⌋ with parity' n
⌊ .(n * 2) /2⌋ | even n = n
⌊ .(suc (n * 2)) /2⌋ | odd n = n

data Quadity : ℕ → Set where
  zero : ∀ k → Quadity (k * 2 * 2)
  one : ∀ k → Quadity (suc (k * 2 * 2))
  two : ∀ k → Quadity (suc (suc (k * 2 * 2)))
  three : ∀ k → Quadity (suc (suc (suc (k * 2 * 2))))

quad : ∀ n → Quadity n
quad n with parity' n
quad .(n * 2) | even n with parity' n
quad .(n * 2 * _) | even .(n * 2) | even n = zero n
quad .(suc (n * 2) * _) | even .(suc (n * 2)) | odd n = two n
quad .(suc (n * 2)) | odd n with parity' n
quad .(suc (n * 2 * _)) | odd .(n * 2) | even n = one n
quad .(suc (suc (n * 2) * _)) | odd .(suc (n * 2)) | odd n = three n
