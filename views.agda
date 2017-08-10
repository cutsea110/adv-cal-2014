module views where

open import Data.Nat

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd  : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(suc (k * 2))) | odd k = even (suc k)


half : ℕ → ℕ
half n with parity n
half .(k * 2) | even k = k
half .(suc (k * 2)) | odd k = k
  

data Trity : ℕ → Set where
  one : (k : ℕ) → Trity (k * 3)
  two : (k : ℕ) → Trity (1 + k * 3)
  thr : (k : ℕ) → Trity (2 + k * 3)

trity : (n : ℕ) → Trity n
trity zero = one zero
trity (suc zero) = two zero
trity (suc (suc n)) with trity n
trity (suc (suc .(k * 3))) | one k = thr k
trity (suc (suc .(suc (k * 3)))) | two k = one (suc k)
trity (suc (suc .(suc (suc (k * 3))))) | thr k = two (suc k)

div3 : ℕ → ℕ
div3 n with trity n
div3 .(k * 3) | one k = k
div3 .(suc (k * 3)) | two k = k
div3 .(suc (suc (k * 3))) | thr k = k
