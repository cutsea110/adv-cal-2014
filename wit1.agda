open import Data.Fin
open import Data.Vec
open import Data.Nat

_!_ : {n : ℕ}{A : Set} → Vec A n → Fin n → A
[] ! () -- () absurd pattern
(x ∷ xs) ! zero = x
(x ∷ xs) ! suc n = xs ! n

open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Relation.Nullary

boo : Dec ⊥
-- boo = no λ()
boo = no (λ z → z)

yeah : Dec ⊤
yeah = yes tt

foo : true ≡ false → ⊥
foo = λ() -- C-cC-a

bar : true ≡ false → ⊥
bar () -- {!x!} C-cC-c

quz : true ≡ false → ⊤
-- quz x = tt
quz () -- top???

