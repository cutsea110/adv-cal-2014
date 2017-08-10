module Universes where

data False : Set where
record True : Set where


data Bool : Set where
  false : Bool
  true : Bool

isTrue : Bool → Set
isTrue true = True
isTrue false = False

infix 30 not_
infixr 25 _and_

not_ : Bool → Bool
not false = true
not true = false

_and_ : Bool → Bool → Bool
false and b = false
true and b = b

notNotId : (a : Bool) → isTrue (not (not a)) → isTrue a
notNotId false ()
notNotId true p = p

andIntro : (a b : Bool) → isTrue a → isTrue b → isTrue (a and b)
andIntro false b p q = p
andIntro true b p q = q

open import Data.Nat

nonZero : ℕ → Bool
nonZero zero = false
nonZero (suc n) = true

postulate _div_ : ℕ → (m : ℕ){p : isTrue (nonZero m)} → ℕ

three = 16 div 5

open import Data.List
open import Data.Product

data Type : Set where
  bool : Type
  nat  : Type
  list : Type → Type
  pair : Type → Type → Type

El : Type → Set
El bool = Bool
El nat = ℕ
El (list a) = List (El a)
El (pair a b) = (El a) × El b

infix 30 _==_
_==_ : {a : Type} → El a → El a → Bool
_==_ {bool} false b = not b
_==_ {bool} true b = b
_==_ {nat} zero zero = true
_==_ {nat} zero (suc b) = false
_==_ {nat} (suc a) zero = false
_==_ {nat} (suc a) (suc b) = a == b
_==_ {list a} [] [] = true
_==_ {list a} [] (x ∷ ys) = false
_==_ {list a} (x ∷ xs) [] = false
_==_ {list a} (x ∷ xs) (y ∷ ys) = x == y and xs == ys
_==_ {pair a b} (x₁ , x₂) (y₁ , y₂) = x₁ == y₁ and x₂ == y₂
