module Monoid where

open import Data.List
open import Data.Nat
open import Data.Product
open import Function using (_∘_; id; const)
open import Relation.Binary.PropositionalEquality as PropEq hiding (Extensionality)
open import Axiom.Extensionality.Propositional

Op₂ : Set → Set
Op₂ A = A → A → A
Assoc : {A : Set} →  Op₂ A → Set
Assoc _∙_ = ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
Left-Id : {A : Set} → Op₂ A → A → Set
Left-Id _∙_ e = ∀ x → e ∙ x ≡ x
Right-Id : {A : Set} → Op₂ A → A → Set
Right-Id _∙_ e = ∀ x → x ∙ e ≡ x
Identity : {A : Set} → Op₂ A → A → Set
Identity _∙_ e = Left-Id _∙_ e × Right-Id _∙_ e

record IsSemiGroup (A : Set) (_∙_ : Op₂ A) : Set where
  field
    assoc : Assoc _∙_

ℕ+-isSemigroup : IsSemiGroup ℕ _+_
ℕ+-isSemigroup = record { assoc = ℕ+-assoc }
  where
    ℕ+-assoc : Assoc _+_
    ℕ+-assoc zero y z = refl
    ℕ+-assoc (suc x) y z = cong suc (ℕ+-assoc x y z)

record IsMonoid (A : Set) (_∙_ : Op₂ A) (e : A) : Set where
  field
    isSemigroup : IsSemiGroup A _∙_
    identity : Identity _∙_ e

ℕ+0-isMonoid : IsMonoid ℕ _+_ 0
ℕ+0-isMonoid = record { isSemigroup = ℕ+-isSemigroup
                      ; identity = 0+x≡x , x+0≡x
                      }
             where
               0+x≡x : Left-Id _+_ 0
               0+x≡x x = refl
               x+0≡x : Right-Id _+_ 0
               x+0≡x zero = refl
               x+0≡x (suc x) = cong suc (x+0≡x x)

ℕ*-isSemigroup : IsSemiGroup ℕ _*_
ℕ*-isSemigroup = record { assoc = ℕ*-assoc }
  where
    *-+-dist-r : (n m p : ℕ) → (n + m) * p ≡ (n * p) + (m * p)
    *-+-dist-r zero m p = refl
    *-+-dist-r (suc n) m p
      rewrite *-+-dist-r n m p
            | (IsSemiGroup.assoc ℕ+-isSemigroup) p (n * p) (m * p)
            = refl

    ℕ*-assoc : Assoc _*_
    ℕ*-assoc zero y z = refl
    ℕ*-assoc (suc x) y z
      rewrite ℕ*-assoc x y z
            | *-+-dist-r y (x * y) z
            = cong ((y * z) +_) (ℕ*-assoc x y z)

ℕ*1-isMonoid : IsMonoid ℕ _*_ 1
ℕ*1-isMonoid = record { isSemigroup = ℕ*-isSemigroup
                      ; identity = 1*x≡x , x*1≡x
                      }
             where
               1*x≡x : Left-Id _*_ 1
               1*x≡x zero = refl
               1*x≡x (suc x) = cong suc (1*x≡x x)
               x*1≡x : Right-Id _*_ 1
               x*1≡x zero = refl
               x*1≡x (suc x) = cong suc (x*1≡x x)

List++-isSemigroup : {a : Set} → IsSemiGroup (List a) _++_
List++-isSemigroup = record { assoc = List++-assoc }
  where
    List++-assoc : Assoc _++_
    List++-assoc [] y z = refl
    List++-assoc (x ∷ xs) y z rewrite List++-assoc xs y z = refl

List++[]-isMonoid : {a : Set} → IsMonoid (List a) _++_ []
List++[]-isMonoid = record { isSemigroup = List++-isSemigroup
                           ; identity = []++xs≡xs , xs++[]≡xs
                           }
                  where
                    []++xs≡xs : Left-Id _++_ []
                    []++xs≡xs xs = refl
                    xs++[]≡xs : Right-Id _++_ []
                    xs++[]≡xs [] = refl
                    xs++[]≡xs (x ∷ xs) rewrite xs++[]≡xs xs = refl

record Endo (A : Set) : Set where
  constructor endo
  field
    appEndo : A → A

_∙_ : {A : Set} → Op₂ (Endo A)
endo f ∙ endo g = endo (f ∘ g)

Endo-isSemigroup : {A : Set} → IsSemiGroup (Endo A) _∙_
Endo-isSemigroup = record { assoc = λ x y z → refl }

Endo-isMonoid : {A : Set} → IsMonoid (Endo A) _∙_ (endo id)
Endo-isMonoid = record { isSemigroup = Endo-isSemigroup
                       ; identity = (λ x → refl) , (λ x → refl)
                       }

record Dual (A : Set) : Set where
  constructor dual
  field
    getDual : A

⇄ : {A : Set} → (Op₂ A) → Op₂ (Dual A)
⇄ _⊕_ (dual x) (dual y) = dual (y ⊕ x)

Dual-isSemigroup : {A : Set}{_⊕_ : Op₂ A} →
  IsSemiGroup A _⊕_ → IsSemiGroup (Dual A) (⇄ _⊕_)
Dual-isSemigroup {_⊕_ = _⊕_} prf
  = record { assoc = ⇄-assoc {_⊕_ = _⊕_} (assoc prf) }
  where
    open IsSemiGroup
    open Dual
    ⇄-assoc : ∀ {A} {_⊕_ : Op₂ A} → Assoc _⊕_ → Assoc (⇄ _⊕_)
    ⇄-assoc prf (dual x) (dual y) (dual z) = cong dual (sym (prf z y x))

Dual-isMonoid : {A : Set}{_⊕_ : Op₂ A}{e : A} →
  IsMonoid A _⊕_ e → IsMonoid (Dual A) (⇄ _⊕_) (dual e)
Dual-isMonoid {_⊕_ = _⊕_} prf
  = record { isSemigroup = Dual-isSemigroup (isSemigroup prf)
           ; identity = left-id {_⊕_ = _⊕_} (proj₂ (identity prf))
                      , right-id {_⊕_ = _⊕_} (proj₁ (identity prf))
           }
              where
                open IsMonoid
                open Dual
                left-id : ∀ {A} {_⊕_ : Op₂ A} {e : A} →
                  Right-Id _⊕_ e → Left-Id (⇄ _⊕_) (dual e)
                left-id p (dual x) = cong dual (p x)
                right-id : ∀ {A} {_⊕_ : Op₂ A} {e : A} →
                  Left-Id _⊕_ e → Right-Id (⇄ _⊕_) (dual e)
                right-id p (dual x) = cong dual (p x)

_|><|_ : {A B : Set} → Op₂ A → Op₂ B → Op₂ (A × B)
(_⊕_ |><| _⊗_) (x₁ , x₂) (y₁ , y₂) = x₁ ⊕ y₁ , x₂ ⊗ y₂

×-isSemigroup : {A B : Set}{_⊕_ : Op₂ A}{_⊗_ : Op₂ B} →
  IsSemiGroup A _⊕_ → IsSemiGroup B _⊗_ → IsSemiGroup (A × B) (_⊕_ |><| _⊗_)
×-isSemigroup {_⊕_ = _⊕_}{_⊗_ = _⊗_} prf₁ prf₂
  = record { assoc = ×-assoc {_⊕_ = _⊕_}{_⊗_ = _⊗_} (assoc prf₁) (assoc prf₂) }
  where
    open IsSemiGroup
    ×-assoc : ∀ {A B} {_⊕_ : Op₂ A} {_⊗_ : Op₂ B} →
            Assoc _⊕_ → Assoc _⊗_ → Assoc (_⊕_ |><| _⊗_)
    ×-assoc p₁ p₂ (x₁ , x₂) (y₁ , y₂) (z₁ , z₂)
      rewrite p₁ x₁ y₁ z₁ | p₂ x₂ y₂ z₂ = refl

×-isMonoid : {A B : Set}{_⊕_ : Op₂ A}{_⊗_ : Op₂ B}{e₁ : A}{e₂ : B} →
  IsMonoid A _⊕_ e₁ → IsMonoid B _⊗_ e₂ → IsMonoid (A × B) (_⊕_ |><| _⊗_) (e₁ , e₂)
×-isMonoid {_⊕_ = _⊕_}{_⊗_ = _⊗_} prf₁ prf₂
  = record { isSemigroup = ×-isSemigroup (isSemigroup prf₁) (isSemigroup prf₂)
           ; identity = ×-identity {_⊕_ = _⊕_}{_⊗_ = _⊗_} (identity prf₁) (identity prf₂)
           }
  where
    open IsMonoid
    left-id : ∀ {A B} {_⊕_ : Op₂ A} {_⊗_ : Op₂ B} {e₁ : A} {e₂ : B} →
            Left-Id _⊕_ e₁ → Left-Id _⊗_ e₂ → Left-Id (_⊕_ |><| _⊗_) (e₁ , e₂)
    left-id p₁ p₂ (x₁ , x₂) rewrite p₁ x₁ | p₂ x₂ = refl
    right-id : ∀ {A B} {_⊕_ : Op₂ A} {_⊗_ : Op₂ B} {e₁ : A} {e₂ : B} →
            Right-Id _⊕_ e₁ → Right-Id _⊗_ e₂ → Right-Id (_⊕_ |><| _⊗_) (e₁ , e₂)
    right-id p₁ p₂ (x₁ , x₂) rewrite p₁ x₁ | p₂ x₂ = refl
    ×-identity : ∀ {A B} {_⊕_ : Op₂ A} {_⊗_ : Op₂ B} {e₁ : A} {e₂ : B} →
               Identity _⊕_ e₁ → Identity _⊗_ e₂ → Identity (_⊕_ |><| _⊗_) (e₁ , e₂)
    ×-identity {_⊕_ = _⊕_}{_⊗_ = _⊗_} prf₁ prf₂
      = left-id {_⊕_ = _⊕_}{_⊗_ = _⊗_} (proj₁ prf₁) (proj₁ prf₂)
      , right-id {_⊕_ = _⊕_}{_⊗_ = _⊗_} (proj₂ prf₁) (proj₂ prf₂)

postulate
  extensionality : ∀ {a b} → Extensionality a b

↦ : {A B : Set} → Op₂ B → Op₂ (A → B)
↦ _⊕_ f g x = f x ⊕ g x

↦-isSemigroup : {A B : Set} {_⊕_ : Op₂ B} → IsSemiGroup B _⊕_ → IsSemiGroup (A → B) (↦ _⊕_)
↦-isSemigroup {_⊕_ = _⊕_} prf = record { assoc = ↦-assoc {_⊕_ = _⊕_} (assoc prf) }
  where
    open IsSemiGroup
    ↦-assoc : ∀ {A B} {_⊕_ : Op₂ B} → Assoc _⊕_ → Assoc (↦ {A} _⊕_)
    ↦-assoc prf f g h = extensionality (λ x → prf (f x) (g x) (h x))

↦-isMonoid : {A B : Set} {_⊕_ : Op₂ B}{e : B} →
  IsMonoid B _⊕_ e → IsMonoid (A → B) (↦ _⊕_) (const e)
↦-isMonoid {_⊕_ = _⊕_} prf
  = record { isSemigroup = ↦-isSemigroup (isSemigroup prf)
           ; identity = left-id {_⊕_ = _⊕_} (proj₁ (identity prf))
                      , right-id {_⊕_ = _⊕_} (proj₂ (identity prf))
           }
  where
    open IsMonoid
    left-id : ∀ {A B} {_⊕_ : Op₂ B} {e : B} → Left-Id _⊕_ e → Left-Id (↦ {A} _⊕_) (const e)
    left-id p f = extensionality (λ x → p (f x))
    right-id : ∀ {A B} {_⊕_ : Op₂ B} {e : B} → Right-Id _⊕_ e → Right-Id (↦ {A} _⊕_) (const e)
    right-id p f = extensionality (λ x → p (f x))

foo-isMonoid : {A : Set} → IsMonoid ((Dual (A → ℕ)) × (A → (Dual ℕ))) (⇄ (↦ _+_) |><| ↦ (⇄ _+_)) ((dual (const 0)) , (const (dual 0)))
foo-isMonoid = ×-isMonoid (Dual-isMonoid (↦-isMonoid ℕ+0-isMonoid))
                           (↦-isMonoid (Dual-isMonoid ℕ+0-isMonoid))

bar-isMonoid : {A : Set} → IsMonoid ((Dual (List (A → ℕ))) × (A → (List (Dual ℕ)))) (⇄ _++_ |><| ↦ _++_) ((dual []) , (const []))
bar-isMonoid = ×-isMonoid (Dual-isMonoid List++[]-isMonoid) (↦-isMonoid List++[]-isMonoid)

buz-isMonoid : IsMonoid (ℕ × ℕ) (_+_ |><| _*_) (0 , 1)
buz-isMonoid = ×-isMonoid ℕ+0-isMonoid ℕ*1-isMonoid
