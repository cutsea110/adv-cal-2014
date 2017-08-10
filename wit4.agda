module wit4 where

-- View

open import Data.Nat hiding (erase)

-- view data type
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

record Test1 : Set where
  open import Data.Empty
  
  f : Parity 0
  f = even zero

  f' : Parity 1
  f' = odd zero

  f'' : Parity 2
  f'' = even (suc zero)


open import Function hiding (_$_)
open import Data.List
open import Data.Bool
open import Data.Unit
open import Data.Empty

infixr 30 _:all:_
data All {A : Set}(P : A → Set) : List A → Set where
  all[] : All P []
  _:all:_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

isTrue : Bool → Set
isTrue true = ⊤
isTrue false = ⊥

isFalse : Bool → Set
isFalse x = isTrue (not x)

-- convert
satisfies : {A : Set} → (A → Bool) → A → Set
satisfies p x = isTrue (p x) -- isTrue false or isTrue true

-- view for All
data Find {A : Set}(p : A → Bool) : List A → Set where
  found : (xs : List A)(y : A) → satisfies p y → (ys : List A) → Find p (xs ++ y ∷ ys)
  not-found : ∀ {xs} → All (satisfies (not ∘ p)) xs → Find p xs

{--
find₁ : {A : Set} → (p : A → Bool) → (xs : List A) → Find p xs
find₁ p [] = not-found all[]
find₁ p (x ∷ xs) with p x
find₁ p (x ∷ xs) | true = found [] x {!!} xs
find₁ p (x ∷ xs) | false = {!!}
--}

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- Aの値,true,0,3とかをInspect true,Inspect 0などにマップして値としては it true refl, it 0 reflとかを作成
-- refl は true ≡ true, 0 ≡ 0 とか
-- View
data Inspect {A : Set}(x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

-- convert
inspect : {A : Set}(x : A) → Inspect x
inspect x = it x refl

trueIsTrue : {x : Bool} → x ≡ true → isTrue x
trueIsTrue refl = tt

falseIsFalse : {x : Bool} → x ≡ false → isFalse x
falseIsFalse refl = tt

this-is-a-miso? : {A : Set} → (x : A) → (p : A → Bool) → p x ≡ true → satisfies p x
this-is-a-miso? p x prf = trueIsTrue prf

find : {A : Set} → (p : A → Bool) → (xs : List A) → Find p xs
find p [] = not-found all[]
find p (x ∷ xs) with inspect (p x)
find p (x ∷ xs) | it true px≡true = found [] x (trueIsTrue px≡true) xs
find p (x ∷ xs) | it false px≡false with find p xs
find p (x₁ ∷ .(xs ++ y ∷ ys)) | it false px≡false | found xs y py≡true ys = found (x₁ ∷ xs) y py≡true ys
find p (x₁ ∷ xs) | it false px≡false | not-found npxs = not-found (falseIsFalse px≡false :all: npxs)

data _∈_ {A : Set} (x : A) : List A → Set where
  hd : {xs : List A} → x ∈ (x ∷ xs)
  tl : {y : A}{xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

index : ∀ {A}{x : A}{xs} → x ∈ xs → ℕ
index hd = zero
index (tl prf) = suc (index prf)

data Lookup {A : Set}(xs : List A) : ℕ → Set where
  inside : (x : A)(p : x ∈ xs) → Lookup xs (index p)
  outside : (m : ℕ) → Lookup xs (length xs + m)

_!_ : {A : Set}(xs : List A)(n : ℕ) → Lookup xs n
[] ! n = outside n
(x ∷ xs) ! zero = inside x hd
(x ∷ xs) ! suc n with xs ! n
(x ∷ xs) ! suc .(index p) | inside y p = inside y (tl p)
(x ∷ xs) ! suc .(foldr (λ _ → suc) 0 xs + m) | outside m = outside m

infixr 30 _⇒_
data Type : Set where
  ı : Type
  _⇒_ : Type → Type → Type

data Equal? : Type → Type → Set where
  yes : ∀{τ} → Equal? τ τ
  no  : ∀{σ τ} → Equal? σ τ

_=?=_ : (σ τ : Type) → Equal? σ τ
ı =?= ı = yes
ı =?= (_ ⇒ _) = no
(_ ⇒ _) =?= ı = no
(σ₁ ⇒ τ₁) =?= (σ₂ ⇒ τ₂) with σ₁ =?= σ₂ | τ₁ =?= τ₂
σ₁ ⇒ τ₁ =?= .σ₁ ⇒ .τ₁ | yes | yes = yes
σ₁ ⇒ τ₁ =?= σ₂ ⇒ τ₂ | _ | _ = no

infixl 80 _$_
data Raw : Set where
  var : ℕ → Raw
  _$_ : Raw → Raw → Raw
  lam : Type → Raw → Raw

Cxt = List Type

data Term (Γ : Cxt) : Type → Set where
  var : ∀{τ} → τ ∈ Γ → Term Γ τ
  _$_ : ∀{σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

erase : ∀ {Γ τ} → Term Γ τ → Raw
erase (var x) = var (index x)
erase (t $ u) = (erase t) $ (erase u)
erase (lam σ t) = lam σ (erase t)

data Infer (Γ : Cxt) : Raw → Set where
  ok : (τ : Type)(t : Term Γ τ) → Infer Γ (erase t)
  bad : {e : Raw} → Infer Γ e

infer : (Γ : Cxt) (e : Raw) → Infer Γ e
infer Γ (var n) with Γ ! n
infer Γ (var .(length Γ + n)) | outside n = bad
infer Γ (var .(index x)) | inside σ x = ok σ (var x)
infer Γ (e₁ $ e₂) with infer Γ e₁
infer Γ (e₁ $ e₂) | bad = bad
infer Γ (.(erase t₁) $ e₂) | ok ı t₁ = bad
infer Γ (.(erase t₁) $ e₂) | ok (σ ⇒ τ) t₁ with infer Γ e₂
infer Γ (.(erase t₁) $ e₂) | ok (σ ⇒ τ) t₁ | bad = bad
infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⇒ τ) t₁ | ok σ' t₂ with σ =?= σ'
infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⇒ τ) t₁ | ok .σ t₂ | yes = ok τ (t₁ $ t₂)
infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⇒ τ) t₁ | ok σ' t₂ | no = bad
infer Γ (lam σ e) with infer (σ ∷ Γ) e
infer Γ (lam σ .(erase t)) | ok τ t = ok (σ ⇒ τ) (lam σ t)
infer Γ (lam σ e) | bad = bad
