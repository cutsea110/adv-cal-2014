module Printf where

open import Data.Char
open import Data.List hiding (_++_)
open import Data.Nat
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Float renaming (show to showFloat)
open import Data.String

data Format : Set where
  FEnd : Format
  FStr : Format → Format
  FNat : Format → Format
  FFlt : Format → Format
  FLit : Char → Format → Format

toFormat : List Char → Format
toFormat [] = FEnd
toFormat ('%' ∷ 's' ∷ cs) = FStr (toFormat cs)
toFormat ('%' ∷ 'd' ∷ cs) = FNat (toFormat cs)
toFormat ('%' ∷ 'f' ∷ cs) = FFlt (toFormat cs)
toFormat (c ∷ cs) = FLit c (toFormat cs)

stringToFormat : String → Format
stringToFormat s = toFormat (toList s)

toType : Format → Set
toType FEnd = String
toType (FStr fmt) = String → toType fmt
toType (FNat fmt) = ℕ → toType fmt
toType (FFlt fmt) = Float → toType fmt
toType (FLit c fmt) = toType fmt

toFunction : (fmt : Format) → String → toType fmt
toFunction FEnd acc = acc
toFunction (FStr fmt) acc = λ s → toFunction fmt (acc ++ s)
toFunction (FNat fmt) acc = λ n → toFunction fmt (acc ++ showℕ n)
toFunction (FFlt fmt) acc = λ f → toFunction fmt (acc ++ showFloat f)
toFunction (FLit c fmt) acc = toFunction fmt (acc ++ fromList [ c ])

printf : (s : String) → toType (stringToFormat s)
printf s = toFunction (stringToFormat s) ""
