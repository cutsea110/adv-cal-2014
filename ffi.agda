module ffi where

data Unit : Set where
  tt : Unit
  
{-# COMPILE GHC Unit = data () (()) #-}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}

postulate IO : Set → Set
{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

open import Data.String

{-# FOREIGN GHC import qualified System.IO as IO #-}
{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}

postulate
  putStrLn : String → IO Unit
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

postulate printError : String → IO Unit
{-# COMPILE GHC printError = (Text.hPutStrLn IO.stderr) #-}

main : IO Unit
main = putStrLn "Hello, World!"
