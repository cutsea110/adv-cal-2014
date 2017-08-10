module ffi where

data Unit : Set where
  unit : Unit
  
{-# COMPILED_DATA Unit () ()  #-}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

{-# COMPILED_DATA Maybe Maybe Nothing Just  #-}

postulate IO : Set → Set
{-# COMPILED_TYPE IO IO #-}

open import Data.String
postulate
  putStrLn : String → IO Unit
{-# COMPILED putStrLn putStrLn #-}

{-# IMPORT System.IO #-}
postulate printError : String → IO Unit
{-# COMPILED printError (hPutStrLn stderr) #-}

main : IO Unit
main = putStrLn "Hello, World!"
