module Indices where

open import Data.Nat using (ℕ; _+_; _≟_; suc)
open import Data.List using (List; []; _++_; _∷_; map)
open import Relation.Nullary using (yes; no)

indices : ℕ → List ℕ → List ℕ
indices n [] = []
indices n (x ∷ xs) with n ≟ x
... | yes _ = 0 ∷ map suc (indices n xs)
... | no  _ = map suc (indices n xs)

indices-tail-1 : ℕ → List ℕ → ℕ → List ℕ
indices-tail-1 n [] count = []
indices-tail-1 n (x ∷ xs) count with n ≟ x
... | yes _ = count ∷ indices-tail-1 n xs (suc count)
... | no  _ = indices-tail-1 n xs (suc count)

open import Data.Product using (_,_ ; _×_)

indices-tail-2 : ℕ → List ℕ → (ℕ × List ℕ) → List ℕ
indices-tail-2 n [] (_ , l) = l
indices-tail-2 n (x ∷ xs) (v , l) with n ≟ x
... | yes _ = indices-tail-2 n xs (v + 1 , v ∷ l)
... | no _ = indices-tail-2 n xs (v + 1 , l)

test-indices : List ℕ
test-indices = indices 4 (2 ∷ 1 ∷ 4 ∷ 3 ∷ 4 ∷ [])

test-indices-tail-1 : List ℕ
test-indices-tail-1 = indices-tail-1 4 (2 ∷ 1 ∷ 4 ∷ 3 ∷ 4 ∷ []) 0

test-indices-tail-2 : List ℕ
test-indices-tail-2 = indices-tail-2 4 (2 ∷ 1 ∷ 4 ∷ 3 ∷ 4 ∷ []) (0 , [])

