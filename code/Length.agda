module Length where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.List using (List; []; _∷_; _++_)

variable A : Set

length : List A → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)

length-tail : List A → ℕ → ℕ
length-tail [] n = n
length-tail (x ∷ xs) n = length-tail xs (suc n)

-- Functional equality

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym)
open import Data.Nat.Properties using (+-suc)

length-pull-generalized :
    ∀ (xs : List A) (n p : ℕ)
    → n + length-tail xs p ≡ length-tail xs (n + p)
length-pull-generalized [] n p = refl
length-pull-generalized (x ∷ xs) n p
  rewrite (sym (+-suc n p))
        = length-pull-generalized xs n (suc p)

length-pull : ∀ (xs : List A)
            → suc (length-tail xs 0) ≡ length-tail xs 1
length-pull xs = length-pull-generalized xs 1 0

length≡length-tail : ∀ (xs : List A)
                   → length xs ≡ length-tail xs 0
length≡length-tail [] = refl
length≡length-tail (x ∷ xs) =
  let ind-h = length≡length-tail xs
      suc-cong = cong suc ind-h
      suc-pull = length-pull xs
   in trans suc-cong suc-pull

-- Other properties

concat-length : ∀ (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
concat-length [] ys = refl
concat-length (x ∷ xs) ys = cong suc (concat-length xs ys)

concat-length-tail : ∀ (xs ys : List ℕ)
                   → length-tail (xs ++ ys) 0 ≡ length-tail xs 0 + length-tail ys 0
concat-length-tail [] ys = refl
concat-length-tail (x ∷ xs) ys
  rewrite sym (length-pull (xs ++ ys))
        | sym (length-pull xs)
        = cong suc (concat-length-tail xs ys)

