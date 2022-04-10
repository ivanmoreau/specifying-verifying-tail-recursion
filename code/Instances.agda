module Instances where

open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-0-isMonoid)
open import GenericBasic
  {A = ℕ} (λ _ → 1) _+_ 0 +-0-isMonoid
  renaming ( reduce to length
           ; reduce-tail to length-tail
           ; reduce≡reduce-tail to length≡length-tail
           )

open import Algebra.Structures using (IsMonoid)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong₂)
open import Relation.Binary.PropositionalEquality.Properties
  using (isEquivalence)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-identityˡ; ++-isMagma; ++-assoc)
open import Data.Product using (_,_)

++-flipped-isMonoid : {A : Set}
                    → IsMonoid {A = List A} _≡_
                        (flip _++_) []
++-flipped-isMonoid {A} = record
  { isSemigroup = record
    { isMagma = record
      { isEquivalence = isEquivalence
      ; ∙-cong = cong₂ (flip _++_)
      }
    ; assoc = λ x y z → sym (++-assoc z y x)
    }
  ; identity = ++-identityʳ , ++-identityˡ
  }

open import GenericBasic
  {A = ℕ} (λ x → x ∷ []) (flip _++_) []
           ++-flipped-isMonoid
  renaming ( reduce to reverse
           ; reduce-tail to reverse-tail
           ; reduce≡reduce-tail to reverse≡reverse-tail
           )

