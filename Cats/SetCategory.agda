module Cats.SetCategory where

open import Cats.Category
open import Relation.Binary.PropositionalEquality
open import Level

SetCategory : ∀ a → Category (suc a) a
SetCategory a = category 
  (Set a)
  (λ A B → A → B) 
  (is 
    (λ z → z) 
    (λ f g x → f (g x)) 
    (λ _ → refl)
    (λ _ → refl) 
    (λ _ _ _ → refl))
