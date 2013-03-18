module Cats.Functor.Category where

open import Cats.Category hiding (category)
open import Cats.Functor.Core
open import Cats.NaturalTransformation renaming (_∘_ to _∘₁_)

functor-category : ∀ {o₁ m₁ o₂ m₂} (C : Category o₁ m₁) (D : Category o₂ m₂) 
  → Category _ _
functor-category C D = Category.category 
  (Functor C D)
  NaturalTransformation
  (is 
  id 
  _∘₁_ 
  (λ m → equal (λ _ → Category.idˡ D _))
  (λ m → equal (λ _ → Category.idʳ D _))
  (λ x y z → equal (λ _ → Category.assoc D _ _ _)))
