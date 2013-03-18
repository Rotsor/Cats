module Cats.Functor where

open import Cats.Category
open import Relation.Binary.PropositionalEquality
open import Level

open import Cats.Functor.Core public

Endofunctor : ∀ {o m} (C : Category o m) → Set (o ⊔ m)
Endofunctor C = Functor C C

Id : ∀ {o m} → (C : Category o m) → Endofunctor C
Id C = record 
  { O = λ x → x
  ; map = λ m → m
  ; natural-id = refl
  ; natural-compose = λ _ _ → refl }

postulate
 equal : ∀
  {o₁ m₁} {C₁ : Category o₁ m₁}
  {o₂ m₂} {C₂ : Category o₂ m₂}
  (F G : Functor C₁ C₂)
  → (∀ x → Functor.O F x ≡ Functor.O G x)
  → (∀ {o₁ o₂} (m : Category.Morphism C₁ o₁ o₂) 
     → Functor.map F m ≡ Functor.map F m)
  → F ≡ G

open import Cats.Functor.Category public using () 
  renaming (functor-category to category)
