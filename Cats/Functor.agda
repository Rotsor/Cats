module Cats.Functor where

open import Cats.Category
open import Relation.Binary.PropositionalEquality
open import Level

record Functor 
  {o₁ m₁} (C₁ : Category o₁ m₁)
  {o₂ m₂} (C₂ : Category o₂ m₂)
  : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂) where
  module C₁ = Category C₁
  module C₂ = Category C₂
  open C₁ using () renaming (Morphism to M₁; _∘_ to _∘₁_; Obj to O₁)
  open C₂ using () renaming (Morphism to M₂; _∘_ to _∘₂_; Obj to O₂)
  field
    O : O₁ → O₂
    map : ∀ {a b} → M₁ a b → M₂ (O a) (O b)
    .natural-id : ∀ {a} → map {a} (C₁.id) ≡ C₂.id
    .natural-compose : ∀ {a b c} (f : M₁ b c) (g : M₁ a b) → map f ∘₂ map g ≡ map (f ∘₁ g)

Endofunctor : ∀ {o m} (C : Category o m) → Set (o ⊔ m)
Endofunctor C = Functor C C

Id : ∀ {o m} → (C : Category o m) → Endofunctor C
Id C = record 
  { O = λ x → x
  ; map = λ m → m
  ; natural-id = refl
  ; natural-compose = λ _ _ → refl }

infix 15 _∘_

_∘_ : ∀ {o₁ m₁ o₂ m₂ o₃ m₃} 
  {C : Category o₁ m₁} {D : Category o₂ m₂} {E : Category o₃ m₃} 
  → Functor D E → Functor C D → Functor C E
F ∘ G = record 
  { O = λ x → F.O (G.O x)
  ; map = λ x → F.map (G.map x)
  ; natural-id = trans (cong F.map G.natural-id) F.natural-id
  ; natural-compose = λ f g → trans (F.natural-compose _ _) (cong F.map (G.natural-compose f g))
  } where
  module F = Functor F
  module G = Functor G
