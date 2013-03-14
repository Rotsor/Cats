module Cats.NaturalTransformation where

open import Cats.Functor using (Functor; module Functor) renaming (_∘_ to _f∘_)
open import Cats.Category
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)

open import Level using (_⊔_)

record NaturalTransformation {o₁ m₁ o₂ m₂} {C : Category o₁ m₁} {D : Category o₂ m₂} (F G : Functor C D) : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂) where
  module C = Category C
  module D = Category D
  open D using (_∘_)
  module F = Functor F
  module G = Functor G
  field
    η : ∀ {x} → D.Morphism (F.O x) (G.O x)
    .natural : ∀ {a b} (m : C.Morphism a b) → η ∘ F.map m ≡ G.map m ∘ η

infix 10 _⇒_

_⇒_ : ∀ {o₁ m₁ o₂ m₂} {C : Category o₁ m₁} {D : Category o₂ m₂} (F G : Functor C D) → Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂)
_⇒_ = NaturalTransformation

infixl 8 _∘_
infixl 8 _^∘_

_∘_ : ∀ {o₁ m₁ o₂ m₂} {C : Category o₁ m₁} {D : Category o₂ m₂} {F G H : Functor C D} →
  G ⇒ H → (F ⇒ G) → F ⇒ H
_∘_ {D = D} N₁ N₂ = record { 
  η =  N₁.η D∘ N₂.η;
  natural = λ m →
    trans (assoc _ _ _) (trans (trans (cong (λ q → N₁.η D∘ q) (N₂.natural m)) 
    (trans (sym (assoc _ _ _)) (cong (λ q → q D∘ N₂.η) (N₁.natural m))))
    (assoc _ _ _)) 
  } where
  open Category D renaming (_∘_ to _D∘_)
  module N₁ = NaturalTransformation N₁
  module N₂ = NaturalTransformation N₂

_^∘_ : ∀ {o₁ m₁ o₂ m₂ o₃ m₃} {C : Category o₁ m₁} {D : Category o₂ m₂} {E : Category o₃ m₃}
  → (F : Functor D E) → {G H : Functor C D} → NaturalTransformation G H →  NaturalTransformation (F f∘ G) (F f∘ H)
F ^∘ N = record {
  η = F.map N.η; 
  natural = λ m → trans (F.natural-compose _ _) (trans (cong F.map (N.natural m)) (sym (F.natural-compose _ _))) } where
  module F = Functor F
  module N = NaturalTransformation N

_∘^_ : ∀ {o₁ m₁ o₂ m₂ o₃ m₃} {C : Category o₁ m₁} {D : Category o₂ m₂} {E : Category o₃ m₃}
  → {G H : Functor D E} → NaturalTransformation G H →  (F : Functor C D) → NaturalTransformation (G f∘ F) (H f∘ F)
N ∘^ F = record { 
  η = N.η; natural = λ m → N.natural _ } where
  module N = NaturalTransformation N

id : ∀ {o₁ m₁ o₂ m₂} {C : Category o₁ m₁} {D : Category o₂ m₂} {F : Functor C D} → F ⇒ F
id {D = D} = record { 
  η = Category.id D; 
  natural = λ _ → trans (Category.idˡ D _) (sym (Category.idʳ D _)) 
  }

open import Cats.Logic

postulate 
  equal : ∀ {o₁ m₁ o₂ m₂} {C : Category o₁ m₁} {D : Category o₂ m₂} {F G : Functor C D} 
    → {a b : F ⇒ G} → (∀ x → NaturalTransformation.η a {x} ≡ NaturalTransformation.η b {x}) → a ≡ b

