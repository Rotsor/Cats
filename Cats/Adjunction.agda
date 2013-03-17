module Cats.Adjunction where

open import Cats.Functor
open import Cats.Category
open import Cats.NaturalTransformation renaming (_∘_ to _∘₁_)
open import Level
open import Relation.Binary.PropositionalEquality

record Adjunction
  {o₁ m₁} {C : Category o₁ m₁}
  {o₂ m₂} {D : Category o₂ m₂}
  (F : Functor C D)
  (G : Functor D C) : Set (o₁ ⊔ o₂ ⊔ m₁ ⊔ m₂) where
 field
  unit : Id C ⇒ G ∘ F
  counit : F ∘ G ⇒ Id D
  .axiom1 : (G ^∘ counit) ∘₁ (unit ∘^ G) ≡ id
  .axiom2 : (counit ∘^ F) ∘₁ (F ^∘ unit) ≡ id
