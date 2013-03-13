module Monad where

open import Category
open import Functor using (Endofunctor; Id) renaming (_∘_ to _f∘_)
open import NaturalTransformation
open import Level
open import Relation.Binary.PropositionalEquality

record Monad {o m} (C : Category o m) : Set (o ⊔ m) where
  field
   F : Endofunctor C
   η : Id C ⇒ F
   μ : F f∘ F ⇒ F

   .unitˡ : μ ∘ (F ^∘ η) ≡ id
   .unitʳ : μ ∘ (η ∘^ F) ≡ id
   .assoc : μ ∘ (μ ∘^ F) ≡ μ ∘ (F ^∘ μ)
