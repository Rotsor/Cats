-- Assume univalence!

module Cats.Category where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Level

record IsCategory {o m} {O : Set o} (M : O → O → Set m) : Set (o ⊔ m) where
  constructor is
  field
    id : ∀ {o} → M o o
    _∘_ : ∀ {a b c} → M b c → M a b → M a c
    .idˡ : ∀ {a b} (m : M a b) → id ∘ m ≡ m
    .idʳ : ∀ {a b} (m : M a b) → m ∘ id ≡ m
    .assoc : ∀ {a b c d} (x : M c d) (y : M b c) (z : M a b) 
      → (x ∘ y) ∘ z ≡ x ∘ (y ∘ z)

record Category (o m : Level) : Set (suc (o ⊔ m)) where
  constructor category
  field
    Obj : Set o
    Morphism : Obj → Obj → Set m
    is-category : IsCategory Morphism
  open IsCategory is-category public

_[_,_] : ∀ {o m} → (c : Category o m) → (a b : Category.Obj c) → Set m
C [ a , b ] = Category.Morphism C a b
