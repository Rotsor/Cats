-- Assume univalence!

module Category where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Level

record IsCategory {o m} {O : Set o} (M : O → O → Set m) : Set (o ⊔ m) where
  constructor is
  field
    id : ∀ {o} → M o o
    _∘_ : ∀ {a b c} → M b c → M a b → M a c
    idˡ : ∀ {a b} (m : M a b) → id ∘ m ≡ m
    idʳ : ∀ {a b} (m : M a b) → m ∘ id ≡ m
    assoc : ∀ {a b c d} (a : M a b) (b : M b c) (c : M c d) → (c ∘ b) ∘ a ≡ c ∘ (b ∘ a)

record Category (o m : Level) : Set (suc (o ⊔ m)) where
  constructor category
  field
    Obj : Set o
    Morphism : Obj → Obj → Set m
    is-category : IsCategory Morphism
  open IsCategory is-category public
