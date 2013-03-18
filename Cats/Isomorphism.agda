open import Cats.Category
open import Relation.Binary.PropositionalEquality

module Cats.Isomorphism {o m} (C : Category o m) where

open Category C

record Isomorphism (A B : Obj) : Set m where
 field
  to : Morphism A B
  from : Morphism B A
  .inv1 : from ∘ to ≡ id
  .inv2 : to ∘ from ≡ id
