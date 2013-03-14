module Cats.Algebra where

open import Cats.Monad
open import Cats.Category
open import Level
open import Cats.NaturalTransformation using (module NaturalTransformation)
open import Relation.Binary.PropositionalEquality

record Algebra {a b} {C : Category a b} (M : Monad C) : Set (a ⊔ b) where
 open Category C
 open Monad M
 field
  A : Category.Obj C
  θ : C [ O A , A ]
  law1 : θ ∘ NaturalTransformation.η η ≡ id
  law2 : θ ∘ map θ ≡ θ ∘ NaturalTransformation.η μ
