module Cats.NaturalIsomorphism where

open import Cats.Functor
open import Cats.Isomorphism
open import Cats.Category hiding (category)

NaturalIsomorphism : ∀
  {o₁ m₁} {C : Category o₁ m₁}
  {o₂ m₂} {D : Category o₂ m₂}
  (F G : Functor C D) → Set _
NaturalIsomorphism F G = Isomorphism (category _ _) F G
