module Cats.Logic where

open import Relation.Binary.PropositionalEquality

postulate extensionality : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

implicify : ∀  {a b} {A : Set a} {B : Set b} → ({x : A} → B) → (A → B)
implicify f = λ x → f {x}

open import Level

{- substt : ∀ {a b l} {A : Set a} {B : Set b} → (P : Set (a ⊔ b) → Set l)
  → P ({x : A} → B) → P (A → B)
substt P tr = {!!}

implicify-inj : ∀ {a b} {A : Set a} {B : Set b} → (f g : {x : A} → B) 
  → implicify (λ {x} → f {x}) ≡ implicify (λ {x} → g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
implicify-inj f g eq = {!eq!} -}

postulate extensionality' : ∀ {a b} {A : Set a} {B : Set b} {f g : ∀ {a : A} → B} → (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})

