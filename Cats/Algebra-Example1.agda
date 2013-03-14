module Cats.Algebra-Example1 where

open import Level
open import Algebra.Structures using (IsMonoid; module IsMonoid)
open import Cats.Algebra
open import Cats.Logic
open import Relation.Binary.PropositionalEquality
open import Cats.Monad-Example1
open import Data.List renaming (map to lmap)
open import Data.Product

module WithMonoid (A : Set) (ε : A) (_∙_ : A → A → A) 
  (Mo : IsMonoid _≡_ _∙_ ε) where

  open IsMonoid Mo hiding (refl; trans)

  open import Data.Product

  eval = foldr _∙_ ε
  theorem : ∀ (l : List (List A)) → eval (lmap eval l) ≡ eval (concat l)
  theorem [] = refl
  theorem ([] ∷ xs) = trans (proj₁ identity _) (theorem xs)
  theorem ((x ∷ xs) ∷ xss) = trans (assoc x (eval xs) _) 
    (cong (_∙_ x) (theorem (xs ∷ xss)))

  example-algebra : Algebra (ListM zero)
  example-algebra = record { 
    A = A; 
    θ = foldr _∙_ ε; 
    law1 = extensionality (proj₂ identity); 
    law2 = extensionality theorem }

module WithAlgebra (Alg : Algebra (ListM zero)) where
  open Algebra Alg
  ε = θ []
  _∙_ = λ a b → θ (a ∷ b ∷ [])
  Mo : IsMonoid _≡_ _∙_ ε
  Mo = record { 
    isSemigroup = record { 
      isEquivalence = record { refl = refl; sym = sym; trans = trans }; 
      assoc = λ x y z → trans 
        (trans
          (cong (λ q → θ (θ (x ∷ y ∷ []) ∷ q ∷ [])) 
            (sym (unextensionality law1 _)))
          (unextensionality law2 ((x ∷ y ∷ []) ∷ (z ∷ []) ∷ []))
        )
        (sym (trans
        (cong (λ q → θ (q ∷ θ (y ∷ z ∷ []) ∷ []))
          (sym (unextensionality law1 _)) )
        (unextensionality law2 ((x ∷ []) ∷ (y ∷ z ∷ []) ∷ []))
        ));
      ∙-cong = cong₂ (λ x y → θ (x ∷ y ∷ [])) }; 
    identity = (
      λ x → trans
        (cong (λ q → θ (θ [] ∷ q ∷ [])) (sym (unextensionality law1 _)))
         (trans 
           (unextensionality law2 _)
           (unextensionality law1 _)))
      , λ x → trans
        (cong (λ q → θ (q ∷ θ [] ∷ [])) (sym (unextensionality law1 _)))
         (trans 
           (unextensionality law2 _)
           (unextensionality law1 _)) }
