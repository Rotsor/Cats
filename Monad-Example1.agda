module Monad-Example1 where

open import Category
open import Relation.Binary.PropositionalEquality
open import Level

SetCategory : ∀ a → Category (suc a) a
SetCategory a = category 
  (Set a)
  (λ A B → A → B) 
  (is 
    (λ z → z) 
    (λ f g x → f (g x)) 
    (λ m → refl)
    (λ m → refl) 
    (λ a' b' c' → refl))

open import Data.List
import Data.List.Properties as ListProps
open ListProps hiding(module Monad)
open import Functor
open import Monad
open import NaturalTransformation
open import Logic

ListF : ∀ a → Endofunctor (SetCategory a)
ListF a = record { 
  F = List; 
  map = map; 
  natural-id = extensionality map-id; 
  natural-compose = λ f g → sym (extensionality map-compose) }

concat-return : ∀ {a} {A : Set a} (l : List A) →
   concat (map (λ x → x ∷ []) l) ≡ l
concat-return [] = refl
concat-return (x ∷ xs) = cong (_∷_ x) (concat-return xs)

import Algebra

open import Data.Product

ListM : ∀ a → Monad (SetCategory a)
ListM a = record { 
  F = ListF a; 
  η = record { 
    η = λ x →  x ∷ []; 
    natural = λ _ → refl };
  μ = record { 
    η = concat; 
    natural = λ f → extensionality concat-map }; 
  unitˡ = equal (λ A → extensionality concat-return);
  unitʳ = equal (λ A → extensionality 
                (proj₂ (Algebra.Monoid.identity (monoid A)) ));
  assoc = equal (λ A → extensionality 
    (λ (x : List (List (List A))) →
      trans (sym (cong concat (trans (map-id _) (cong concat (map-id x)))))
      (trans (sym (ListProps.Monad.associative x (λ z → z) (λ z → z)))
      (cong concat (map-cong (λ y → cong concat (map-id y)) x)))))
  }
