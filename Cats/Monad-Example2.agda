module Cats.Monad-Example2 where

open import Cats.Monad
open import Cats.Category


record Graph : Set₁ where
 field
  O : Set
  M : O → O → Set

data ArrowChain (G : Graph) : let open Graph G in O → O → Set where
  [] : ∀ {o} → ArrowChain G o o
  _∷_ : ∀ {a b c} → Graph.M G b c → ArrowChain G a b → ArrowChain G a c

_++_ : ∀ {G : Graph} {a b c} → ArrowChain G b c → ArrowChain G a b → ArrowChain G a c
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

open import Relation.Binary.PropositionalEquality

right-zero : ∀ {G} {a b} {m : ArrowChain G a b} → m ++ [] ≡ m
right-zero {m = []} = refl
right-zero {m = x ∷ xs} = cong (λ q → x ∷ q) right-zero

assoc : ∀ {G} {a b c d} 
  (x : ArrowChain G c d) (y : ArrowChain G b c) (z : ArrowChain G a b) 
  → (x ++ y) ++ z ≡ x ++ (y ++ z)
assoc [] y z = refl
assoc (x ∷ xs) ys zs = cong (λ q → x ∷ q) (assoc xs ys zs)

FreeCat : Graph → Category _ _
FreeCat G = category 
  O
  (ArrowChain G)
  (is 
    []
    _++_ 
    (λ _ → refl) 
    (λ _ → right-zero) 
    assoc)
 where
  open Graph G
