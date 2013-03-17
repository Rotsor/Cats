module Cats.Algebra where

open import Cats.Monad
open import Cats.Category
open import Level
open import Cats.NaturalTransformation using (module NaturalTransformation)
open import Relation.Binary.PropositionalEquality hiding ([_])

record Algebra {a b} {C : Category a b} (M : Monad C) : Set (a ⊔ b) where
 open Category C
 open Monad M
 field
  A : Category.Obj C
  θ : C [ O A , A ]
  law1 : θ ∘ NaturalTransformation.η η ≡ id
  law2 : θ ∘ map θ ≡ θ ∘ NaturalTransformation.η μ

module WithMonad {a b} {C : Category a b} {M : Monad C} where

  open Monad M renaming (assoc to M-assoc)
  open Algebra
  open Category C hiding (_∘_; id; idˡ; idʳ; assoc)
  open IsCategory (Category.is-category C)

  record AlgebraMorphism
    (A B : Algebra M) : Set (a ⊔ b) where
   constructor algebra-morphism
   field
    f : C [ Algebra.A A , Algebra.A B ]
    .good : f ∘ θ A ≡ θ B ∘ Monad.map M f

  am-equal'' : ∀ {A B} → ∀ {a b} 
    .{ag : (a ∘ θ A ≡ θ B ∘ Monad.map M a)}
    .{bg : (b ∘ θ A ≡ θ B ∘ Monad.map M b)}
    → a ≡ b
    → algebra-morphism {A} {B} a ag
     ≡ algebra-morphism {A} {B} b bg
  am-equal'' refl = refl

  am-equal : ∀ {A B} → (a b : AlgebraMorphism A B)
    → AlgebraMorphism.f a ≡ AlgebraMorphism.f b
    → a ≡ b
  am-equal (algebra-morphism a ag) (algebra-morphism b bg)  eq = 
    am-equal'' {a = a} {b = b}
    {ag = ag} {bg = bg}
    eq

  id-am : ∀ {A} → AlgebraMorphism A A
  id-am {Alg} = algebra-morphism id
      (trans (idˡ _) 
      (trans (sym (idʳ _)) 
        (cong (λ q → (θ Alg) ∘ q) 
          (sym natural-id))))
  compose-am : ∀ {A B C} → 
    AlgebraMorphism B C →
    AlgebraMorphism A B →
    AlgebraMorphism A C
  compose-am {A} {B} {C} 
    (algebra-morphism a a-good) 
    (algebra-morphism b b-good) =
    algebra-morphism
      (a ∘ b) 
      (trans (assoc _ _ _) 
        (trans (cong (_∘_ a) b-good) 
        (trans
        (trans
        (trans
        (sym (assoc _ _ _))
        (cong (λ q → q ∘ map b) a-good))
        (assoc _ _ _))
        (cong (_∘_ (θ C)) (natural-compose _ _)))))

  .idˡ-am : ∀ {A B} (m : AlgebraMorphism A B) → compose-am id-am m ≡ m
  idˡ-am m = 
    am-equal (compose-am id-am m) m (idˡ _)

  .idʳ-am : ∀ {A B} (m : AlgebraMorphism A B) → compose-am m id-am ≡ m
  idʳ-am m = am-equal (compose-am m id-am) m
    (idʳ _)

  .assoc-am : ∀ {A B C D} 
    (a : AlgebraMorphism C D) 
    (b : AlgebraMorphism B C)
    (c : AlgebraMorphism A B)
    → compose-am (compose-am a b) c
    ≡ compose-am a (compose-am b c)
  assoc-am a b c = 
    am-equal 
      (compose-am (compose-am a b) c) 
      (compose-am a (compose-am b c))
      (assoc _ _ _) 

  AlgebraCat : Category _ _
  AlgebraCat = category 
    (Algebra M) 
    AlgebraMorphism
    (is 
      id-am
      compose-am 
      idˡ-am
      idʳ-am
      assoc-am)
