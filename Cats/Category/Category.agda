module Cats.Category.Category where

open import Cats.Category hiding (category)

open import Level
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Cats.Functor hiding (category)

category : ∀ o m → Category (suc (o ⊔ m)) (m ⊔ o)
category o m = Category.category 
  (Category o m)
  (λ A B → Functor A B)
  (is 
    (Id _)
    _∘_
    (λ m → refl)
    (λ m → refl) 
    (λ x y z → refl))

import Data.Product as Prod
open Prod using (_,_)

_×_ : ∀ {o₁ m₁ o₂ m₂} → Category o₁ m₁ → Category o₂ m₂ 
    → Category (o₁ ⊔ o₂) (m₁ ⊔ m₂)
C × D = Category.category 
  (Prod._×_ C.Obj D.Obj) 
  (λ { (a₁ , a₂) (b₁ , b₂) → Prod._×_ (C [ a₁ , b₁ ]) (D [ a₂ , b₂ ]) }) 
  (is 
    (C.id , D.id) 
    (λ { (a₁ , a₂) (b₁ , b₂) → (C._∘_ a₁ b₁ , D._∘_ a₂ b₂) })
    (λ { (m₁ , m₂) → cong₂ _,_ (C.idˡ _) (D.idˡ _) })
    ((λ _ → cong₂ _,_ (C.idʳ _) (D.idʳ _) ))
    (λ _ _ _ → cong₂ _,_ (C.assoc _ _ _) (D.assoc _ _ _))) where
 module C = Category C
 module D = Category D
