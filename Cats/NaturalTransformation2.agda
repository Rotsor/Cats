module Cats.NaturalTransformation2 where

open import Data.Bool
open import Cats.Category
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; trans; cong; sym)

data SegmentMorphism : Bool → Bool → Set where
  refl : ∀ b → SegmentMorphism b b
  less : SegmentMorphism false true

_∘_ : ∀ {a b c }
  → SegmentMorphism b c 
  → SegmentMorphism a b
  → SegmentMorphism a c
refl _ ∘ g = g
less ∘ refl ._ = less

module Local where
  assoc : ∀ {a b c d}
    (x : SegmentMorphism c d)
    (y : SegmentMorphism b c)
    (z : SegmentMorphism a b)
    → (x ∘ y) ∘ z ≡ x ∘ (y ∘ z)
  assoc {a} {b} {.d} {d} (refl .d) y z = PropEq.refl
  assoc less (refl .false) z = PropEq.refl

segment-category : Category _ _
segment-category = category 
  Bool 
  SegmentMorphism
  (is
  (refl _) 
  _∘_ 
  (λ _ → PropEq.refl) 
  (λ { {.b} {b} (refl .b) → PropEq.refl 
    ; less → PropEq.refl }) 
  assoc) where open Local

module WithCategories
  {a b c d} (C : Category a b) (D : Category c d) where

  import Cats.Category.Category as CatCat
  open CatCat
  open import Cats.Functor hiding (_∘_)
  LC = segment-category × C
  Mystery-Functor = Functor LC D
  open import Cats.NaturalTransformation
  open import Level
  record NT : Set (a ⊔ b ⊔ c ⊔ d) where
   constructor mk-nt
   field
    F : Functor C D
    G : Functor C D
    nt : NaturalTransformation F G
  .nt-equal' : 
    ∀ F₁ F₂
    G₁ G₂
    nt₁ nt₂
    (f-eq : F₁ ≡ F₂)
    → (g-eq : G₁ ≡ G₂)
    → PropEq.subst₂ NaturalTransformation f-eq g-eq nt₁ ≡ nt₂
    → mk-nt F₁ G₁ nt₁ ≡ mk-nt F₂ G₂ nt₂
  nt-equal' .F₂ F₂ .G₂ G₂ .nt₂ nt₂ PropEq.refl PropEq.refl PropEq.refl = PropEq.refl

  .nt-equal : 
    ∀ (NT₁ NT₂ : NT) 
    → let F₁ = NT.F NT₁; F₂ = NT.F NT₂;
           G₁ = NT.G NT₁; G₂ = NT.G NT₂;
           nt₁ = NT.nt NT₁; nt₂ = NT.nt NT₂ in
    (f-eq : F₁ ≡ F₂)
    → (g-eq : G₁ ≡ G₂)
    → PropEq.subst₂ NaturalTransformation f-eq g-eq nt₁ ≡ nt₂
    → NT₁ ≡ NT₂
  nt-equal a b eq1 eq2 eq3 = nt-equal' (NT.F a) (NT.F b) (NT.G a) (NT.G b) (NT.nt a) (NT.nt b) eq1 eq2 eq3

  open import Data.Product using (_,_)

  hh : Mystery-Functor → NT
  hh mf = record { F = F; G = G; nt = n-trans } where

    F : Functor C D
    F = record { 
      O = λ x → Functor.O mf (false , x); 
      map = λ m → Functor.map mf (refl _ , m); 
      natural-id = Functor.natural-id mf; 
      natural-compose = λ f g → Functor.natural-compose mf _ _ }

    G : Functor C D
    G = record { 
      O = λ x → Functor.O mf (true , x); 
      map = λ m → Functor.map mf (refl _ , m); 
      natural-id = Functor.natural-id mf; 
      natural-compose = λ f g → Functor.natural-compose mf _ _ }

    n-trans : NaturalTransformation F G
    n-trans = record { 
      η = Functor.map mf (less , Category.id C); 
      natural = λ m → trans (Functor.natural-compose mf _ _) 
      (trans (cong (λ q → Functor.map mf (less , q)) 
      (trans (Category.idˡ C m) (sym (Category.idʳ C m)))
      ) (sym (Functor.natural-compose mf _ _))) }

  open import Function using (_⟨_⟩_)

  gg : NT → Mystery-Functor
  gg nt = record { 
    O = λ { (false , o) → Functor.O F o; (true , o) → Functor.O G o };
    map = λ { 
      {(true , ao)} {(._ , bo)} (refl ._ , mr) → Functor.map G mr; 
      {(false , ao)} {(._ , bo)} (refl ._ , mr) → Functor.map F mr; 
      {(._ , ao)} {(._ , bo)} (less , mr) → 
        Functor.map G mr ∘'
        NaturalTransformation.η n-tran  }; 
    natural-id = λ 
      { {(false , ao)} → F.natural-id
      ; {(true , ao)} → G.natural-id }; 
    natural-compose = λ { 
      {._ , ao} {._ , bo} {._ , co} (refl true , m₁) (refl .true , m₂) 
        → G.natural-compose _ _;
      {._ , ao} {._ , bo} {._ , co} (refl true , m₁) (less , m₂) →
          trans (sym (assoc _ _ _))
          (cong (λ q → q ∘' η) (
              G.natural-compose m₁ m₂));
      {._ , ao} {._ , bo} {._ , co} (refl false , m₁) (refl .false , m₂) 
        → F.natural-compose _ _;
      {._ , ao} {._ , bo} {._ , co} (less , m₁) (refl .false , m₂) → 
        assoc _ _ _  ⟨ trans ⟩
        (cong (λ q → G.map m₁ ∘' q) (NTR.natural _) ⟨ trans ⟩
        (sym (assoc _ _ _) ⟨ trans ⟩
        cong (λ q → q ∘' η) 
          (G.natural-compose _ _))) 
    } } where
    module F = Functor (NT.F nt)
    module G = Functor (NT.G nt)
    F = NT.F nt
    G = NT.G nt
    module NTR = NaturalTransformation (NT.nt nt)
    n-tran = NT.nt nt
    open NaturalTransformation n-tran using (η)
    open IsCategory (Category.is-category D) using (assoc) renaming (_∘_ to _∘'_)
    

  reverse1 : ∀ x → gg (hh x) ≡ x
  reverse1 x = Cats.Functor.equal 
    (gg (hh x)) x 
    (λ { (false , o) → PropEq.refl; (true , o) → PropEq.refl })
    λ { 
      {._ , o₁} {._ , o₂} (refl false , m) → PropEq.refl ;
      {._ , o₁} {._ , o₂} (refl true , m) → PropEq.refl ;
      {._ , o₁} {._ , o₂} (less , m) → PropEq.refl
    }

  .reverse2 : ∀ x → hh (gg x) ≡ x
  reverse2 x = nt-equal
    (hh (gg x))
    x
    PropEq.refl
    PropEq.refl
    (Cats.NaturalTransformation.equal 
    (λ o → trans (cong (λ q → q ∘₁ η) G.natural-id) (Category.idˡ D _))) where 
    module G = Functor (NT.G x)
    open NaturalTransformation (NT.nt x) using (η)
    open Category D using () renaming (_∘_ to _∘₁_)
