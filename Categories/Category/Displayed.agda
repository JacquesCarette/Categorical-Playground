{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Displayed {o ℓ e} (B : Category o ℓ e) where

open import Data.Product
open import Level

open import Categories.Functor.Core

open Category B
open Equiv

-- A displayed category captures the idea of placing extra structure
-- over a base category. For example, the category of monoids can be
-- considered as the category of setoids with extra structure on the
-- objects and extra conditions on the morphisms.
record Displayed o′ ℓ′ e′ : Set (o ⊔ ℓ ⊔ e ⊔ suc (o′ ⊔ ℓ′ ⊔ e′)) where
  infix 4 _⇒[_]_ _≈[_]_
  infixr 9 _∘′_
  field
    Obj[_] : Obj → Set o′
    _⇒[_]_ : ∀ {X Y} → Obj[ X ] → X ⇒ Y → Obj[ Y ] → Set ℓ′
    _≈[_]_ : ∀ {A B X Y} {f g : A ⇒ B} → X ⇒[ f ] Y → f ≈ g → X ⇒[ g ] Y → Set e′

    id′ : ∀ {A} {X : Obj[ A ]} → X ⇒[ id ] X
    _∘′_ : ∀ {A B C X Y Z} {f : B ⇒ C} {g : A ⇒ B}
         → Y ⇒[ f ] Z → X ⇒[ g ] Y → X ⇒[ f ∘ g ] Z

    identityʳ′ : ∀ {A B X Y} {f : A ⇒ B} → {f′ : X ⇒[ f ] Y} → f′ ∘′ id′ ≈[ identityʳ ] f′
    identityˡ′ : ∀ {A B X Y} {f : A ⇒ B} → {f′ : X ⇒[ f ] Y} → id′ ∘′ f′ ≈[ identityˡ ] f′
    identity²′ : ∀ {A} {X : Obj[ A ]} → id′ {X = X} ∘′ id′ ≈[ identity² ] id′
    assoc′ : ∀ {A B C D W X Y Z} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
           → {f′ : Y ⇒[ f ] Z} → {g′ : X ⇒[ g ] Y} → {h′ : W ⇒[ h ] X}
           → (f′ ∘′ g′) ∘′ h′ ≈[ assoc ] f′ ∘′ (g′ ∘′ h′)
    sym-assoc′ : ∀ {A B C D W X Y Z} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
           → {f′ : Y ⇒[ f ] Z} → {g′ : X ⇒[ g ] Y} → {h′ : W ⇒[ h ] X}
           → f′ ∘′ (g′ ∘′ h′) ≈[ sym-assoc ] (f′ ∘′ g′) ∘′ h′

    refl′ : ∀ {A B X Y} {f : A ⇒ B} {f′ : X ⇒[ f ] Y}
          → f′ ≈[ refl ] f′
    sym′ : ∀ {A B X Y} {f g : A ⇒ B} {f′ : X ⇒[ f ] Y} {g′ : X ⇒[ g ] Y} {p : f ≈ g}
         → f′ ≈[ p ] g′ → g′ ≈[ sym p ] f′
    trans′ : ∀ {A B X Y} {f g h : A ⇒ B} {f′ : X ⇒[ f ] Y} {g′ : X ⇒[ g ] Y} {h′ : X ⇒[ h ] Y} {p : f ≈ g} {q : g ≈ h}
           → f′ ≈[ p ] g′ → g′ ≈[ q ] h′ → f′ ≈[ trans p q ] h′

    ∘′-resp-[]≈ : ∀ {A B C X Y Z} {f h : B ⇒ C} {g i : A ⇒ B}
                    {f′ : Y ⇒[ f ] Z} {h′ : Y ⇒[ h ] Z} {g′ : X ⇒[ g ] Y} {i′ : X ⇒[ i ] Y}
                    {p : f ≈ h} {q : g ≈ i}
                → f′ ≈[ p ] h′ → g′ ≈[ q ] i′ → f′ ∘′ g′ ≈[ ∘-resp-≈ p q ] h′ ∘′ i′

  -- We can treat any displayed category as a category if we bundle it appropriately
  Total : Set (o ⊔ o′)
  Total = Σ[ Carrier ∈ Obj ] Obj[ Carrier ]

  record Total⇒ (X Y : Total) : Set (ℓ ⊔ ℓ′) where
    constructor total⇒
    field
      {arr} : proj₁ X ⇒ proj₁ Y
      preserves : proj₂ X ⇒[ arr ] proj₂ Y

  open Total⇒

  ∫ : Category (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
  ∫ = record
    { Obj = Total
    ; _⇒_ = Total⇒
    ; _≈_ = λ f g → ∃[ p ] preserves f ≈[ p ] preserves g
    ; id = total⇒ id′
    ; _∘_ = λ f g → total⇒ (preserves f ∘′ preserves g)
    ; assoc = -, assoc′
    ; sym-assoc = -, sym-assoc′
    ; identityˡ = -, identityˡ′
    ; identityʳ = -, identityʳ′
    ; identity² = -, identity²′
    ; equiv = record
      { refl = -, refl′
      ; sym = λ p → -, sym′ (proj₂ p)
      ; trans = λ p q → -, trans′ (proj₂ p) (proj₂ q)
      }
    ; ∘-resp-≈ = λ p q → -, ∘′-resp-[]≈ (proj₂ p) (proj₂ q)
    }

  -- There is a functor from the displayed category to the base category
  display : Functor ∫ B
  display = record
    { F₀ = proj₁
    ; F₁ = arr
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = proj₁
    }
