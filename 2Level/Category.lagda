\documentclass[letterpaper,UKenglish,cleveref, autoref]{lipics-v2019}

\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}

\begin{document}
\begin{code}
module 2Level.Category where

open import Level
open import Relation.Binary.Core using (REL; Rel)
open import Relation.Binary.Structures using (IsEquivalence)

\end{code}

\section{2 Levels?}

This is an exploration of categories where the objects are externally
known to consist of two parts, and so the morphisms and the notion of
equivalence follows suit. The ``interesting'' case is when these parts
are dependence. The non-dependent case is mildly interesting, as it
does not mix levels for certain constructions.

\begin{code}
record Category (o o′ ℓ ℓ′ e e′ : Level) : Set (suc (o ⊔ o′ ⊔ ℓ ⊔ ℓ′ ⊔ e ⊔ e′)) where
  eta-equality
  infix  4 _≈₀_ _⇒₀_
  infixr 9 _∘₀_
  infix 4 _⇒[_]_ _≈[_]_
  infixr 9 _∘₁_

  field
\end{code}
We unbundle everything.
\begin{code}
    Obj : Set o
\end{code}
The level is \emph{uniform} and not dependent. While having some dependence
here would be interesting, Agda is far from ready to deal with that.
\begin{code}
    DObj : Obj → Set o′
\end{code}
Likewise, the morphisms are unbundled.
\begin{code}
    _⇒₀_ : Obj → Obj → Set ℓ
    _⇒[_]_ : {a b : Obj} → DObj a → a ⇒₀ b → DObj b → Set ℓ′
\end{code}

Even identity and composition are unbundled!
\begin{code}
    id₀ : {a : Obj} → a ⇒₀ a
    id₁ : {a : Obj} {a′ : DObj a} → a′ ⇒[ id₀ ] a′

    _∘₀_ : {a b c : Obj} → b ⇒₀ c → a ⇒₀ b → a ⇒₀ c
    _∘₁_ : {a₀ b₀ c₀ : Obj} {a₁ : DObj a₀} {b₁ : DObj b₀} {c₁ : DObj c₀} →
      {f : b₀ ⇒₀ c₀} {g : a₀ ⇒₀ b₀} →
      b₁ ⇒[ f ] c₁ → a₁ ⇒[ g ] b₁ → a₁ ⇒[ f ∘₀ g ] c₁
\end{code}

\begin{code}
    _≈₀_ : {a b : Obj} → Rel (a ⇒₀ b) e
    _≈[_]_ : {a₀ b₀ : Obj} {a₁ : DObj a₀} {b₁ : DObj b₀} {f g : a₀ ⇒₀ b₀} →
      a₁ ⇒[ f ] b₁ → f ≈₀ g → a₁ ⇒[ g ] b₁ → Set e′
\end{code}

And we also need the laws. Let's start with the ones from the first level, which are
predictably the exact same as for a 1Cat.
\begin{code}
  field
    assoc₀     : ∀ {A B C D} {f : A ⇒₀ B} {g : B ⇒₀ C} {h : C ⇒₀ D} → (h ∘₀ g) ∘₀ f ≈₀ h ∘₀ (g ∘₀ f)
    sym-assoc₀ : ∀ {A B C D} {f : A ⇒₀ B} {g : B ⇒₀ C} {h : C ⇒₀ D} → h ∘₀ (g ∘₀ f) ≈₀ (h ∘₀ g) ∘₀ f
    identityˡ₀ : ∀ {A B} {f : A ⇒₀ B} → id₀ ∘₀ f ≈₀ f
    identityʳ₀ : ∀ {A B} {f : A ⇒₀ B} → f ∘₀ id₀ ≈₀ f
    identity²₀ : ∀ {A} → id₀ ∘₀ id₀ {A} ≈₀ id₀ {A}
    equiv₀     : ∀ {A B} → IsEquivalence (_≈₀_ {A} {B})
    ∘₀-resp-≈₀ : ∀ {A B C} {f h : B ⇒₀ C} {g i : A ⇒₀ B} → f ≈₀ h → g ≈₀ i → f ∘₀ g ≈₀ h ∘₀ i

  private
    module E {A} {B} = IsEquivalence (equiv₀ {A} {B})
    
  refl₀ = E.refl
  sym₀ = E.sym
  trans₀ = E.trans
\end{code}

And the higher ones.
\begin{code}
  field
    identityˡ₁ : {A B : Obj} {X : DObj A} {Y : DObj B} {f : A ⇒₀ B} {f′ : X ⇒[ f ] Y} →
      (id₁ ∘₁ f′) ≈[ identityˡ₀ ] f′
    identityʳ₁ : {A B : Obj} {X : DObj A} {Y : DObj B} {f : A ⇒₀ B} {f′ : X ⇒[ f ] Y} →
      (f′ ∘₁ id₁) ≈[ identityʳ₀ ] f′
    identity²₁ : {A : Obj} {X : DObj A} → (id₁ {a′ = X} ∘₁ id₁) ≈[ identity²₀ ] id₁
    assoc₁ : ∀ {A B C D W X Y Z} {f : C ⇒₀ D} {g : B ⇒₀ C} {h : A ⇒₀ B}
           → {f′ : Y ⇒[ f ] Z} → {g′ : X ⇒[ g ] Y} → {h′ : W ⇒[ h ] X}
           → (f′ ∘₁ g′) ∘₁ h′ ≈[ assoc₀ ] f′ ∘₁ (g′ ∘₁ h′)
    sym-assoc₁ : ∀ {A B C D W X Y Z} {f : C ⇒₀ D} {g : B ⇒₀ C} {h : A ⇒₀ B}
           → {f′ : Y ⇒[ f ] Z} → {g′ : X ⇒[ g ] Y} → {h′ : W ⇒[ h ] X}
           → f′ ∘₁ (g′ ∘₁ h′) ≈[ sym-assoc₀ ] (f′ ∘₁ g′) ∘₁ h′
    refl′ : ∀ {A B X Y} {f : A ⇒₀ B} {f′ : X ⇒[ f ] Y}
          → f′ ≈[ refl₀ ] f′
    sym′ : ∀ {A B X Y} {f g : A ⇒₀ B} {f′ : X ⇒[ f ] Y} {g′ : X ⇒[ g ] Y} {p : f ≈₀ g}
         → f′ ≈[ p ] g′ → g′ ≈[ sym₀ p ] f′
    trans′ : ∀ {A B X Y} {f g h : A ⇒₀ B} {f′ : X ⇒[ f ] Y} {g′ : X ⇒[ g ] Y} {h′ : X ⇒[ h ] Y}
               {p : f ≈₀ g} {q : g ≈₀ h}
           → f′ ≈[ p ] g′ → g′ ≈[ q ] h′ → f′ ≈[ trans₀ p q ] h′
    ∘′-resp-[]≈ : ∀ {A B C X Y Z} {f h : B ⇒₀ C} {g i : A ⇒₀ B}
                    {f′ : Y ⇒[ f ] Z} {h′ : Y ⇒[ h ] Z} {g′ : X ⇒[ g ] Y} {i′ : X ⇒[ i ] Y}
                    {p : f ≈₀ h} {q : g ≈₀ i}
                → f′ ≈[ p ] h′ → g′ ≈[ q ] i′ → f′ ∘₁ g′ ≈[ ∘₀-resp-≈₀ p q ] h′ ∘₁ i′

\end{code}

\section{Slice}

One driving example is that of slice categories, where there is some mixing
going on.

\begin{code}
open import Categories.Category.Core using () renaming (Category to 1Cat)

Slice : {o₁ ℓ₁ e₁ : Level} (C : 1Cat o₁ ℓ₁ e₁) → 1Cat.Obj C → Category o₁ ℓ₁ ℓ₁ e₁ e₁ e₁
Slice C x = record
  { Obj = 1Obj
  ; DObj = _⇒ x
  ; _⇒₀_ = _⇒_
  ; _⇒[_]_ = λ f h g → g ∘ h ≈ f 
  ; id₀ = id
  ; id₁ = C.identityʳ
  ; _∘₀_ = _∘_
  ; _∘₁_ = λ c∘f≈b b∘g≈a → C.sym-assoc ○ (C.∘-resp-≈ˡ c∘f≈b ○ b∘g≈a)
  ; _≈₀_ = _≈_
  ; _≈[_]_ = λ { {f = f} {g} _ _ _ → f ≈ g}
  ; assoc₀ = assoc
  ; sym-assoc₀ = sym-assoc
  ; identityˡ₀ = identityˡ
  ; identityʳ₀ = identityʳ
  ; identity²₀ = identity²
  ; equiv₀     = equiv
  ; ∘₀-resp-≈₀ = ∘-resp-≈
  ; identityˡ₁ = identityˡ
  ; identityʳ₁ = identityʳ
  ; identity²₁ = identity²
  ; assoc₁ = assoc
  ; sym-assoc₁ = sym-assoc
  ; refl′ = Equiv.refl
  ; sym′ = Equiv.sym
  ; trans′ = Equiv.trans
  ; ∘′-resp-[]≈ = ∘-resp-≈
  }
  where
    open 1Cat C renaming (Obj to 1Obj)
    module C = 1Cat C
    open C.HomReasoning

\end{code}

We can project out a 1Cat from a Category
\begin{code}
Cat⇒1Cat : {o₀ o₁ ℓ₀ ℓ₁ e₀ e₁ : Level} → Category o₀ o₁ ℓ₀ ℓ₁ e₀ e₁ → 1Cat o₀ ℓ₀ e₀
Cat⇒1Cat C = record
  { Obj = Obj
  ; _⇒_ = _⇒₀_
  ; _≈_ = _≈₀_
  ; id = id₀
  ; _∘_ = _∘₀_
  ; assoc = assoc₀
  ; sym-assoc = sym-assoc₀
  ; identityˡ = identityˡ₀
  ; identityʳ = identityʳ₀
  ; identity² = identity²₀
  ; equiv = equiv₀
  ; ∘-resp-≈ = ∘₀-resp-≈₀
  } where open Category C
\end{code}

More interestingly, we get a full Displayed Category.
\begin{code}
open import Categories.Category.Displayed

Cat⇒Disp : {o₀ o₁ ℓ₀ ℓ₁ e₀ e₁ : Level} (C : Category o₀ o₁ ℓ₀ ℓ₁ e₀ e₁) → Displayed (Cat⇒1Cat C) o₁ ℓ₁ e₁
Cat⇒Disp C = record
  { Obj[_] = DObj
  ; _⇒[_]_ = _⇒[_]_
  ; _≈[_]_ = _≈[_]_
  ; id′ = id₁
  ; _∘′_ = _∘₁_
  ; identityʳ′ = identityʳ₁
  ; identityˡ′ = identityˡ₁
  ; identity²′ = identity²₁
  ; assoc′ = assoc₁
  ; sym-assoc′ = sym-assoc₁
  ; refl′ = refl′
  ; sym′ = sym′
  ; trans′ = trans′
  ; ∘′-resp-[]≈ = ∘′-resp-[]≈
  } where open Category C
\end{code}
We also need all the laws too, but these can be filled-in later.
Notes:
\begin{itemize}
\item Is here a good place to also talk about levels tracking
indepence?
\end{itemize}
\end{document}
