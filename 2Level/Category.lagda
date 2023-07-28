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
    Hom : Obj → Obj → Set ℓ
    DHom : {a b : Obj} (a′ : DObj a) (b′ : DObj b) → Hom a b → Set ℓ′
\end{code}

Even identity and composition are unbundled!
\begin{code}
    id₀ : {a : Obj} → Hom a a
    id₁ : {a : Obj} {a′ : DObj a} → DHom a′ a′ (id₀ {a})

    _∘₀_ : {a b c : Obj} → Hom b c → Hom a b → Hom a c
    _∘₁_ : {a₀ b₀ c₀ : Obj} {a₁ : DObj a₀} {b₁ : DObj b₀} {c₁ : DObj c₀} →
      {f : Hom b₀ c₀} {g : Hom a₀ b₀} →
      DHom b₁ c₁ f → DHom a₁ b₁ g → DHom a₁ c₁ (f ∘₀ g)
\end{code}

\begin{code}
    _≈₀_ : {a b : Obj} → Rel (Hom a b) e
    _≈₁_ : {a₀ b₀ : Obj} {a₁ : DObj a₀} {b₁ : DObj b₀} {f g : Hom a₀ b₀} →
      REL (DHom a₁ b₁ f) (DHom a₁ b₁ g) e′
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
  ; Hom = _⇒_
  ; DHom = λ f g h → g ∘ h ≈ f 
  ; id₀ = id
  ; id₁ = C.identityʳ
  ; _∘₀_ = _∘_
  ; _∘₁_ = λ c∘f≈b b∘g≈a → C.sym-assoc ○ (C.∘-resp-≈ˡ c∘f≈b ○ b∘g≈a)
  ; _≈₀_ = _≈_
  ; _≈₁_ = λ { {f = f} {g} _ _ → f ≈ g}
  }
  where
    open 1Cat C using (_⇒_; id; _≈_; _∘_) renaming (Obj to 1Obj)
    module C = 1Cat C
    open C.HomReasoning

\end{code}
We also need all the laws too, but these can be filled-in later.
Notes:
\begin{itemize}
\item Is here a good place to also talk about levels tracking
indepence?
\end{itemize}
\end{document}
