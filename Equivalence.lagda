\documentclass[letterpaper,UKenglish,cleveref, autoref]{lipics-v2019}

\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}

\begin{document}
\begin{code}
module Equivalence where

open import Level
open import Data.Product using (Σ; proj₂; _,_)
open import Function.Equality using (Π; _⟨$⟩_; _⟶_)
open import Function.Surjection using (Surjective)

open import Categories.Category
open import Categories.Category.Equivalence
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties hiding (EssentiallySurjective)
open import Categories.Morphism using (module ≅)
open import Categories.Morphism.Reasoning hiding (push-eq)
open import Categories.NaturalTransformation using (module NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (sym)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
private
  variable
    o ℓ e o′ ℓ′ e′ : Level
\end{code}

\section{Exploring}

This is an exploration of the concept of categorical equivalence.
The first two things to contrast are those of equivalence based on
inverses, and those on essential surjectivity.

We end up proving, contrary to expectations, that they are... the same.

Why is that? And why is this not in the main references? Because our
definition of ``Essentially Surjective'' is as follows
\begin{code}
EssentiallySurjective : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → Functor C D → Set _
EssentiallySurjective {C = C} {D = D} F = (d : Category.Obj D) → Σ C.Obj (λ c → Functor.F₀ F c ≅ d)
  where
  open Categories.Morphism D
  module C = Category C
\end{code}
What this gives is a \emph{coherent choice} of inverse objects to |d|. The usual
definition of essential surjectivity is a \emph{mere existence} statement that has less
power.
\appendix

\section{Equivalence of strong equivalence and Fully-Faithful + Essentially
Surjective}
\begin{code}
module _ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F : Functor C D} where

  open Categories.Morphism._≅_
  open Category D
  open Functor F
  open Surjective
  private
    module C = Category C
    module CE = C.Equiv
    module RC = C.HomReasoning

  EssSurj×FullyFaithful→StrongEquiv : EssentiallySurjective F → Full F → Faithful F → StrongEquivalence C D
  EssSurj×FullyFaithful→StrongEquiv ess full faith = record
    { F = F
    ; G = G
    ; weak-inverse = record
      { F∘G≈id = niHelper record
        { η = fwd
        ; η⁻¹ = bwd
        ; commute = λ {X} {Y} f → let open HomReasoning in
          let FX = fwd X
              FY = fwd Y
              TY = bwd Y in begin
          FY ∘ F₁ (F⟶ ⟨$⟩ TY ∘ f ∘ FX) ≈⟨ (refl⟩∘⟨ right-inverse-of full (TY ∘ f ∘ FX)) ⟩
          FY ∘ (TY ∘ f ∘ FX)           ≈⟨ cancelˡ D (isoʳ (proj₂ (ess Y))) ⟩
          f ∘ FX ∎
        ; iso = λ d → iso (proj₂ (ess d))
        }
      ; G∘F≈id = niHelper record
        { η = λ c → F⟶ ⟨$⟩ fwd (F₀ c)
        ; η⁻¹ = λ c → F⟶ ⟨$⟩ bwd (F₀ c)
        ; commute = λ {X} {Y} f → let open C.HomReasoning in begin
          (F⟶ ⟨$⟩ fwd (F₀ Y)) C.∘ (F⟶ ⟨$⟩ (bwd (F₀ Y) ∘ F₁ f ∘ fwd (F₀ X)))  ≈⟨ full-hom ⟩
          F⟶ ⟨$⟩ fwd (F₀ Y) ∘ (bwd (F₀ Y) ∘ F₁ f ∘ fwd (F₀ X))               ≈⟨ Π.cong F⟶ (cancelˡ D (isoʳ (proj₂ (ess _)))) ⟩
          F⟶ ⟨$⟩ F₁ f ∘ fwd (F₀ X)                                           ≈˘⟨ full-hom ⟩
          (F⟶ ⟨$⟩ F₁ f) C.∘ (F⟶ ⟨$⟩ fwd (F₀ X))                              ≈⟨ (faith _ f (right-inverse-of full (F₁ f)) ⟩∘⟨refl) ⟩
          f C.∘ (F⟶ ⟨$⟩ fwd (F₀ X)) ∎
        ; iso = λ c →
          let x = bwd (F₀ c)
              y = fwd (F₀ c) in record
         { isoˡ = RC.begin
           (F⟶ ⟨$⟩ x) C.∘ (F⟶ ⟨$⟩ y) RC.≈⟨ full-hom ⟩
           F⟶ ⟨$⟩ (x ∘ y)            RC.≈⟨ Π.cong F⟶ (isoˡ (proj₂ (ess (F₀ c)))) ⟩
           F⟶ ⟨$⟩ id                 RC.≈⟨ Π.cong F⟶ (Equiv.sym identity) ⟩
           F⟶ ⟨$⟩ (F₁ C.id)          RC.≈⟨ faith _ _ (right-inverse-of full (F₁ C.id)) ⟩
           C.id                      RC.∎
         ; isoʳ = let open C.HomReasoning in begin
           (F⟶ ⟨$⟩ fwd (F₀ c)) C.∘ (F⟶ ⟨$⟩ bwd (F₀ c)) ≈⟨ full-hom ⟩
           F⟶ ⟨$⟩ fwd (F₀ c) ∘ bwd (F₀ c)              ≈⟨ Π.cong F⟶ (isoʳ (proj₂ (ess (F₀ c)))) ⟩
           F⟶ ⟨$⟩ id                                   ≈⟨ Π.cong F⟶ (Equiv.sym identity) ⟩
           F⟶ ⟨$⟩ F₁ C.id                              ≈⟨ faith _ _ (right-inverse-of full (F₁ C.id)) ⟩
           C.id ∎
         }
        }
      }
    }
    where
    F⟶ : ∀ {a b} → hom-setoid ⟶ C.hom-setoid {a} {b}
    F⟶ = from full
    G : Functor D C
    G = EssSurj×Full×Faithful⇒Invertible F ess full faith
    fwd : (d : Obj) → D [ Functor.F₀ (F ∘F G) d , d ]
    fwd d = from (proj₂ (ess d))
    bwd : (d : Obj) → D [ d , Functor.F₀ (F ∘F G) d ]
    bwd d = to (proj₂ (ess d))
    full-hom : {a b c : C.Obj} {y : F₀ a ⇒ F₀ b} {x : F₀ b ⇒ F₀ c} → (F⟶ ⟨$⟩ x) C.∘ (F⟶ ⟨$⟩ y) C.≈ F⟶ ⟨$⟩ x ∘ y
    full-hom {y = y} {x} = let open HomReasoning in faith _ _ (begin
      F₁ ((F⟶ ⟨$⟩ x) C.∘ (F⟶ ⟨$⟩ y)) ≈⟨ homomorphism ⟩
      F₁ (F⟶ ⟨$⟩ x) ∘ F₁ (F⟶ ⟨$⟩ y)  ≈⟨ (right-inverse-of full x ⟩∘⟨ right-inverse-of full y) ⟩
      x ∘ y                          ≈˘⟨ right-inverse-of full (x ∘ y) ⟩
      F₁ (F⟶ ⟨$⟩ x ∘ y) ∎)
\end{code}
And, in the opposite direction, we can do all three parts.  Separate out
Faithful, as we'll want to use it in both directions in the proof of Full.

\begin{code}
module _ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} where
  open StrongEquivalence

  StrongEquiv→Faithful : (e : StrongEquivalence C D) → Faithful (F e)
  StrongEquiv→Faithful e f g Ff≈Fg = push-eq W.G∘F≈id (G.F-resp-≈ Ff≈Fg)
    where
    module G = Functor (G e)
    module W = WeakInverse (weak-inverse e)

module _ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} where
  open StrongEquivalence

  StrongEquiv→Full : (e : StrongEquivalence C D) → Full (F e)
  StrongEquiv→Full e {X} {Y} = record
    { from = record
      { _⟨$⟩_ = λ f → GF⇒.η Y ∘ G.₁ f ∘ GF⇐.η X
      ; cong = λ i≈j → ∘-resp-≈ʳ (∘-resp-≈ˡ (G.F-resp-≈ i≈j))
      }
      -- take g : FX⇒FY
    ; right-inverse-of = λ g →
      let f = GF⇒.η Y ∘ G.₁ g ∘ GF⇐.η X in
      let H = G e ∘F F e in
      let module H = Functor H in
      StrongEquiv→Faithful (sym e) (F.₁ f) g (begin
        G.₁ (F.₁ (GF⇒.η Y ∘ G.₁ g ∘ GF⇐.η X))                         ≈⟨ H.homomorphism ⟩
        G.₁ (F.₁ (GF⇒.η Y)) ∘ G.₁ (F.₁ (G.₁ g ∘ GF⇐.η X))             ≈⟨ refl⟩∘⟨ H.homomorphism ⟩
        G.₁ (F.₁ (GF⇒.η Y)) ∘ G.₁ (F.₁ (G.₁ g)) ∘ G.₁ (F.₁ (GF⇐.η X)) ≈⟨ Equiv.sym (F≃id-comm₁ W.G∘F≈id) ⟩∘⟨ refl⟩∘⟨ Equiv.sym (F≃id-comm₂ W.G∘F≈id) ⟩
        GF⇒.η (G.₀ (F.₀ Y)) ∘ G.₁ (F.₁ (G.₁ g)) ∘ GF⇐.η (G.₀ (F.₀ X)) ≈⟨ (refl⟩∘⟨ GF⇐.sym-commute (G.₁ g)) ⟩
        GF⇒.η (G.₀ (F.₀ Y)) ∘ GF⇐.η (G.₀ (F.₀ Y)) ∘ G.₁ g             ≈⟨ cancelˡ C (W.G∘F≈id.iso.isoʳ _) ⟩
        G.₁ g ∎)
    }
    where
    module C = Category C
    module F = Functor (F e)
    module G = Functor (G e)
    module W = WeakInverse (weak-inverse e)
    module GF⇒ = NaturalTransformation (W.G∘F≈id.F⇒G)
    module GF⇐ = NaturalTransformation (W.G∘F≈id.F⇐G)
    open Category C
    open HomReasoning

  StrongEquiv→EssSurj : (e : StrongEquivalence C D) → EssentiallySurjective (F e)
  StrongEquiv→EssSurj e d = G.₀ d , W.F∘G≈id.FX≅GX {d}
    where
    module G = Functor (G e)
    module W = WeakInverse (weak-inverse e)
\end{code}
\end{document}
