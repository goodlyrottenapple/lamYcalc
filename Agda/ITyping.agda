module ITyping where

open import Data.List
open import Data.Product
open import Data.List.Any as Any
open Any.Membership-≡
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


open import Core
open import Typing

data IType : Set
data ITypeₛ : Set


data IType where
  o : IType
  _~>_ : (s : ITypeₛ) -> (t : IType) -> IType

data ITypeₛ where
   ∩ : List IType -> ITypeₛ

ω = ∩ []

∩' : IType -> ITypeₛ
∩' x = ∩ (x ∷ [])

~>-inj-l : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂} -> (τ₁₁ ~> τ₁₂) ≡ (τ₂₁ ~> τ₂₂) -> τ₁₁ ≡ τ₂₁
~>-inj-l refl = refl

~>-inj-r : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂} -> (τ₁₁ ~> τ₁₂) ≡ (τ₂₁ ~> τ₂₂) -> τ₁₂ ≡ τ₂₂
~>-inj-r refl = refl


ICtxt = List (Atom × ITypeₛ)


data Wf-ICtxt : ICtxt -> Set where
  nil : Wf-ICtxt []
  cons : ∀ {Γ x τ} -> (x∉ : x ∉ dom Γ) -> Wf-ICtxt Γ ->
    Wf-ICtxt ((x , τ) ∷ Γ)


data _∷'_ : IType -> Type -> Set
data _∷'ₛ_ : ITypeₛ -> Type -> Set

data _∷'_ where
  base : o ∷' σ
  arr : ∀ {δ τ A B} -> δ ∷'ₛ A -> τ ∷' B -> (δ ~> τ) ∷' (A ⟶ B)

data _∷'ₛ_ where
  int : ∀{τᵢ A} -> (c : ∀ {τ} -> (τ∈τᵢ : τ ∈ τᵢ) -> τ ∷' A) -> ∩ τᵢ ∷'ₛ A


data _⊩_∶_ : ICtxt -> PTerm -> IType -> Set where
  var : ∀ {Γ x τ} {τᵢ : List IType} -> Wf-ICtxt Γ -> (x , (∩ τᵢ)) ∈ Γ -> τ ∈ τᵢ -> Γ ⊩ fv x ∶ τ
  app : ∀ {Γ s t τᵢ τ} -> Γ ⊩ s ∶ ((∩ τᵢ) ~> τ) -> (c : ∀ {τ'} -> (τ'∈τᵢ : τ' ∈ τᵢ) -> Γ ⊩ t ∶ τ') ->
    Γ ⊩ (app s t) ∶ τ
  abs : ∀ {Γ δ τ} (L : FVars) -> ∀ {t} ->
    ( cf : ∀ {x} -> (x∉L : x ∉ L) -> ((x , δ) ∷ Γ) ⊩ t ^' x ∶ τ ) -> Γ ⊩ lam t ∶ (δ ~> τ)
  Y : ∀ {Γ A τ₁ τ₂} -> Wf-ICtxt Γ -> τ₁ ∷'ₛ (A ⟶ A) -> τ₂ ∷' A -> Γ ⊩ Y A ∶ (τ₁ ~> τ₂) -- dunno abou this definition??
