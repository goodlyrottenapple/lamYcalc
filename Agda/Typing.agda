module Typing where

open import Data.Empty
open import Data.Product
open import Data.Nat
open import Data.List

open import Data.List.Any as Any
open Any.Membership-≡
open import Data.List.Any.Membership
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Function.Related as Related
open Related.EquationalReasoning
open import Data.List.Any.Properties

open import Relation.Binary.Core

open import Core
open import Core-Lemmas
open import Reduction


≡⟶-l : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂} -> (τ₁₁ ⟶ τ₁₂) ≡ (τ₂₁ ⟶ τ₂₂) -> τ₁₁ ≡ τ₂₁
≡⟶-l refl = refl

≡⟶-r : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂} -> (τ₁₁ ⟶ τ₁₂) ≡ (τ₂₁ ⟶ τ₂₂) -> τ₁₂ ≡ τ₂₂
≡⟶-r refl = refl

≡-×-l : ∀ {A B : Set} {x1 x2 : A} {y1 y2 : B} -> (x1 , y1) ≡ (x2 , y2) -> x1 ≡ x2
≡-×-l refl = refl

≡-×-r : ∀ {A B : Set} {x1 x2 : A} {y1 y2 : B} -> (x1 , y1) ≡ (x2 , y2) -> y1 ≡ y2
≡-×-r refl = refl

_≟T_ : Decidable {A = Type} _≡_
σ ≟T σ   = yes refl
σ ≟T (_ ⟶ _) = no λ()
(_ ⟶ _) ≟T σ = no λ()
(τ₁₁ ⟶ τ₁₂) ≟T (τ₂₁ ⟶ τ₂₂) with τ₁₁ ≟T τ₂₁ | τ₁₂ ≟T τ₂₂
(τ₁₁ ⟶ τ₁₂) ≟T (.τ₁₁ ⟶ .τ₁₂) | yes refl | yes refl = yes refl
(τ₁₁ ⟶ τ₁₂) ≟T (.τ₁₁ ⟶ τ₂₂) | yes refl | no τ₁₂≠τ₂₂ = no (λ eq → τ₁₂≠τ₂₂ (≡⟶-r eq))
(τ₁₁ ⟶ τ₁₂) ≟T (τ₂₁ ⟶ τ₂₂) | no τ₁₁≠τ₂₁ | _ = no (λ eq → τ₁₁≠τ₂₁ (≡⟶-l eq))

Ctxt = List (Atom × Type)

dom : Ctxt -> FVars
dom = Data.List.map proj₁

data Wf_Ctxt : Ctxt -> Set where
  nil : Wf_Ctxt []
  cons : ∀ {Γ x τ} -> (x∉ : x ∉ dom Γ) -> Wf_Ctxt Γ ->
    Wf_Ctxt ((x , τ) ∷ Γ)


data _⊢_∶_ : Ctxt -> PTerm -> Type -> Set where
  var : ∀ {Γ x τ} -> Wf_Ctxt Γ -> (x , τ) ∈ Γ -> Γ ⊢ fv x ∶ τ
  app : ∀ {Γ t1 t2 τ₁ τ₂} -> Γ ⊢ t1 ∶ (τ₁ ⟶ τ₂) -> Γ ⊢ t2 ∶ τ₁ -> Γ ⊢ (app t1 t2) ∶ τ₂
  abs : ∀ {Γ τ₁ τ₂} (L : FVars) -> ∀ {t} ->
    ( cf : ∀ {x} -> (x∉L : x ∉ L) -> ((x , τ₁) ∷ Γ) ⊢ t ^' x ∶ τ₂ ) -> Γ ⊢ lam t ∶ (τ₁ ⟶ τ₂)
  Y : ∀ {Γ τ} -> Wf_Ctxt Γ -> Γ ⊢ Y τ ∶ ((τ ⟶ τ) ⟶ τ)

typ-term : ∀ {Γ m τ} -> Γ ⊢ m ∶ τ -> Term m
typ-term (var _ _) = var
typ-term (app Γ⊢t1∶τ₁⟶τ₂ Γ⊢t2∶τ₁) = app (typ-term Γ⊢t1∶τ₁⟶τ₂) (typ-term Γ⊢t2∶τ₁)
typ-term (abs L cf) = lam L (λ {x} x∉L → typ-term (cf x∉L))
typ-term (Y _) = Y

map-∈ : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y xs} →
         (∃ λ x → x ∈ xs × y ≡ f x) -> y ∈ Data.List.map f xs
map-∈ {a} {b} {A} {B} {f = f} {y} {xs} x∈xs = (↔⇒ {implication} map-∈↔) x∈xs

∉-dom : ∀ {L x τ} -> x ∉ dom L -> (x , τ) ∉ L
∉-dom {Γ} {x} {τ} x∉domL xτ∈L = x∉domL (map-∈ ((x , τ) , (xτ∈L , refl)))

var-typ-≡ : ∀ {x y τ₁ τ₂ Γ} -> ((x , τ₁) ∷ Γ) ⊢ fv y ∶ τ₂ -> x ≡ y -> τ₁ ≡ τ₂
var-typ-≡ {x} {.x} {τ₁} {τ₂} {Γ} (var (cons x∉ wf-Γ) x∈x∷Γ) refl with τ₂ ≟T τ₁
var-typ-≡ (var (cons x∉ wf-Γ) x∈x∷Γ) refl | yes refl = refl
var-typ-≡ {x} {.x} {τ₁} {τ₂} {Γ} (var (cons x∉ wf-Γ) x∈x∷Γ) refl | no τ₂≠τ₁ = ⊥-elim (contr x∈x∷Γ)
  where
  contr : (x , τ₂) ∉ (x , τ₁) ∷ Γ
  contr = ∉-∷ _ _ (λ xτ₂≡xτ₁ → τ₂≠τ₁ (≡-×-r xτ₂≡xτ₁)) (∉-dom x∉)


wf-cons : ∀ {Γ x τ} -> Wf_Ctxt ((x , τ) ∷ Γ) -> Wf_Ctxt Γ
wf-cons (cons x∉ wf-Γ) = wf-Γ


⊢-imp-wfΓ : ∀ {Γ m τ} -> Γ ⊢ m  ∶ τ -> Wf_Ctxt Γ
⊢-imp-wfΓ (var wf-Γ _) = wf-Γ
⊢-imp-wfΓ (app Γ⊢m:τ Γ⊢m:τ₁) = ⊢-imp-wfΓ Γ⊢m:τ₁
⊢-imp-wfΓ (abs {Γ} {τ₁} {τ₂} L cf) = wf-cons ih
  where
  x = ∃fresh L

  x∉ : x ∉ L
  x∉ = ∃fresh-spec L

  ih : Wf_Ctxt ((x , τ₁) ∷ Γ)
  ih = ⊢-imp-wfΓ (cf x∉)

⊢-imp-wfΓ (Y wf-Γ) = wf-Γ

subst-typ : ∀ {Γ m n τ₁ τ₂ x} -> Term m -> ((x , τ₁) ∷ Γ) ⊢ m ∶ τ₂ -> Γ ⊢ n ∶ τ₁ ->
  Γ ⊢ (m [ x ::= n ]) ∶ τ₂
subst-typ {x = x} var (var {_} {y} wf-x∷Γ xτ∈Γ) Γ⊢n∶τ₁ with x ≟ y
subst-typ var (var wf-x∷Γ xτ∈Γ) Γ⊢n∶τ₁ | yes refl rewrite
  var-typ-≡ (var wf-x∷Γ xτ∈Γ) refl = Γ⊢n∶τ₁
subst-typ {Γ} {.x} {_} {τ₁} {τ₂} {x} var (var {.x} {y} wf-x∷Γ yτ₂∈Γ) Γ⊢n∶τ₁ | no x≠y =
  var (⊢-imp-wfΓ Γ⊢n∶τ₁) (∈-∷-elim _ _ (λ xτ₂≡yτ₁ → x≠y (≡-×-l xτ₂≡yτ₁)) yτ₂∈Γ)
subst-typ (lam L cf) (abs L₁ cf₁) Γ⊢n∶τ₁ = {!   !}
subst-typ (app term-m term-m₁) (app x∷Γ⊢m∶τ₂ x∷Γ⊢m∶τ₃) Γ⊢n∶τ₁ =
  app (subst-typ term-m x∷Γ⊢m∶τ₂ Γ⊢n∶τ₁) (subst-typ term-m₁ x∷Γ⊢m∶τ₃ Γ⊢n∶τ₁)
subst-typ Y (Y (cons x∉ wf-Γ)) Γ⊢n∶τ₁ = Y wf-Γ


^-typ : ∀ {Γ L m n τ₁ τ₂}  -> ( cf : ∀ {x} -> (x∉L : x ∉ L) -> ((x , τ₁) ∷ Γ) ⊢ m ^' x ∶ τ₂ ) ->
  Γ ⊢ n ∶ τ₁ -> Γ ⊢ m ^ n ∶ τ₂
^-typ {Γ} {L} {m} {n} {τ₁} {τ₂} cf Γ⊢n∶τ₁ = body
  where
  x = ∃fresh (L ++ FV m)

  x∉ : x ∉ (L ++ FV m)
  x∉ = ∃fresh-spec (L ++ FV m)

  body : Γ ⊢ m ^ n ∶ τ₂
  body rewrite
    subst-intro x n m (∉-cons-r L _ x∉) (typ-term Γ⊢n∶τ₁) =
    subst-typ (typ-term (cf (∉-cons-l _ _ x∉))) (cf (∉-cons-l _ _ x∉)) Γ⊢n∶τ₁

->β-typ : ∀ {Γ m m' τ} -> Γ ⊢ m ∶ τ -> m ->β m' -> Γ ⊢ m' ∶ τ
->β-typ (app Γ⊢m∶τ Γ⊢n∶τ₁) (redL x m->βm') = app (->β-typ Γ⊢m∶τ m->βm') Γ⊢n∶τ₁
->β-typ (app Γ⊢m∶τ Γ⊢m∶τ₁) (redR x m->βm') = app Γ⊢m∶τ (->β-typ Γ⊢m∶τ₁ m->βm')
->β-typ (abs L cf) (abs L₁ cf₁) =
  abs (L ++ L₁) (λ {x} x∉L → ->β-typ (cf (∉-cons-l _ _ x∉L)) (cf₁ (∉-cons-r L _ x∉L)))
->β-typ (app {Γ} {_} {n} (abs L {m} cf) Γ⊢n∶τ₁) (beta term-lam-x term-cf) = ^-typ {m = m} cf Γ⊢n∶τ₁
->β-typ (app (Y wf-Γ) Γ⊢m∶τ₁) (Y term-m) = app Γ⊢m∶τ₁ (app (Y wf-Γ) Γ⊢m∶τ₁)
