module Typing where

open import Data.Empty
open import Data.Product
open import Data.Nat
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡
open import Data.List.Any.Membership
open import Relation.Nullary
open import Function.Related as Related
open Related.EquationalReasoning
open import Relation.Binary.Core

open import Core
open import Core-Lemmas
open import Reduction

⟶-inj-l : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂} -> (τ₁₁ ⟶ τ₁₂) ≡ (τ₂₁ ⟶ τ₂₂) -> τ₁₁ ≡ τ₂₁
⟶-inj-l refl = refl
------------------------------------------------------------------------------------

⟶-inj-r : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂} -> (τ₁₁ ⟶ τ₁₂) ≡ (τ₂₁ ⟶ τ₂₂) -> τ₁₂ ≡ τ₂₂
⟶-inj-r refl = refl
------------------------------------------------------------------------------------

×-inj-l : ∀ {A B : Set} {x1 x2 : A} {y1 y2 : B} -> (x1 , y1) ≡ (x2 , y2) -> x1 ≡ x2
×-inj-l refl = refl
------------------------------------------------------------------------------------

×-inj-r : ∀ {A B : Set} {x1 x2 : A} {y1 y2 : B} -> (x1 , y1) ≡ (x2 , y2) -> y1 ≡ y2
×-inj-r refl = refl
------------------------------------------------------------------------------------

_≟T_ : Decidable {A = Type} _≡_
σ ≟T σ   = yes refl
σ ≟T (_ ⟶ _) = no λ()
(_ ⟶ _) ≟T σ = no λ()
(τ₁₁ ⟶ τ₁₂) ≟T (τ₂₁ ⟶ τ₂₂) with τ₁₁ ≟T τ₂₁ | τ₁₂ ≟T τ₂₂
(τ₁₁ ⟶ τ₁₂) ≟T (.τ₁₁ ⟶ .τ₁₂) | yes refl | yes refl = yes refl
(τ₁₁ ⟶ τ₁₂) ≟T (.τ₁₁ ⟶ τ₂₂) | yes refl | no τ₁₂≠τ₂₂ =
  no (λ eq → τ₁₂≠τ₂₂ (⟶-inj-r eq))
(τ₁₁ ⟶ τ₁₂) ≟T (τ₂₁ ⟶ τ₂₂) | no τ₁₁≠τ₂₁ | _ = no (λ eq → τ₁₁≠τ₂₁ (⟶-inj-l eq))
------------------------------------------------------------------------------------

Ctxt = List (Atom × Type)
------------------------------------------------------------------------------------

dom : ∀ {A : Set} -> List (Atom × A) -> FVars
dom = Data.List.map proj₁
------------------------------------------------------------------------------------

data Wf-Ctxt : Ctxt -> Set where
  nil : Wf-Ctxt []
  cons : ∀ {Γ x τ} -> (x∉ : x ∉ dom Γ) -> Wf-Ctxt Γ ->
    Wf-Ctxt ((x , τ) ∷ Γ)
------------------------------------------------------------------------------------

data _⊢_∶_ : Ctxt -> PTerm -> Type -> Set where
  var : ∀ {Γ x τ} -> Wf-Ctxt Γ -> (x , τ) ∈ Γ -> Γ ⊢ fv x ∶ τ
  app : ∀ {Γ t1 t2 τ₁ τ₂} -> Γ ⊢ t1 ∶ (τ₁ ⟶ τ₂) -> Γ ⊢ t2 ∶ τ₁ ->
    Γ ⊢ (app t1 t2) ∶ τ₂
  abs : ∀ {Γ τ₁ τ₂} (L : FVars) -> ∀ {t} ->
    ( cf : ∀ {x} -> (x∉L : x ∉ L) -> ((x , τ₁) ∷ Γ) ⊢ t ^' x ∶ τ₂ ) ->
    Γ ⊢ lam t ∶ (τ₁ ⟶ τ₂)
  Y : ∀ {Γ τ} -> Wf-Ctxt Γ -> Γ ⊢ Y τ ∶ ((τ ⟶ τ) ⟶ τ)
------------------------------------------------------------------------------------

⊢-term : ∀ {Γ m τ} -> Γ ⊢ m ∶ τ -> Term m
⊢-term (var _ _) = var
⊢-term (app Γ⊢t1∶τ₁⟶τ₂ Γ⊢t2∶τ₁) = app (⊢-term Γ⊢t1∶τ₁⟶τ₂) (⊢-term Γ⊢t2∶τ₁)
⊢-term (abs L cf) = lam L (λ {x} x∉L → ⊢-term (cf x∉L))
⊢-term (Y _) = Y
------------------------------------------------------------------------------------

map-∈ : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y xs} →
         (∃ λ x → x ∈ xs × y ≡ f x) -> y ∈ Data.List.map f xs
map-∈ {a} {b} {A} {B} {f = f} {y} {xs} x∈xs = (↔⇒ {implication} map-∈↔) x∈xs
------------------------------------------------------------------------------------

∉-dom : ∀ {A : Set} {L x τ} -> x ∉ dom {A} L -> (x , τ) ∉ L
∉-dom {A} {Γ} {x} {τ} x∉domL xτ∈L = x∉domL (map-∈ ((x , τ) , (xτ∈L , refl)))
------------------------------------------------------------------------------------

var-⊢-≡ : ∀ {x y τ₁ τ₂ Γ} -> ((x , τ₁) ∷ Γ) ⊢ fv y ∶ τ₂ -> x ≡ y -> τ₁ ≡ τ₂
var-⊢-≡ {x} {.x} {τ₁} {τ₂} {Γ} (var (cons x∉ wf-Γ) x∈x∷Γ) refl with τ₂ ≟T τ₁
var-⊢-≡ (var (cons x∉ wf-Γ) x∈x∷Γ) refl | yes refl = refl
var-⊢-≡ {x} {.x} {τ₁} {τ₂} {Γ} (var (cons x∉ wf-Γ) x∈x∷Γ) refl | no τ₂≠τ₁ =
  ⊥-elim (contr x∈x∷Γ)

  where
  contr : (x , τ₂) ∉ (x , τ₁) ∷ Γ
  contr = ∉-∷ _ _ (λ xτ₂≡xτ₁ → τ₂≠τ₁ (×-inj-r xτ₂≡xτ₁)) (∉-dom x∉)
------------------------------------------------------------------------------------

wf-cons : ∀ {Γ x τ} -> Wf-Ctxt ((x , τ) ∷ Γ) -> Wf-Ctxt Γ
wf-cons (cons x∉ wf-Γ) = wf-Γ
------------------------------------------------------------------------------------

⊢-imp-wfΓ : ∀ {Γ m τ} -> Γ ⊢ m  ∶ τ -> Wf-Ctxt Γ
⊢-imp-wfΓ (var wf-Γ _) = wf-Γ
⊢-imp-wfΓ (app Γ⊢m:τ Γ⊢m:τ₁) = ⊢-imp-wfΓ Γ⊢m:τ₁
⊢-imp-wfΓ (abs {Γ} {τ₁} {τ₂} L cf) = wf-cons ih
  where
  x = ∃fresh L

  x∉ : x ∉ L
  x∉ = ∃fresh-spec L

  ih : Wf-Ctxt ((x , τ₁) ∷ Γ)
  ih = ⊢-imp-wfΓ (cf x∉)

⊢-imp-wfΓ (Y wf-Γ) = wf-Γ
------------------------------------------------------------------------------------

weakening : ∀ {Γ Γ' m τ} -> Γ ⊆ Γ' -> Wf-Ctxt Γ' -> Γ ⊢ m ∶ τ -> Γ' ⊢ m ∶ τ
weakening Γ⊆Γ' wf-Γ' (var _ xτ∈Γ) = var wf-Γ' (Γ⊆Γ' xτ∈Γ)
weakening Γ⊆Γ' wf-Γ' (app Γ⊢m∶τ Γ⊢n∶τ₁) =
  app (weakening Γ⊆Γ' wf-Γ' Γ⊢m∶τ) (weakening Γ⊆Γ' wf-Γ' Γ⊢n∶τ₁)
weakening {Γ} {Γ'} Γ⊆Γ' wf-Γ' (abs {_} {τ₁} {τ₂} L {m} cf) =
  abs (L ++ dom Γ')
    (λ {x} x∉L++Γ' → weakening {(x , τ₁) ∷ Γ} {(x , τ₁) ∷ Γ'} {m ^' x} {τ₂}
      (cons-⊆ Γ⊆Γ') (cons (∉-cons-r L _ x∉L++Γ') wf-Γ') (cf (∉-cons-l _ _ x∉L++Γ')))
weakening Γ⊆Γ' wf-Γ' (Y _) = Y wf-Γ'
------------------------------------------------------------------------------------

wf-Γ-exchange : ∀ {Γ x y τ₁ τ₂} -> Wf-Ctxt ((x , τ₁) ∷ (y , τ₂) ∷ Γ) ->
  Wf-Ctxt ((y , τ₂) ∷ (x , τ₁) ∷ Γ)
wf-Γ-exchange (cons x∉y∷Γ (cons y∉Γ wf∷Γ)) =
  cons
    (∉-∷ _ _ (λ y≡x → fv-x≠y _ _ x∉y∷Γ (≡-sym y≡x)) y∉Γ)
    (cons (∉-∷-elim _ x∉y∷Γ) wf∷Γ)
------------------------------------------------------------------------------------

exchange : ∀ {Γ m x y τ₁ τ₂ δ} -> ((x , τ₁) ∷ (y , τ₂) ∷ Γ) ⊢ m ∶ δ ->
  ((y , τ₂) ∷ (x , τ₁) ∷ Γ) ⊢ m ∶ δ
exchange {Γ} {m} {x} {y} {τ₁} {τ₂} x∷y∷Γ⊢m∶δ =
  weakening {(x , τ₁) ∷ (y , τ₂) ∷ Γ} {(y , τ₂) ∷ (x , τ₁) ∷ Γ}
    sub (wf-Γ-exchange (⊢-imp-wfΓ x∷y∷Γ⊢m∶δ)) x∷y∷Γ⊢m∶δ

    where
    sub : (x , τ₁) ∷ (y , τ₂) ∷ Γ ⊆ (y , τ₂) ∷ (x , τ₁) ∷ Γ
    sub (here px) = there (here px)
    sub (there (here px)) = here px
    sub (there (there ∈)) = there (there ∈)
------------------------------------------------------------------------------------

subst-⊢ : ∀ {Γ m n τ₁ τ₂ x} -> Term m -> ((x , τ₁) ∷ Γ) ⊢ m ∶ τ₂ -> Γ ⊢ n ∶ τ₁ ->
  Γ ⊢ (m [ x ::= n ]) ∶ τ₂
subst-⊢ {x = x} var (var {_} {y} wf-x∷Γ xτ∈Γ) Γ⊢n∶τ₁ with x ≟ y
subst-⊢ var (var wf-x∷Γ xτ∈Γ) Γ⊢n∶τ₁ | yes refl rewrite
  var-⊢-≡ (var wf-x∷Γ xτ∈Γ) refl = Γ⊢n∶τ₁
subst-⊢ {Γ} {.x} {_} {τ₁} {τ₂} {x} var (var {.x} {y} (cons x∉ wf-Γ) yτ₂∈Γ) Γ⊢n∶τ₁ | no x≠y =
  var wf-Γ (∈-∷-elim _ _ (λ xτ₂≡yτ₁ → x≠y (×-inj-l xτ₂≡yτ₁)) yτ₂∈Γ)
subst-⊢ {Γ} {_} {n} {τ₁} {_} {x} (lam L cf) (abs {_} {τ₁'} {τ₂} L' {m} cf') Γ⊢n∶τ₁ =
  abs (x ∷ (L ++ L' ++ dom Γ)) body

  where
  body : ∀ {x' : ℕ} -> x' ∉ x ∷ L ++ L' ++ dom Γ ->
    ((x' , τ₁') ∷ Γ) ⊢ (m [ x ::= n ]) ^' x' ∶ τ₂
  body {x'} x'∉ rewrite
    subst-open-var x' x n m (fv-x≠y _ _ x'∉) (⊢-term Γ⊢n∶τ₁) =
      subst-⊢ {(x' , τ₁') ∷ Γ} {m ^' x'} {n} {τ₁} {τ₂}
        (cf (∉-∷-elim _ (∉-cons-l _ _ x'∉)))
          (exchange (cf' (∉-cons-l _ _ (∉-cons-r L _ (∉-∷-elim _ x'∉)))))
          (weakening there
            (cons
              (∉-cons-r L' _ (∉-cons-r L _ (∉-∷-elim _ x'∉)))
              (⊢-imp-wfΓ Γ⊢n∶τ₁)) Γ⊢n∶τ₁)

subst-⊢ (app term-m term-m₁) (app x∷Γ⊢m∶τ₂ x∷Γ⊢m∶τ₃) Γ⊢n∶τ₁ =
  app (subst-⊢ term-m x∷Γ⊢m∶τ₂ Γ⊢n∶τ₁) (subst-⊢ term-m₁ x∷Γ⊢m∶τ₃ Γ⊢n∶τ₁)
subst-⊢ Y (Y (cons x∉ wf-Γ)) Γ⊢n∶τ₁ = Y wf-Γ
------------------------------------------------------------------------------------

^-⊢ : ∀ {Γ L m n τ₁ τ₂}  ->
  ( cf : ∀ {x} -> (x∉L : x ∉ L) -> ((x , τ₁) ∷ Γ) ⊢ m ^' x ∶ τ₂ ) ->
  Γ ⊢ n ∶ τ₁ -> Γ ⊢ m ^ n ∶ τ₂
^-⊢ {Γ} {L} {m} {n} {τ₁} {τ₂} cf Γ⊢n∶τ₁ = body
  where
  x = ∃fresh (L ++ FV m)

  x∉ : x ∉ (L ++ FV m)
  x∉ = ∃fresh-spec (L ++ FV m)

  body : Γ ⊢ m ^ n ∶ τ₂
  body rewrite
    subst-intro x n m (∉-cons-r L _ x∉) (⊢-term Γ⊢n∶τ₁) =
    subst-⊢ (⊢-term (cf (∉-cons-l _ _ x∉))) (cf (∉-cons-l _ _ x∉)) Γ⊢n∶τ₁
------------------------------------------------------------------------------------

->β-⊢ : ∀ {Γ m m' τ} -> Γ ⊢ m ∶ τ -> m ->β m' -> Γ ⊢ m' ∶ τ
->β-⊢ (app Γ⊢m∶τ Γ⊢n∶τ₁) (redL x m->βm') = app (->β-⊢ Γ⊢m∶τ m->βm') Γ⊢n∶τ₁
->β-⊢ (app Γ⊢m∶τ Γ⊢m∶τ₁) (redR x m->βm') = app Γ⊢m∶τ (->β-⊢ Γ⊢m∶τ₁ m->βm')
->β-⊢ (abs L cf) (abs L₁ cf₁) =
  abs (L ++ L₁) (λ {x} x∉L → ->β-⊢ (cf (∉-cons-l _ _ x∉L)) (cf₁ (∉-cons-r L _ x∉L)))
->β-⊢ (app {Γ} {_} {n} (abs L {m} cf) Γ⊢n∶τ₁) (beta term-lam-x term-cf) =
  ^-⊢ {m = m} cf Γ⊢n∶τ₁
->β-⊢ (app (Y wf-Γ) Γ⊢m∶τ₁) (Y term-m) = app Γ⊢m∶τ₁ (app (Y wf-Γ) Γ⊢m∶τ₁)
