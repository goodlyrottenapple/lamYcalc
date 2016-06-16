module ITyping where

open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.List.Any as Any
open Any.Membership-≡
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core


open import Core
open import Core-Lemmas
open import Typing
open import Reduction



data IType : Set
data ITypeₛ : Set


data ITypeₛ where
  o : ITypeₛ
  _~>_ : (s : IType) -> (t : ITypeₛ) -> ITypeₛ

data IType where
   ∩ : List ITypeₛ -> IType

ω = ∩ []

∩' : ITypeₛ -> IType
∩' x = ∩ (x ∷ [])

~>-inj-l : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂} -> (τ₁₁ ~> τ₁₂) ≡ (τ₂₁ ~> τ₂₂) -> τ₁₁ ≡ τ₂₁
~>-inj-l refl = refl

~>-inj-r : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂} -> (τ₁₁ ~> τ₁₂) ≡ (τ₂₁ ~> τ₂₂) -> τ₁₂ ≡ τ₂₂
~>-inj-r refl = refl

∩-inj-cons : ∀ {x y τᵢ τⱼ} -> ∩ (x ∷ τᵢ) ≡ ∩ (y ∷ τⱼ) -> ∩ τᵢ ≡ ∩ τⱼ
∩-inj-cons refl = refl

∩-inj : ∀ {x y τᵢ τⱼ} -> ∩ (x ∷ τᵢ) ≡ ∩ (y ∷ τⱼ) -> x ≡ y
∩-inj refl = refl


_≟TI_ : Decidable {A = IType} _≡_
_≟TIₛ_ : Decidable {A = ITypeₛ} _≡_

∩ [] ≟TI ∩ [] = yes refl
∩ [] ≟TI ∩ (x ∷ τⱼ) = no (λ ())
∩ (x ∷ τᵢ) ≟TI ∩ [] = no (λ ())
∩ (x ∷ τᵢ) ≟TI ∩ (y ∷ τⱼ) with x ≟TIₛ y | (∩ τᵢ) ≟TI (∩ τⱼ)
∩ (x ∷ τᵢ) ≟TI ∩ (.x ∷ .τᵢ) | yes refl | yes refl = yes refl
∩ (x ∷ τᵢ) ≟TI ∩ (.x ∷ τⱼ) | yes refl | no τᵢ≠τⱼ = no (λ ∩x∷τᵢ≡∩x∷τⱼ → τᵢ≠τⱼ (∩-inj-cons ∩x∷τᵢ≡∩x∷τⱼ))
∩ (x ∷ τᵢ) ≟TI ∩ (y ∷ τⱼ) | no x≠y | _ = no (λ ∩x∷τᵢ≡∩y∷τⱼ → x≠y (∩-inj ∩x∷τᵢ≡∩y∷τⱼ))

o ≟TIₛ o = yes refl
o ≟TIₛ (_ ~> _) = no (λ ())
(_ ~> _) ≟TIₛ o = no (λ ())
(τ₁₁ ~> τ₁₂) ≟TIₛ (τ₂₁ ~> τ₂₂) with τ₁₁ ≟TI τ₂₁ | τ₁₂ ≟TIₛ τ₂₂
(τ₁₁ ~> τ₁₂) ≟TIₛ (.τ₁₁ ~> .τ₁₂) | yes refl | yes refl = yes refl
(τ₁₁ ~> τ₁₂) ≟TIₛ (.τ₁₁ ~> τ₂₂) | yes refl | no τ₁₂≠τ₂₂ = no (λ eq → τ₁₂≠τ₂₂ (~>-inj-r eq))
(τ₁₁ ~> τ₁₂) ≟TIₛ (τ₂₁ ~> τ₂₂) | no τ₁₁≠τ₂₁ | _ = no (λ eq → τ₁₁≠τ₂₁ (~>-inj-l eq))


ICtxt = List (Atom × IType)


data Wf-ICtxt : ICtxt -> Set where
  nil : Wf-ICtxt []
  cons : ∀ {Γ x τ} -> (x∉ : x ∉ dom Γ) -> Wf-ICtxt Γ ->
    Wf-ICtxt ((x , τ) ∷ Γ)


data _∷'_ : IType -> Type -> Set
data _∷'ₛ_ : ITypeₛ -> Type -> Set

data _∷'ₛ_ where
  base : o ∷'ₛ σ
  arr : ∀ {δ τ A B} -> δ ∷' A -> τ ∷'ₛ B -> (δ ~> τ) ∷'ₛ (A ⟶ B)

data _∷'_ where
  int : ∀{τᵢ A} -> (c : ∀ {τ} -> (τ∈τᵢ : τ ∈ τᵢ) -> τ ∷'ₛ A) -> ∩ τᵢ ∷' A


data _⊩_∶_ : ICtxt -> PTerm -> ITypeₛ -> Set where
  var : ∀ {Γ x τ} {τᵢ : List ITypeₛ} -> (wf-Γ : Wf-ICtxt Γ) -> (τᵢ∈Γ : (x , (∩ τᵢ)) ∈ Γ) -> (τ∈τᵢ : τ ∈ τᵢ) ->
    Γ ⊩ fv x ∶ τ
  app : ∀ {Γ s t τᵢ τ} -> Γ ⊩ s ∶ ((∩ τᵢ) ~> τ) -> Term t -> (Γ⊩t∶τᵢ : ∀ {τ'} -> (τ'∈τᵢ : τ' ∈ τᵢ) -> Γ ⊩ t ∶ τ') ->
    Γ ⊩ (app s t) ∶ τ
  abs : ∀ {Γ τᵢ τ} (L : FVars) -> ∀ {t} ->
    ( cf : ∀ {x} -> (x∉L : x ∉ L) -> ((x , ∩ τᵢ) ∷ Γ) ⊩ t ^' x ∶ τ ) -> Γ ⊩ lam t ∶ (∩ τᵢ ~> τ)
  Y : ∀ {Γ A τᵢ τ} -> Wf-ICtxt Γ -> (τ∈τᵢ : τ ∈ τᵢ) -> (τᵢ∷ : ∀ {τ} -> τ ∈ τᵢ -> τ ∷'ₛ A) ->
    Γ ⊩ Y A ∶ (∩ (Data.List.map (λ τₖ -> (∩ τᵢ ~> τₖ)) τᵢ) ~> τ)

⊩-term : ∀ {Γ m τ} -> Γ ⊩ m ∶ τ -> Term m
⊩-term (var _ _ _) = var
⊩-term (app Γ⊩m∶τ trm-t c) = app (⊩-term Γ⊩m∶τ) trm-t
⊩-term (abs L cf) = lam L (λ {x} x∉L → ⊩-term (cf x∉L))
⊩-term (Y x τ∈τᵢ x₁) = Y

_⊩_∶∩_ : ICtxt -> PTerm -> List ITypeₛ -> Set
Γ ⊩ m ∶∩ τᵢ = ∀ {τ} -> τ ∈ τᵢ -> Γ ⊩ m ∶ τ

_⊩_∶∩_~>∩_ : ICtxt -> PTerm -> List ITypeₛ -> List ITypeₛ -> Set
Γ ⊩ m ∶∩ τᵢ ~>∩ τⱼ = ∀ {τ} -> τ ∈ τⱼ -> Γ ⊩ m ∶ (∩ τᵢ ~> τ)

_⊩_∶∩_~>∩_~>∩_ : ICtxt -> PTerm -> List ITypeₛ -> List ITypeₛ -> List ITypeₛ -> Set
Γ ⊩ m ∶∩ τᵢ ~>∩ τⱼ ~>∩ τₖ = ∀ {τ} -> τ ∈ τₖ -> Γ ⊩ m ∶ (∩ (Data.List.map (λ τₘ -> (∩ τᵢ ~> τₘ)) τⱼ) ~> τ)


data _≤ₛ_ : ITypeₛ -> ITypeₛ -> Set
data _≤∩_ : IType -> IType -> Set

data _≤ₛ_ where
  base : o ≤ₛ o
  arr : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂} -> τ₁₂ ≤ₛ τ₂₂ -> τ₂₁ ≤∩ τ₁₁ -> (τ₁₁ ~> τ₁₂) ≤ₛ (τ₂₁ ~> τ₂₂)
  transₛ : ∀ {τ₁ τ₂ τ₃} -> τ₁ ≤ₛ τ₂ -> τ₂ ≤ₛ τ₃ -> τ₁ ≤ₛ τ₃

data _≤∩_ where
  ∈-∩ : ∀ {τ τᵢ} -> τ ∈ τᵢ -> ∩ τᵢ ≤∩ ∩' τ
  introₛ : ∀ {τ τᵢ} -> (∀ {τ'} -> (τ'∈τᵢ : τ' ∈ τᵢ) -> τ ≤ₛ τ') -> ∩' τ ≤∩ ∩ τᵢ
  intro : ∀ {τⱼ τᵢ} -> (∀ {τ'} -> (τ'∈τᵢ : τ' ∈ τᵢ) -> ∩ τⱼ ≤∩ ∩' τ') -> ∩ τⱼ ≤∩ ∩ τᵢ
  trans-∩ : ∀ {τ₁ τ₂ τ₃} -> τ₁ ≤∩ τ₂ -> τ₂ ≤∩ τ₃ -> τ₁ ≤∩ τ₃

≤ω : ∀ {τ} -> τ ≤∩ ω
≤ω {∩ τᵢ} = intro (λ {τ'} → λ ())

≤∩-refl : ∀ {τ} -> τ ≤∩ τ
≤∩-refl {∩ []} = ≤ω
≤∩-refl {∩ (x ∷ τᵢ)} = intro (λ {τ'} → ∈-∩)

≤ₛ-refl : ∀ {τ} -> τ ≤ₛ τ
≤ₛ-refl {o} = base
≤ₛ-refl {_ ~> _} = arr ≤ₛ-refl ≤∩-refl

wfI-cons : ∀ {Γ x τ} -> Wf-ICtxt ((x , τ) ∷ Γ) -> Wf-ICtxt Γ
wfI-cons (cons x∉ wf-Γ) = wf-Γ


⊩-imp-wfΓ : ∀ {Γ m τ} -> Γ ⊩ m  ∶ τ -> Wf-ICtxt Γ
⊩-imp-wfΓ (var x₁ x₂ x₃) = x₁
⊩-imp-wfΓ (app Γ⊢m:τ trm-t c) = ⊩-imp-wfΓ Γ⊢m:τ
⊩-imp-wfΓ (abs L cf) = wfI-cons (⊩-imp-wfΓ (cf x∉))
  where
  x = ∃fresh L

  x∉ : x ∉ L
  x∉ = ∃fresh-spec L

⊩-imp-wfΓ (Y x τ∈τᵢ x₁) = x


var-⊩-∈ : ∀ {x y τᵢ τ Γ} -> ((x , ∩ τᵢ) ∷ Γ) ⊩ fv y ∶ τ -> x ≡ y -> τ ∈ τᵢ
var-⊩-∈ {x} {_} {τᵢ} {τ} (var {x = .x} {τᵢ = τⱼ} (cons x∉ wf-Γ) ∩τⱼ∈x∷Γ τ∈τⱼ) refl with (∩ τⱼ) ≟TI (∩ τᵢ)
var-⊩-∈ (var (cons x∉ wf-Γ) ∩τⱼ∈x∷Γ τ∈τⱼ) refl | yes refl = τ∈τⱼ
var-⊩-∈ (var (cons x∉ wf-Γ) ∩τⱼ∈x∷Γ τ∈τⱼ) refl | no ∩τⱼ≠∩τᵢ = ⊥-elim (∉-∷ _ _ (λ x → ∩τⱼ≠∩τᵢ (×-inj-r x)) (∉-dom x∉) ∩τⱼ∈x∷Γ)


-- substitution lemma.

weakening-⊩ : ∀ {Γ Γ' m τ} -> Γ ⊆ Γ' -> Wf-ICtxt Γ' -> Γ ⊩ m ∶ τ -> Γ' ⊩ m ∶ τ
weakening-⊩ Γ⊆Γ' wf-Γ' (var wf-Γ ∩τᵢ∈Γ τ∈τᵢ) = var wf-Γ' (Γ⊆Γ' ∩τᵢ∈Γ) τ∈τᵢ
weakening-⊩ Γ⊆Γ' wf-Γ' (app Γ⊩m∶τ x c) = app (weakening-⊩ Γ⊆Γ' wf-Γ' Γ⊩m∶τ) x
  (λ {τ'} τ'∈τᵢ → weakening-⊩ Γ⊆Γ' wf-Γ' (c τ'∈τᵢ))
weakening-⊩ {Γ} {Γ'} Γ⊆Γ' wf-Γ' (abs {_} {τᵢ} {τ} L {m} cf) =
  abs (L ++ dom Γ') (λ {x} x∉L++Γ' →
    weakening-⊩ {(x , τᵢ) ∷ Γ} {(x , τᵢ) ∷ Γ'} {m ^' x} {τ}
      (cons-⊆ Γ⊆Γ')
      (cons (∉-cons-r L _ x∉L++Γ') wf-Γ')
      (cf (∉-cons-l _ _ x∉L++Γ')))
weakening-⊩ Γ⊆Γ' wf-Γ' (Y x τ∈τᵢ x₁) = Y wf-Γ' τ∈τᵢ x₁


wfI-Γ-exchange : ∀ {Γ x y τ₁ τ₂} -> Wf-ICtxt ((x , τ₁) ∷ (y , τ₂) ∷ Γ) -> Wf-ICtxt ((y , τ₂) ∷ (x , τ₁) ∷ Γ)
wfI-Γ-exchange (cons x∉y∷Γ (cons y∉Γ wf∷Γ)) =
  cons (∉-∷ _ _ (λ y≡x → fv-x≠y _ _ x∉y∷Γ (≡-sym y≡x)) y∉Γ) (cons (∉-∷-elim _ x∉y∷Γ) wf∷Γ)


exchange-⊩ : ∀ {Γ m x y τ₁ τ₂ δ} -> ((x , τ₁) ∷ (y , τ₂) ∷ Γ) ⊩ m ∶ δ -> ((y , τ₂) ∷ (x , τ₁) ∷ Γ) ⊩ m ∶ δ
exchange-⊩ {Γ} {m} {x} {y} {τ₁} {τ₂} x∷y∷Γ⊢m∶δ =
  weakening-⊩ {(x , τ₁) ∷ (y , τ₂) ∷ Γ} {(y , τ₂) ∷ (x , τ₁) ∷ Γ}
    sub (wfI-Γ-exchange (⊩-imp-wfΓ x∷y∷Γ⊢m∶δ)) x∷y∷Γ⊢m∶δ

    where
    sub : (x , τ₁) ∷ (y , τ₂) ∷ Γ ⊆ (y , τ₂) ∷ (x , τ₁) ∷ Γ
    sub (here px) = there (here px)
    sub (there (here px)) = here px
    sub (there (there ∈)) = there (there ∈)


subst-⊩ : ∀ {Γ m n τᵢ τ₂ x} -> Term m -> Term n -> ((x , ∩ τᵢ) ∷ Γ) ⊩ m ∶ τ₂ -> (∀ {τ} -> τ ∈ τᵢ -> Γ ⊩ n ∶ τ) ->
  Γ ⊩ (m [ x ::= n ]) ∶ τ₂
subst-⊩ {x = x} var trm-n (var {x = y} wf-Γ ∩τᵢ∈Γ τ∈τᵢ) Γ⊩n∶τᵢ with x ≟ y
subst-⊩ var trm-n (var wf-Γ ∩τᵢ∈Γ τ∈τᵢ) Γ⊩n∶τᵢ | yes refl =
  Γ⊩n∶τᵢ (var-⊩-∈ (var wf-Γ ∩τᵢ∈Γ τ∈τᵢ) refl)
subst-⊩ {Γ} {x = x} var trm-n (var {x = y} wf-Γ ∩τᵢ∈Γ τ∈τᵢ) Γ⊩n∶τᵢ | no x≠y =
  var {Γ} {y} (wfI-cons wf-Γ) (∈-∷-elim _ _ (λ x∩τᵢ≡y∩τⱼ → x≠y (×-inj-l x∩τᵢ≡y∩τⱼ)) ∩τᵢ∈Γ) τ∈τᵢ
subst-⊩ {Γ} {_} {n} {τᵢ} {_} {x} (lam L cf) trm-n (abs {_} {τᵢ'} {τ₂} L' {m} cf') Γ⊩n∶τᵢ = abs (x ∷ L ++ L' ++ dom Γ) body
  where
  body : ∀ {x' : ℕ} → x' ∉ x ∷ L ++ L' ++ dom Γ → ((x' , τᵢ') ∷ Γ) ⊩ (m [ x ::= n ]) ^' x' ∶ τ₂
  body {x'} x'∉ rewrite
    subst-open-var x' x n m (fv-x≠y _ _ x'∉) trm-n =
      subst-⊩ {(x' , τᵢ') ∷ Γ} {m ^' x'} {n} {τᵢ} {τ₂}
        (cf (∉-∷-elim _ (∉-cons-l _ _ x'∉)))
        trm-n
        (exchange-⊩ (cf' (∉-cons-l _ _ (∉-cons-r L _ (∉-∷-elim _ x'∉)))))
        (λ τ∈τᵢ → weakening-⊩ there (cons (∉-cons-r L' _ (∉-cons-r L _ (∉-∷-elim _ x'∉))) (⊩-imp-wfΓ (Γ⊩n∶τᵢ τ∈τᵢ))) (Γ⊩n∶τᵢ τ∈τᵢ))

subst-⊩ (app trm-m trm-m₁) trm-n (app x∷Γ⊩m∶τ₂ trm-t c) Γ⊩n∶τᵢ =
  app (subst-⊩ trm-m trm-n x∷Γ⊩m∶τ₂ Γ⊩n∶τᵢ) (subst-Term trm-t trm-n) (λ {τ'} τ'∈τᵢ → subst-⊩ trm-m₁ trm-n (c τ'∈τᵢ) Γ⊩n∶τᵢ)
subst-⊩ Y trm-n (Y (cons x∉ wf-Γ) τ∈τᵢ x₂) Γ⊩n∶τᵢ = Y wf-Γ τ∈τᵢ x₂


-- subject reduction
^-⊩ : ∀ {Γ L m n τᵢ τ₂} -> Term n -> ( cf : ∀ {x} -> (x∉L : x ∉ L) -> ((x , ∩ τᵢ) ∷ Γ) ⊩ m ^' x ∶ τ₂ ) ->
  (∀ {τ} -> τ ∈ τᵢ -> Γ ⊩ n ∶ τ) -> Γ ⊩ m ^ n ∶ τ₂
^-⊩ {Γ} {L} {m} {n} {τᵢ} {τ} trm-n cf Γ⊩n∶τᵢ = body
  where
  x = ∃fresh (L ++ FV m)

  x∉ : x ∉ (L ++ FV m)
  x∉ = ∃fresh-spec (L ++ FV m)

  body : Γ ⊩ m ^ n ∶ τ
  body rewrite
    subst-intro x n m (∉-cons-r L _ x∉) trm-n =
    subst-⊩ (⊩-term (cf (∉-cons-l _ _ x∉))) trm-n (cf (∉-cons-l _ _ x∉)) Γ⊩n∶τᵢ


->β⊩ : ∀ {Γ m m' τ} -> Γ ⊩ m ∶ τ -> m ->β m' -> Γ ⊩ m' ∶ τ
->β⊩ (app Γ⊩m∶τ x c) (redL x₁ m->βm') = app (->β⊩ Γ⊩m∶τ m->βm') x₁ c
->β⊩ (app Γ⊩m∶τ trm-t c) (redR x₁ m->βm') = app Γ⊩m∶τ (->β-Term-r m->βm') (λ τ'∈τᵢ → ->β⊩ (c τ'∈τᵢ) m->βm')
->β⊩ (abs L cf) (abs L₁ cf₁) = abs (L ++ L₁) (λ {x} x∉L → ->β⊩ (cf (∉-cons-l _ _ x∉L)) (cf₁ (∉-cons-r L _ x∉L)))
->β⊩ (app (abs L {m} cf) x Γ⊢n∶τᵢ) (beta x₁ trm-n) = ^-⊩ {m = m} trm-n cf Γ⊢n∶τᵢ
->β⊩ (app (Y {τ = τ} wf-Γ τ∈τᵢ τ∷'ₛσ) _ Γ⊩m∶τᵢ) (Y trm-m) =
  app
    (Γ⊩m∶τᵢ (map-∈ (τ , τ∈τᵢ , refl)))
    (app Y trm-m)
    (λ τ'∈τᵢ → app (Y wf-Γ τ'∈τᵢ (λ τ∈τᵢ → τ∷'ₛσ τ∈τᵢ)) trm-m (λ τ'∈τᵢ₁ → Γ⊩m∶τᵢ τ'∈τᵢ₁))

-- subject expansion
aaab : ∀ {τ Γ A m} -> Γ ⊩ app (Y A) m ∶ τ -> ∃(λ τᵢ -> τ ∈ τᵢ -> Γ ⊩ Y A ∶∩ τᵢ ~>∩ τᵢ ~>∩ τᵢ × Γ ⊩ m ∶∩ τᵢ ~>∩ τᵢ)
aaab (app (Y {τᵢ = τᵢ} x τ∈τᵢ τᵢ∷) x₁ Γ⊩t∶τᵢ) = τᵢ , (λ τ∈τᵢ → (λ {τ} z → Y x z τᵢ∷) , (λ {τ} x₂ → Γ⊩t∶τᵢ (map-∈ (τ , x₂ , refl))))

aux : ∀ {τᵢ Γ A m} -> (Γ⊩Ym∶τᵢ : Γ ⊩ app (Y A) m ∶∩ τᵢ) ->
  ∃( λ τⱼ -> ( Γ ⊩ Y A ∶∩ τⱼ ~>∩ τⱼ ~>∩ τⱼ) × ( Γ ⊩ m ∶∩ τⱼ ~>∩ τⱼ ) )
aux {τᵢ} Γ⊩Ym∶τᵢ = τᵢ , (λ τ∈τᵢ → {!   !}) , {!   !}


-- ⊩^-1 : ∀ {Γ L m n τᵢ τ₂ x} -> Γ ⊩ m ^ n ∶ τ₂ -> (x∉L : x ∉ L) -> ((x , ∩ τᵢ) ∷ Γ) ⊩ m ^' x ∶ τ₂
-- ⊩^-1 Γ⊩m^n∶τ₂ x∉L = {!   !}


-- ⊩^-2 : ∀ {Γ m n τᵢ τ₂ τ} -> Γ ⊩ m ^ n ∶ τ₂ -> τ ∈ τᵢ -> Γ ⊩ n ∶ τ
-- ⊩^-2 = {!   !}

⊩->β : ∀ {Γ m m' τ} -> Γ ⊩ m' ∶ τ -> m ->β m' -> Γ ⊩ m ∶ τ
⊩->β Γ⊩m'∶τ (redL {n} {m} {m'} trm-n m->βm') = ⊩->β-redL Γ⊩m'∶τ m->βm'
  where
  ⊩->β-redL : ∀ {Γ m m' n τ} -> Γ ⊩ app m' n ∶ τ -> m ->β m' -> Γ ⊩ app m n ∶ τ
  ⊩->β-redL (app Γ⊩m'n∶τ x Γ⊩t∶τᵢ) (redL trm-n m->βm') = app (⊩->β-redL Γ⊩m'n∶τ m->βm') x Γ⊩t∶τᵢ
  ⊩->β-redL (app Γ⊩mn'∶τ x Γ⊩n∶τᵢ) (redR trm-m n->βn') = app (⊩->β Γ⊩mn'∶τ (redR trm-m n->βn')) x Γ⊩n∶τᵢ
  ⊩->β-redL (app Γ⊩m'n∶τ x Γ⊩t∶τᵢ) (abs L x₁) = app (⊩->β Γ⊩m'n∶τ (abs L x₁)) x Γ⊩t∶τᵢ
  ⊩->β-redL (app Γ⊩m'n∶τ x Γ⊩t∶τᵢ) (beta x₁ x₂) = app (⊩->β Γ⊩m'n∶τ (beta x₁ x₂)) x Γ⊩t∶τᵢ
  ⊩->β-redL (app Γ⊩m'n∶τ x Γ⊩t∶τᵢ) (Y x₁) = app (⊩->β Γ⊩m'n∶τ (Y x₁)) x Γ⊩t∶τᵢ

⊩->β (app Γ⊩m'∶τ x Γ⊩t∶τᵢ) (redR trm-m n->βn') =
  app Γ⊩m'∶τ (->β-Term-l n->βn') (λ τ'∈τᵢ → ⊩->β (Γ⊩t∶τᵢ τ'∈τᵢ) n->βn')
⊩->β (abs L cf) (abs L₁ x) = abs (L ++ L₁) (λ x∉L → ⊩->β (cf (∉-cons-l _ _ x∉L)) (x (∉-cons-r L _ x∉L)))
⊩->β Γ⊩m'∶τ (beta {m} {n} (lam L cf) trm-n) = {!   !}
  -- app {τᵢ = []} (abs L (λ x∉L → ⊩^-1 {m = m} Γ⊩m'∶τ x∉L)) trm-n (λ τ'∈τᵢ → ⊩^-2 {m = m} Γ⊩m'∶τ τ'∈τᵢ)
⊩->β (app {Γ} {m} {τᵢ = τᵢ} {τ} Γ⊩m∶∩τᵢ~>τ (app trm-Y _) Γ⊩Ym∶τᵢ) (Y {_} {A} trm-m) =
  app {τᵢ = Data.List.map (λ τₖ -> (∩ τᵢ ~> τₖ)) τᵢ} (Y {!   !} {!   !} {!   !}) trm-m {!   !}
