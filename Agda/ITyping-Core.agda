module ITyping-Core where

open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.List.Properties
open import Data.List.Any as LAny
open LAny.Membership-≡
open import Relation.Nullary
open import Relation.Binary.Core

open import Core
open import Core-Lemmas
open import Typing
open import Typed-Core
open import Reduction using (_↝_)

data IType : Set where
  o : IType
  _~>_ : List IType -> List IType -> IType


ω : List IType
ω = []

∩' : IType -> List IType
∩' x = (x ∷ [])

_∩_ : IType -> IType -> List IType
A ∩ B = A ∷ B ∷ []


~>-inj-l : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂} -> (τ₁₁ ~> τ₁₂) ≡ (τ₂₁ ~> τ₂₂) -> τ₁₁ ≡ τ₂₁
~>-inj-l refl = refl

~>-inj-r : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂} -> (τ₁₁ ~> τ₁₂) ≡ (τ₂₁ ~> τ₂₂) -> τ₁₂ ≡ τ₂₂
~>-inj-r refl = refl


_≟TI_ : Decidable {A = IType} _≡_
_≟TIₗ_ : Decidable {A = List IType} _≡_

o ≟TI o = yes refl
o ≟TI (_ ~> _) = no (λ ())
(_ ~> _) ≟TI o = no (λ ())
(τ₁₁ ~> τ₁₂) ≟TI (τ₂₁ ~> τ₂₂) with τ₁₁ ≟TIₗ τ₂₁ | τ₁₂ ≟TIₗ τ₂₂
(τ₁₁ ~> τ₁₂) ≟TI (.τ₁₁ ~> .τ₁₂) | yes refl | yes refl = yes refl
(τ₁₁ ~> τ₁₂) ≟TI (.τ₁₁ ~> τ₂₂) | yes refl | no τ₁₂≠τ₂₂ = no (λ eq → τ₁₂≠τ₂₂ (~>-inj-r eq))
(τ₁₁ ~> τ₁₂) ≟TI (τ₂₁ ~> τ₂₂) | no τ₁₁≠τ₂₁ | _ = no (λ eq → τ₁₁≠τ₂₁ (~>-inj-l eq))


[] ≟TIₗ [] = yes refl
[] ≟TIₗ (x ∷ τⱼ) = no (λ ())
(x ∷ τᵢ) ≟TIₗ [] = no (λ ())
(x ∷ τᵢ) ≟TIₗ (y ∷ τⱼ) with x ≟TI y | τᵢ ≟TIₗ τⱼ
(x ∷ τᵢ) ≟TIₗ (.x ∷ .τᵢ) | yes refl | yes refl = yes refl
(x ∷ τᵢ) ≟TIₗ (.x ∷ τⱼ) | yes refl | no τᵢ≠τⱼ = no (λ ∩x∷τᵢ≡∩x∷τⱼ → τᵢ≠τⱼ (proj₂ (∷-injective ∩x∷τᵢ≡∩x∷τⱼ)))
(x ∷ τᵢ) ≟TIₗ (y ∷ τⱼ) | no x≠y | _ = no (λ ∩x∷τᵢ≡∩y∷τⱼ → x≠y (proj₁ (∷-injective ∩x∷τᵢ≡∩y∷τⱼ)))



ICtxt = List (Atom × ((List IType) × Type))


data _∷'_ : IType -> Type -> Set
data _∷'ₗ_ : List IType -> Type -> Set

data _∷'_ where
  base : o ∷' σ
  arr : ∀ {δ τ A B} -> δ ∷'ₗ A -> τ ∷'ₗ B -> (δ ~> τ) ∷' (A ⟶ B)

data _∷'ₗ_ where
  nil : ∀ {A} -> ω ∷'ₗ A
  cons : ∀ {τᵢ τ A} -> τ ∷' A -> τᵢ ∷'ₗ A -> (τ ∷ τᵢ) ∷'ₗ A

data Wf-ICtxt : ICtxt -> Set where
  nil : Wf-ICtxt []
  cons : ∀ {A Γ x τ} ->
    (x∉ : x ∉ dom Γ) -> τ ∷'ₗ A -> Wf-ICtxt Γ ->
    --------------------------------------------
            Wf-ICtxt ((x , (τ , A)) ∷ Γ)



data _⊆[_]_ : IType -> Type -> IType -> Set
data _⊆ₗ[_]_ : List IType -> Type -> List IType -> Set

data _⊆[_]_ where
  base : o ⊆[ σ ] o
  arr : ∀ {A B τ₁₁ τ₁₂ τ₂₁ τ₂₂} ->
    τ₂₁ ⊆ₗ[ A ] τ₁₁ -> τ₁₂ ⊆ₗ[ B ] τ₂₂ ->
    -------------------------------------------------------------------------------------------
                            (τ₁₁ ~> τ₁₂) ⊆[ A ⟶ B ] (τ₂₁ ~> τ₂₂)


data _⊆ₗ[_]_ where
  nil : ∀ {A τ} ->
    τ ∷'ₗ A ->
    -----------
    ω ⊆ₗ[ A ] τ
  cons : ∀ {A τᵢ τ' τ'ᵢ} ->
    ∃(λ τ -> (τ ∈ τᵢ) × (τ' ⊆[ A ] τ)) -> τ'ᵢ ⊆ₗ[ A ] τᵢ ->
    -------------------------------------------------------
                    (τ' ∷ τ'ᵢ) ⊆ₗ[ A ] τᵢ
  ~>∩ : ∀ {A B τ τᵢ τᵢ' τₓ} ->
                ((τ ~> (τᵢ ++ τᵢ')) ∷ τₓ) ∷'ₗ (A ⟶ B) ->
    ---------------------------------------------------------
    ((τ ~> (τᵢ ++ τᵢ')) ∷ τₓ) ⊆ₗ[ A ⟶ B ] ((τ ~> τᵢ) ∷ (τ ~> τᵢ') ∷ τₓ)
  ⊆ₗ-trans : ∀ {A τᵢ τⱼ τₖ} ->
    τᵢ ⊆ₗ[ A ] τⱼ -> τⱼ ⊆ₗ[ A ] τₖ ->
    ---------------------------------
              τᵢ ⊆ₗ[ A ] τₖ


∷'ₗ-∈ : ∀ {A τ τᵢ} -> τ ∈ τᵢ -> τᵢ ∷'ₗ A -> τ ∷' A
∷'ₗ-∈ {τᵢ = []} () _
∷'ₗ-∈ {τ = τ} {τ' ∷ τᵢ} τ∈τ'τᵢ τ'τᵢ∷A with τ' ≟TI τ
∷'ₗ-∈ {A} {τ} {.τ ∷ τᵢ} τ∈τ'τᵢ (cons τ∷A τ'τᵢ∷A) | yes refl = τ∷A
∷'ₗ-∈ {A} {τ} {τ' ∷ τᵢ} τ∈τ'τᵢ (cons τ'∷A τ'τᵢ∷A) | no τ'≠τ = ∷'ₗ-∈ (∈-∷-elim τ τᵢ τ'≠τ τ∈τ'τᵢ) τ'τᵢ∷A

∷'ₗ-++-l : ∀ {A τᵢ τⱼ} -> (τᵢ ++ τⱼ) ∷'ₗ A -> τᵢ ∷'ₗ A
∷'ₗ-++-l {τᵢ = []} τᵢ++τⱼ∷A = nil
∷'ₗ-++-l {τᵢ = τ ∷ τᵢ} (cons x τᵢ++τⱼ∷A) = cons x (∷'ₗ-++-l τᵢ++τⱼ∷A)

∷'ₗ-++-r : ∀ {A τᵢ τⱼ} -> (τᵢ ++ τⱼ) ∷'ₗ A -> τⱼ ∷'ₗ A
∷'ₗ-++-r {τᵢ = []} τᵢ++τⱼ∷A = τᵢ++τⱼ∷A
∷'ₗ-++-r {A} {τᵢ = τ ∷ τᵢ} (cons x τᵢ++τⱼ∷A) = ∷'ₗ-++-r {A} {τᵢ} τᵢ++τⱼ∷A

++-∷'ₗ : ∀ {A τᵢ τⱼ} -> τᵢ ∷'ₗ A -> τⱼ ∷'ₗ A -> (τᵢ ++ τⱼ) ∷'ₗ A
++-∷'ₗ nil τⱼ∷' = τⱼ∷'
++-∷'ₗ (cons x τᵢ∷') τⱼ∷' = cons x (++-∷'ₗ τᵢ∷' τⱼ∷')

⊆-refl : ∀ {A τ} -> τ ∷' A -> τ ⊆[ A ] τ
⊆ₗ-refl : ∀ {A τ} -> τ ∷'ₗ A -> τ ⊆ₗ[ A ] τ
⊆ₗ-⊆ : ∀ {A τᵢ τⱼ} -> τᵢ ⊆ τⱼ -> τⱼ ∷'ₗ A -> τᵢ ⊆ₗ[ A ] τⱼ

⊆-refl {τ = o} base = base
⊆-refl {τ = τ ~> τ'} (arr τ∷ᵢA τ'∷ᵢB) =
  arr (⊆ₗ-refl τ∷ᵢA) (⊆ₗ-refl τ'∷ᵢB)

⊆ₗ-refl {τ = []} nil = nil nil
⊆ₗ-refl {A} {τ ∷ τᵢ} ττᵢ∷A = ⊆ₗ-⊆ (λ {x} z → z) ττᵢ∷A

⊆ₗ-⊆ {τᵢ = []} τᵢ⊆τⱼ τⱼ∷A = nil τⱼ∷A
⊆ₗ-⊆ {τᵢ = τ ∷ τᵢ} τᵢ⊆τⱼ τⱼ∷A =
  cons (τ , (τᵢ⊆τⱼ (here refl)) , ⊆-refl (∷'ₗ-∈ (τᵢ⊆τⱼ (here refl)) τⱼ∷A)) (⊆ₗ-⊆ (λ {x} z → τᵢ⊆τⱼ (there z)) τⱼ∷A)


⊆-∷'-l : ∀ {A τ τ'} -> τ ⊆[ A ] τ' -> τ ∷' A
⊆ₗ-∷'ₗ-l : ∀ {A τᵢ τⱼ} -> τᵢ ⊆ₗ[ A ] τⱼ -> τᵢ ∷'ₗ A
⊆-∷'-r : ∀ {A τ τ'} -> τ ⊆[ A ] τ' -> τ' ∷' A
⊆ₗ-∷'ₗ-r : ∀ {A τᵢ τⱼ} -> τᵢ ⊆ₗ[ A ] τⱼ -> τⱼ ∷'ₗ A

⊆-∷'-l base = base
⊆-∷'-l (arr x y) = arr (⊆ₗ-∷'ₗ-r x) (⊆ₗ-∷'ₗ-l y)

⊆ₗ-∷'ₗ-l (nil x) = nil
⊆ₗ-∷'ₗ-l (cons (_ , _ , τ'⊆τ) τᵢ⊆τⱼ) = cons (⊆-∷'-l τ'⊆τ) (⊆ₗ-∷'ₗ-l τᵢ⊆τⱼ)
⊆ₗ-∷'ₗ-l (~>∩ x) = x
⊆ₗ-∷'ₗ-l (⊆ₗ-trans τᵢ⊆τⱼ τⱼ⊆τₖ) = ⊆ₗ-∷'ₗ-l τᵢ⊆τⱼ

⊆-∷'-r base = base
⊆-∷'-r (arr x y) = arr (⊆ₗ-∷'ₗ-l x) (⊆ₗ-∷'ₗ-r y)

⊆ₗ-∷'ₗ-r {τᵢ = []} (nil τⱼ∷A) = τⱼ∷A
⊆ₗ-∷'ₗ-r {τᵢ = []} (⊆ₗ-trans τᵢ⊆τⱼ τᵢ⊆τⱼ₁) = ⊆ₗ-∷'ₗ-r τᵢ⊆τⱼ₁
⊆ₗ-∷'ₗ-r {τᵢ = τ ∷ τᵢ} (cons x τᵢ⊆τⱼ) = ⊆ₗ-∷'ₗ-r τᵢ⊆τⱼ
⊆ₗ-∷'ₗ-r {τᵢ = _ ∷ τₓ} (~>∩ {τᵢ = τᵢ} (cons (arr x x₁) τₓ∷')) =
  cons (arr x (∷'ₗ-++-l x₁)) (cons (arr x (∷'ₗ-++-r {τᵢ = τᵢ} x₁)) τₓ∷')
⊆ₗ-∷'ₗ-r {τᵢ = τ ∷ τᵢ} (⊆ₗ-trans τᵢ⊆τⱼ τᵢ⊆τⱼ₁) = ⊆ₗ-∷'ₗ-r τᵢ⊆τⱼ₁


-- ⊆ₗ-∈-∃ : ∀ {A τ τ₁ τ₂} -> τ₁ ⊆ₗ[ A ] τ₂ -> τ ∈ τ₁ -> ∃(λ τ' -> (τ' ∈ τ₂) × (τ ⊆[ A ] τ'))
-- ⊆ₗ-∈-∃ (cons ∃τ τ₁⊆τ₂) (here refl) = ∃τ
-- ⊆ₗ-∈-∃ (cons _ τ₁⊆τ₂) (there τ∈τ₁) = ⊆ₗ-∈-∃ τ₁⊆τ₂ τ∈τ₁
--
--
-- ⊆ₗ-ω-⊥ : ∀ {A τ τᵢ} -> (τ ∷ τᵢ) ⊆ₗ[ A ] ω -> ⊥
-- ⊆ₗ-ω-⊥ (cons (_ , () , _) _)
--

⊆-trans : ∀ {A τ₁ τ₂ τ₃} ->
  τ₁ ⊆[ A ] τ₂ -> τ₂ ⊆[ A ] τ₃ ->
  -------------------------------
            τ₁ ⊆[ A ] τ₃

-- ⊆ₗ-trans : ∀ {A τᵢ τⱼ τₖ} ->
--   τᵢ ⊆ₗ[ A ] τⱼ -> τⱼ ⊆ₗ[ A ] τₖ ->
--   ---------------------------------
--             τᵢ ⊆ₗ[ A ] τₖ
⊆-trans base base = base
⊆-trans (arr τ₂₁⊆τ₁₁ τ₁₂⊆τ₂₂) (arr τ₂₃⊆τ₂₁ τ₂₂⊆τ₂₄) =
  arr (⊆ₗ-trans τ₂₃⊆τ₂₁ τ₂₁⊆τ₁₁) (⊆ₗ-trans τ₁₂⊆τ₂₂ τ₂₂⊆τ₂₄)

-- ⊆ₗ-trans {τᵢ = []} τᵢ⊆τⱼ τⱼ⊆τₖ = nil (⊆ₗ-∷'ₗ-r τⱼ⊆τₖ)
-- ⊆ₗ-trans {τᵢ = τ' ∷ τᵢ} τᵢ⊆τⱼ (nil x) = ⊥-elim (⊆ₗ-ω-⊥ τᵢ⊆τⱼ)
-- ⊆ₗ-trans {τᵢ = τ ∷ τᵢ} {τⱼ} {τₖ} (cons (τ' , τ'∈τⱼ , τ⊆τ') τᵢ⊆τⱼ) τⱼ⊆τₖ =
--   cons (τ'' , (τ''∈τₖ , (⊆-trans τ⊆τ' τ'⊆τ''))) (⊆ₗ-trans τᵢ⊆τⱼ τⱼ⊆τₖ)
--     where
--     τ'' = proj₁ (⊆ₗ-∈-∃ τⱼ⊆τₖ τ'∈τⱼ)
--     τ''∈τₖ = proj₁ (proj₂ (⊆ₗ-∈-∃ τⱼ⊆τₖ τ'∈τⱼ))
--     τ'⊆τ'' = proj₂ (proj₂ (⊆ₗ-∈-∃ τⱼ⊆τₖ τ'∈τⱼ))

⊆->⊆ₗ : ∀ {A τ τ'} -> τ ⊆[ A ] τ' -> (∩' τ) ⊆ₗ[ A ] (∩' τ')
⊆->⊆ₗ {τ = τ} {τ'} τ⊆τ' = cons (τ' , (here refl , τ⊆τ')) (nil (cons (⊆-∷'-r τ⊆τ') nil))

-- _≈_ : (A B : List IType) -> Set
-- A ≈ B = A ⊆ B × B ⊆ A

data _⊩_∶_ : ∀ {A} -> ICtxt -> Λ A -> IType -> Set
data _⊩ₗ_∶_ : ∀ {A} -> ICtxt -> Λ A -> List IType -> Set

data _⊩_∶_ where
  var : ∀ {A Γ x τ} {τᵢ : List IType} ->
    (wf-Γ : Wf-ICtxt Γ) -> (τᵢ∈Γ : (x , (τᵢ , A)) ∈ Γ) -> (τ⊆τᵢ : (∩' τ) ⊆ₗ[ A ] τᵢ) ->
    -----------------------------------------------------------------------------------
                                    Γ ⊩ fv {A} x ∶ τ
  app : ∀ {A B Γ s t τ τ₁ τ₂} ->
    Γ ⊩ s ∶ (τ₁ ~> τ₂) -> Γ ⊩ₗ t ∶ τ₁ -> (∩' τ) ⊆ₗ[ B ] τ₂ ->
    ----------------------------------------------------------
                  Γ ⊩ (app {A} {B} s t) ∶ τ
  abs : ∀ {A B Γ τ τ'} (L : FVars) -> ∀ {t : Λ B} ->
    ( cf : ∀ {x} -> (x∉L : x ∉ L) -> ((x , (τ , A)) ∷ Γ) ⊩ₗ Λ[ 0 >> fv {A} x ] t ∶ τ' ) ->
    --------------------------------------------------------------------------------------
                                  Γ ⊩ lam A t ∶ (τ ~> τ')
  Y : ∀ {Γ A τ τ₁ τ₂} ->
    (wf-Γ : Wf-ICtxt Γ) -> (∩' (τ ~> τ)) ⊆ₗ[ A ⟶ A ] τ₁ -> τ₂ ⊆ₗ[ A ] τ -> -- ∃(λ τ' -> (τ' ∈ τ₁) × ((τ ~> τ) ⊆[ A ⟶ A ] τ')) -> τ₁ ∷'ₗ (A ⟶ A) ->
    ----------------------------------------------------------------------
                            Γ ⊩ Y A ∶ (τ₁ ~> τ₂)
  ~>∩ : ∀ {Γ A B τ τ₁ τ₂ τ₁++τ₂} {m : Λ (A ⟶ B)} ->
    Γ ⊩ m ∶ (τ ~> τ₁) -> Γ ⊩ m ∶ (τ ~> τ₂) -> τ₁++τ₂ ⊆ₗ[ B ] (τ₁ ++ τ₂) -> -- τ₁++τ₂ ≈ (τ₁ ++ τ₂) ->
    ----------------------------------------------------------------------
                            Γ ⊩ m ∶ (τ ~> τ₁++τ₂)



data _⊩ₗ_∶_ where
  nil : ∀ {A Γ} {m : Λ A} ->
    (wf-Γ : Wf-ICtxt Γ) ->
    ----------------------
          Γ ⊩ₗ m  ∶ ω
  cons : ∀ {A Γ τ τᵢ} {m : Λ A} ->
    Γ ⊩ m  ∶ τ -> Γ ⊩ₗ m  ∶ τᵢ ->
    --------------------------------
          Γ ⊩ₗ m  ∶ (τ ∷ τᵢ)
  -- subₗ : ∀ {A Γ τ τ'} {m : Λ A} ->
  --   Γ ⊩ₗ m ∶ τ -> τ' ⊆ₗ[ A ] τ ->
  --   -----------------------------
  --           Γ ⊩ₗ m ∶ τ'


data _⊆Γ_ : ICtxt -> ICtxt -> Set where
  nil : ∀ {Γ} ->
    (wf-Γ : Wf-ICtxt Γ) ->
    ----------------------
          [] ⊆Γ Γ
  cons : ∀ {A x τ' Γ Γ'} ->
    ∃(λ τ -> ((x , (τ , A)) ∈ Γ') × (τ' ⊆ₗ[ A ] τ)) -> Γ ⊆Γ Γ' ->
    -------------------------------------------------------------
                      ((x , (τ' , A)) ∷ Γ) ⊆Γ Γ'


⊩ₗ-wf-Γ : ∀ {A Γ} {m : Λ A} {τ} -> Γ ⊩ₗ m ∶ τ -> Wf-ICtxt Γ
⊩ₗ-wf-Γ (nil wf-Γ) = wf-Γ
⊩ₗ-wf-Γ (cons _ Γ⊩ₗm∶τ) = ⊩ₗ-wf-Γ Γ⊩ₗm∶τ
-- ⊩ₗ-wf-Γ (subₗ x _) = ⊩ₗ-wf-Γ x

⊩-wf-Γ : ∀ {A Γ} {m : Λ A} {τ} -> Γ ⊩ m ∶ τ -> Wf-ICtxt Γ
⊩-wf-Γ (var wf-Γ τᵢ∈Γ τ⊆τᵢ) = wf-Γ
⊩-wf-Γ (app Γ⊩m∶τ _ _) = ⊩-wf-Γ Γ⊩m∶τ
⊩-wf-Γ (abs L cf) = cons' (⊩ₗ-wf-Γ (cf x∉))
  where
  x = ∃fresh L

  x∉ : x ∉ L
  x∉ = ∃fresh-spec L

  cons' : ∀ {x τ A Γ} -> Wf-ICtxt ((x , τ , A) ∷ Γ) -> Wf-ICtxt Γ
  cons' (cons x∉ x₂ wf-Γ) = wf-Γ

⊩-wf-Γ (Y wf-Γ x x₁) = wf-Γ
⊩-wf-Γ (~>∩ Γ⊩m∶τ Γ⊩m∶τ₁ x) = ⊩-wf-Γ Γ⊩m∶τ₁

⊆Γ-wfΓ' : ∀ {Γ Γ'} -> Γ ⊆Γ Γ' -> Wf-ICtxt Γ'
⊆Γ-wfΓ' (nil wf-Γ') = wf-Γ'
⊆Γ-wfΓ' (cons _ Γ⊆Γ') = ⊆Γ-wfΓ' Γ⊆Γ'

wf-Γ-∷'ₗ : ∀ {A x τ Γ} -> (x , (τ , A)) ∈ Γ -> Wf-ICtxt Γ -> τ ∷'ₗ A
wf-Γ-∷'ₗ (here refl) (cons _ x₁ _) = x₁
wf-Γ-∷'ₗ (there xτA∈Γ) (cons _ _ wf-Γ) = wf-Γ-∷'ₗ xτA∈Γ wf-Γ


⊆Γ-⊆ : ∀ {Γ Γ'} -> Wf-ICtxt Γ' -> Γ ⊆ Γ' -> Γ ⊆Γ Γ'
⊆Γ-⊆ {[]} wf-Γ' Γ⊆Γ' = nil wf-Γ'
⊆Γ-⊆ {(x , τ , A) ∷ Γ} wf-Γ' Γ⊆Γ' = cons
  (τ , ((Γ⊆Γ' (here refl)) , ⊆ₗ-refl (wf-Γ-∷'ₗ (Γ⊆Γ' (here refl)) wf-Γ')))
  (⊆Γ-⊆ wf-Γ' (λ {x₁} z → Γ⊆Γ' (there z)))


∈-⊆Γ-trans : ∀ {A x τᵢ} {Γ Γ'} -> (x , (τᵢ , A)) ∈ Γ -> Γ ⊆Γ Γ' -> ∃(λ τᵢ' -> ((x , (τᵢ' , A)) ∈ Γ') × τᵢ ⊆ₗ[ A ] τᵢ')
∈-⊆Γ-trans (here refl) (cons x _) = x
∈-⊆Γ-trans (there x∈L) (cons _ L⊆L') = ∈-⊆Γ-trans x∈L L⊆L'


⊆Γ-∷ : ∀ {A x τᵢ Γ Γ'} -> x ∉ dom Γ' -> τᵢ ∷'ₗ A -> Γ ⊆Γ Γ' -> Γ ⊆Γ ((x , τᵢ , A) ∷ Γ')
⊆Γ-∷ {Γ = []} x∉Γ' τᵢ∷A Γ⊆Γ' = nil (cons x∉Γ' τᵢ∷A (⊆Γ-wfΓ' Γ⊆Γ'))
⊆Γ-∷ {Γ = (x , τᵢ , A) ∷ Γ} x∉Γ' τᵢ∷A (cons (proj₁ , proj₂ , proj₃) Γ⊆Γ') =
  cons (proj₁ , ((there proj₂) , proj₃)) (⊆Γ-∷ x∉Γ' τᵢ∷A Γ⊆Γ')


arr' : ∀ {A B τ τ'} -> (τ ~> τ') ∷' (A ⟶ B) -> (τ ∷'ₗ A × τ' ∷'ₗ B)
arr' (arr x y) = x , y

⊆-∷'ₗ : ∀ {A τᵢ τⱼ} -> τᵢ ⊆ τⱼ -> τⱼ ∷'ₗ A -> τᵢ ∷'ₗ A
⊆-∷'ₗ {τᵢ = []} τᵢ⊆τⱼ τⱼ∷' = nil
⊆-∷'ₗ {τᵢ = x ∷ τᵢ} x∷τᵢ⊆τⱼ τⱼ∷' = cons (∷'ₗ-∈ (x∷τᵢ⊆τⱼ (here refl)) τⱼ∷') (⊆-∷'ₗ {τᵢ = τᵢ} (λ {x₁} z → x∷τᵢ⊆τⱼ (there z)) τⱼ∷')



data Tree : Set where
  * : Tree
  U : Tree -> Tree
  _&_ : Tree -> Tree -> Tree


data _~T_ : ∀ {τ} -> Λ τ -> Tree -> Set where
  l-bv : ∀ {A i} -> bv {A} i ~T *
  l-fv : ∀ {A x} -> fv {A} x ~T *
  l-Y : ∀ {A} -> Y A ~T *
  un : ∀ {A B v} {e : Λ B} -> e ~T v -> (lam A e) ~T (U v)
  bin : ∀ {A B v w} {s : Λ (A ⟶ B)} {t : Λ A} -> s ~T v -> t ~T w -> (app s t) ~T (v & w)


^'-~T-inv : ∀ {A B x t k} {m : Λ A} -> m ~T t -> Λ[ k >> fv {B} x ] m ~T t
^'-~T-inv {A} {B} {x} {_} {k} {bv i} l-bv with k ≟ i
^'-~T-inv {A} {B} {x} {.*} {k} {bv .k} l-bv | yes refl with A ≟T B
^'-~T-inv {A} {.A} {x} {.*} {k} {bv .k} l-bv | yes refl | yes refl = l-fv
^'-~T-inv {A} {B} {x} {.*} {k} {bv .k} l-bv | yes refl | no _ = l-bv
^'-~T-inv {A} {B} {x} {.*} {k} {bv i} l-bv | no _ = l-bv
^'-~T-inv l-fv = l-fv
^'-~T-inv l-Y = l-Y
^'-~T-inv (un m~Tt) = un (^'-~T-inv m~Tt)
^'-~T-inv (bin m~Tt m~Tt₁) = bin (^'-~T-inv m~Tt) (^'-~T-inv m~Tt₁)


∃~T : ∀ {A} (m : Λ A) -> ∃(λ t -> m ~T t)
∃~T (bv i) = * , l-bv
∃~T (fv x) = * , l-fv
∃~T (lam A m) = (U (proj₁ ih)) , (un (proj₂ ih))
  where
  ih = ∃~T m
∃~T (app m m₁) = ((proj₁ ihₗ) & (proj₁ ihᵣ)) , bin (proj₂ ihₗ) (proj₂ ihᵣ)
  where
  ihₗ = ∃~T m
  ihᵣ = ∃~T m₁
∃~T (Y t) = * , l-Y



⊩-∷'-aux : ∀ {A Γ} {m : Λ A} {τ} {t} -> m ~T t -> Γ ⊩ m ∶ τ -> τ ∷' A
⊩ₗ-∷'ₗ-aux : ∀ {A Γ} {m : Λ A} {τ} {t} -> m ~T t -> Γ ⊩ₗ m ∶ τ -> τ ∷'ₗ A

⊩-∷'-aux l-fv (var _ _ τ⊆τᵢ) = ∷'ₗ-∈ (here refl) (⊆ₗ-∷'ₗ-l τ⊆τᵢ)
⊩-∷'-aux (bin _ _) (app _ _ τ⊆τᵢ) = ∷'ₗ-∈ (here refl) (⊆ₗ-∷'ₗ-l τ⊆τᵢ)
⊩-∷'-aux (un m~Tt) (abs L cf) = arr (cons' (⊩ₗ-wf-Γ body)) (⊩ₗ-∷'ₗ-aux (^'-~T-inv m~Tt) body) -- arr {!   !} (⊩ₗ-∷'ₗ-aux {!   !} body)
  where
  x = ∃fresh L

  x∉ : x ∉ L
  x∉ = ∃fresh-spec L

  body = cf x∉

  cons' : ∀ {x τ A Γ} -> Wf-ICtxt ((x , τ , A) ∷ Γ) -> τ ∷'ₗ A
  cons' (cons _ x _) = x

⊩-∷'-aux l-Y (Y _ τ⊆τ~>τ τ₂⊆τ) = arr (⊆ₗ-∷'ₗ-r τ⊆τ~>τ) (⊆ₗ-∷'ₗ-l τ₂⊆τ)
⊩-∷'-aux m~Tt (~>∩ x y τ₁τ₂⊆τ₁++τ₂) = arr τ∷ (⊆ₗ-∷'ₗ-l τ₁τ₂⊆τ₁++τ₂)
  where
  τ~>τ₁∷ = ⊩-∷'-aux m~Tt x
  τ∷ = proj₁ (arr' τ~>τ₁∷)

⊩ₗ-∷'ₗ-aux m~Tt (nil _) = nil
⊩ₗ-∷'ₗ-aux m~Tt (cons Γ⊩m∶τ Γ⊩ₗm∶τᵢ) = cons (⊩-∷'-aux m~Tt Γ⊩m∶τ) (⊩ₗ-∷'ₗ-aux m~Tt Γ⊩ₗm∶τᵢ)
-- ⊩ₗ-∷'ₗ (subₗ _ x) = ⊆ₗ-∷'ₗ-l x

⊩-∷' : ∀ {A Γ} {m : Λ A} {τ} -> Γ ⊩ m ∶ τ -> τ ∷' A
⊩-∷' {m = m} = ⊩-∷'-aux (proj₂ (∃~T m))
⊩ₗ-∷'ₗ : ∀ {A Γ} {m : Λ A} {τ} -> Γ ⊩ₗ m ∶ τ -> τ ∷'ₗ A
⊩ₗ-∷'ₗ {m = m} = ⊩ₗ-∷'ₗ-aux (proj₂ (∃~T m))


⊩ₗ-++ : ∀ {A Γ} {n : Λ A} {τₗ τᵣ} -> Γ ⊩ₗ n ∶ τₗ -> Γ ⊩ₗ n ∶ τᵣ -> Γ ⊩ₗ n ∶ (τₗ ++ τᵣ)
⊩ₗ-++ (nil wf-Γ) Γ⊩ₗn∶τᵣ = Γ⊩ₗn∶τᵣ
⊩ₗ-++ (cons x Γ⊩ₗn∶τₗ) Γ⊩ₗn∶τᵣ = cons x (⊩ₗ-++ Γ⊩ₗn∶τₗ Γ⊩ₗn∶τᵣ)

data _->Λβ_ : ∀ {τ} -> Λ τ ↝ Λ τ where
  redL : ∀ {A B} {n : Λ A} {m m' : Λ (A ⟶ B)} -> ΛTerm n -> m ->Λβ m' -> app m n ->Λβ app m' n
  redR : ∀ {A B} {m : Λ (A ⟶ B)} {n n' : Λ A} -> ΛTerm m -> n ->Λβ n' -> app m n ->Λβ app m n'
  abs : ∀ L {A B} {m m' : Λ B} -> ( ∀ {x} -> x ∉ L -> Λ[ 0 >> fv {A} x ] m ->Λβ Λ[ 0 >> fv {A} x ] m' ) ->
    lam A m ->Λβ lam A m'
  beta : ∀ {A B} {m : Λ B} {n : Λ A} -> ΛTerm (lam A m) -> ΛTerm n -> app (lam A m) n ->Λβ (Λ[ 0 >> n ] m)
  Y : ∀ {A} {m : Λ (A ⟶ A)} -> ΛTerm m -> app (Y A) m ->Λβ app m (app (Y A) m)


subΓ : ∀ {A Γ Γ'} {m : Λ A} {τ} -> Γ ⊩ m ∶ τ -> Γ ⊆Γ Γ' -> Γ' ⊩ m ∶ τ
subₗΓ : ∀ {A Γ Γ'} {m : Λ A} {τ} -> Γ ⊩ₗ m ∶ τ -> Γ ⊆Γ Γ' -> Γ' ⊩ₗ m ∶ τ

subΓ (var wf-Γ τᵢ∈Γ τ⊆τᵢ) Γ⊆Γ' = var (⊆Γ-wfΓ' Γ⊆Γ') τᵢ'∈ (⊆ₗ-trans τ⊆τᵢ τᵢ⊆τᵢ')
  where
  τᵢ'∈ = proj₁ (proj₂ (∈-⊆Γ-trans τᵢ∈Γ Γ⊆Γ'))
  τᵢ⊆τᵢ' = proj₂ (proj₂ (∈-⊆Γ-trans τᵢ∈Γ Γ⊆Γ'))

subΓ (app Γ⊩m∶τ x x₁) Γ⊆Γ' = app (subΓ Γ⊩m∶τ Γ⊆Γ') (subₗΓ x Γ⊆Γ') x₁
subΓ {A ⟶ B} {Γ' = Γ'} (abs {τ = τ} L cf) Γ⊆Γ' = abs
  (L ++ dom Γ')
  (λ x∉ → subₗΓ
    (cf (∉-cons-l _ _ x∉))
    (cons
      (τ , (here refl) , (⊆ₗ-refl (τ∷ (∉-cons-l _ _ x∉))))
      (⊆Γ-∷ (∉-cons-r L _ x∉) (τ∷ (∉-cons-l _ _ x∉)) Γ⊆Γ')))
  where
  cons' : ∀ {x τ A Γ} -> Wf-ICtxt ((x , τ , A) ∷ Γ) -> τ ∷'ₗ A
  cons' (cons _ x _) = x

  τ∷ : ∀ {x} -> x ∉ L -> τ ∷'ₗ A
  τ∷ x∉ = cons' (⊩ₗ-wf-Γ (cf x∉))
subΓ (Y x x₁ x₂) Γ⊆Γ' = Y (⊆Γ-wfΓ' Γ⊆Γ') x₁ x₂
subΓ (~>∩ x x₁ z) Γ⊆Γ' = ~>∩ (subΓ x Γ⊆Γ') (subΓ x₁ Γ⊆Γ') z

subₗΓ (nil wf-Γ) Γ⊆Γ' = nil (⊆Γ-wfΓ' Γ⊆Γ')
subₗΓ (cons x Γ⊩ₗm∶τ) Γ⊆Γ' = cons (subΓ x Γ⊆Γ') (subₗΓ Γ⊩ₗm∶τ Γ⊆Γ')
-- subₗΓ (subₗ x y) Γ⊆Γ' = subₗ (subₗΓ x Γ⊆Γ') y


⊩ₗ-∈-⊩ : ∀ {A Γ} {m : Λ A} {τ τᵢ} -> Γ ⊩ₗ m ∶ τᵢ -> τ ∈ τᵢ -> Γ ⊩ m ∶ τ
⊩ₗ-∈-⊩ (nil _) ()
⊩ₗ-∈-⊩ (cons Γ⊩m∶τ x) (here refl) = Γ⊩m∶τ
⊩ₗ-∈-⊩ (cons _ Γ⊩ₗm∶τᵢ) (there τ∈τᵢ) = ⊩ₗ-∈-⊩ Γ⊩ₗm∶τᵢ τ∈τᵢ

∈-++-∨ : ∀ {a} {A : Set a} {x : A} xs {ys} -> x ∈ (xs ++ ys) -> (x ∈ xs) ∨ (x ∈ ys)
∈-++-∨ [] x∈xs++ys = inj₂ x∈xs++ys
∈-++-∨ (x ∷ xs) (here refl) = inj₁ (here refl)
∈-++-∨ (x ∷ xs) (there x∈xs++ys) = Data.Sum.map there (λ x → x) (∈-++-∨ xs x∈xs++ys)


∈-∨-++ : ∀ {a} {A : Set a} {x : A} {xs ys} -> (x ∈ xs) ∨ (x ∈ ys) -> x ∈ (xs ++ ys)
∈-∨-++ {ys = ys} (inj₁ x∈xs) = ∈-cons-l ys x∈xs
∈-∨-++ {xs = xs} (inj₂ x∈ys) = ∈-cons-r xs x∈ys



∷'ₗ-++ : ∀ {A τᵢ τⱼ} -> τᵢ ∷'ₗ A -> τⱼ ∷'ₗ A -> (τᵢ ++ τⱼ) ∷'ₗ A
∷'ₗ-++ nil τⱼ∷A = τⱼ∷A
∷'ₗ-++ (cons x τᵢ∷A) τⱼ∷A = cons x (∷'ₗ-++ τᵢ∷A τⱼ∷A)

∨-comm : ∀ {a} {P Q : Set a} → (P ∨ Q) → (Q ∨ P)
∨-comm (inj₁ p) = inj₂ p
∨-comm (inj₂ q) = inj₁ q

⊆-++-comm : ∀ {a} {A : Set a} {X Y : List A} -> (X ++ Y) ⊆ (Y ++ X)
⊆-++-comm {X = X} x∈X++Y = ∈-∨-++ (∨-comm (∈-++-∨ X x∈X++Y))

⊆ₗ-++-comm : ∀ {A τᵢ τⱼ τ} -> (τᵢ ++ τⱼ) ⊆ₗ[ A ] τ -> (τⱼ ++ τᵢ) ⊆ₗ[ A ] τ
⊆ₗ-++-comm {A} {τᵢ} {τⱼ} τᵢ++τⱼ⊆ₗτ = ⊆ₗ-trans (⊆ₗ-⊆ (⊆-++-comm {X = τⱼ} {τᵢ}) (∷'ₗ-++ {A} {τᵢ} {τⱼ} (∷'ₗ-++-l τᵢ++τⱼ∷'A) (∷'ₗ-++-r {τᵢ = τᵢ} τᵢ++τⱼ∷'A))) τᵢ++τⱼ⊆ₗτ
  where
  τᵢ++τⱼ∷'A = ⊆ₗ-∷'ₗ-l τᵢ++τⱼ⊆ₗτ



⊆ₗ++-r : ∀ {A τᵢ τᵢ' τⱼ} -> τᵢ ⊆ₗ[ A ] τᵢ' -> τⱼ ∷'ₗ A -> (τᵢ ++ τⱼ) ⊆ₗ[ A ] (τᵢ' ++ τⱼ)
⊆ₗ++-r {τᵢ' = τᵢ'} {τⱼ} (nil x) τⱼ∷'A = ⊆ₗ-⊆ (λ x₂ → ∈-cons-r τᵢ' x₂) (∷'ₗ-++ x τⱼ∷'A)
⊆ₗ++-r (cons (τ , τ∈τᵢ , τ'⊆τ) τᵢ⊆τᵢ') τⱼ∷'A = cons (τ , (∈-cons-l _ τ∈τᵢ , τ'⊆τ)) (⊆ₗ++-r τᵢ⊆τᵢ' τⱼ∷'A)
⊆ₗ++-r {τⱼ = τⱼ} (~>∩ x) τⱼ∷'A = ~>∩ (∷'ₗ-++ {τⱼ = τⱼ} x τⱼ∷'A)
⊆ₗ++-r (⊆ₗ-trans τᵢ⊆τᵢ'' τᵢ''⊆τᵢ') τⱼ∷'A = ⊆ₗ-trans (⊆ₗ++-r τᵢ⊆τᵢ'' τⱼ∷'A) (⊆ₗ++-r τᵢ''⊆τᵢ' τⱼ∷'A)

⊆ₗ++-l : ∀ {A τᵢ τⱼ τⱼ'} -> τⱼ ⊆ₗ[ A ] τⱼ' -> τᵢ ∷'ₗ A -> (τᵢ ++ τⱼ) ⊆ₗ[ A ] (τᵢ ++ τⱼ')
⊆ₗ++-l {τᵢ = []} τⱼ⊆τⱼ' τᵢ∷'ₗ = τⱼ⊆τⱼ'
⊆ₗ++-l {τᵢ = τ ∷ τᵢ} {τⱼ} {τⱼ'} τⱼ⊆τⱼ' (cons x τᵢ∷'ₗ) =
  cons (τ , ((here refl) , (⊆-refl x))) (⊆ₗ-trans {τⱼ = τᵢ ++ τⱼ'} (⊆ₗ++-l τⱼ⊆τⱼ' τᵢ∷'ₗ) (⊆ₗ-⊆ (λ {x₁} → there) (++-∷'ₗ (cons x τᵢ∷'ₗ) (⊆ₗ-∷'ₗ-r τⱼ⊆τⱼ'))))


∷-≡ : ∀ {a} {A : Set a} {x y : A} {X Y : List A} ->  x ≡ y -> X ≡ Y -> (x ∷ X) ≡ y ∷ Y
∷-≡ refl refl = refl

++[]-≡ : ∀ {a} {A : Set a} {X : List A} -> X ≡ X ++ []
++[]-≡ {X = []} = refl
++[]-≡ {X = x ∷ X} = ∷-≡ refl ++[]-≡

++[]-≡2 : ∀ {a} {A : Set a} {X : List A} -> X ++ [] ≡ X
++[]-≡2 {X = []} = refl
++[]-≡2 {X = x ∷ X} = ∷-≡ refl ++[]-≡2

++[]++-≡ : ∀ {a} {A : Set a} {X Y : List A} -> (X ++ []) ++ Y ≡ X ++ Y
++[]++-≡ {X = X} rewrite ++[]-≡2 {X = X} = λ {Y₁} → refl


⊆ₗ++-l' : ∀ {A τᵢ τⱼ} -> τᵢ ∷'ₗ A -> τⱼ ∷'ₗ A -> τᵢ ⊆ₗ[ A ] (τᵢ ++ τⱼ)
⊆ₗ++-l' {A} {τᵢ} {τⱼ} τᵢ∷' τⱼ∷' rewrite ++[]-≡ {X = τᵢ} | ++[]++-≡ {X = τᵢ} {Y = τⱼ} = ⊆ₗ++-l {τᵢ = τᵢ} {[]} (nil τⱼ∷') τᵢ∷''
  where
  τᵢ∷'' : τᵢ ∷'ₗ A
  τᵢ∷'' rewrite ++[]-≡ {X = τᵢ} = τᵢ∷'


⊩++ : ∀ {A Γ} {m : Λ (A ⟶ A)} {τᵢ τⱼ} -> Γ ⊩ₗ m ∶ τᵢ -> Γ ⊩ₗ m ∶ τⱼ -> Γ ⊩ₗ m ∶ (τᵢ ++ τⱼ)
⊩++ {τᵢ = []} Γ⊩ₗm∶τᵢ Γ⊩ₗm∶τⱼ = Γ⊩ₗm∶τⱼ
⊩++ {τᵢ = x ∷ τᵢ} (cons x₁ Γ⊩ₗm∶τᵢ) Γ⊩ₗm∶τⱼ = cons x₁ (⊩++ Γ⊩ₗm∶τᵢ Γ⊩ₗm∶τⱼ)
-- ⊩++ {τᵢ = x ∷ τᵢ} (subₗ Γ⊩ₗm∶τᵢ x₁) Γ⊩ₗm∶τⱼ = subₗ (⊩++ Γ⊩ₗm∶τᵢ Γ⊩ₗm∶τⱼ) (⊆ₗ++-r x₁ (⊩ₗ-∷'ₗ Γ⊩ₗm∶τⱼ))

⊆-++-ctrct : ∀ {a} {A : Set a} {X : List A} -> X ++ X ⊆ X
⊆-++-ctrct {X = X} x∈X++X with ∈-++-∨ X x∈X++X
⊆-++-ctrct x∈X++X | inj₁ x = x
⊆-++-ctrct x∈X++X | inj₂ x = x


glb : ∀ {A τ τᵢ τⱼ} -> τᵢ ⊆ₗ[ A ] τ -> τⱼ ⊆ₗ[ A ] τ -> (τᵢ ++ τⱼ) ⊆ₗ[ A ] τ
glb (nil x) τⱼ⊆τ = τⱼ⊆τ
glb (cons x τᵢ⊆τ) τⱼ⊆τ = cons x (glb τᵢ⊆τ τⱼ⊆τ)
glb {A ⟶ B} {τⱼ = τⱼ} (~>∩ {τ = τ} {τᵢ} {τᵢ'} {τₓ} (cons (arr x x₁) x₂)) τⱼ⊆τ = ⊆ₗ-trans {τⱼ = ((τ ~> τᵢ) ∷ (τ ~> τᵢ') ∷ τₓ ++ τⱼ)}
  (~>∩ (∷'ₗ-++ {τᵢ = (τ ~> (τᵢ ++ τᵢ')) ∷ τₓ} {τⱼ} (cons (arr x x₁) x₂) (⊆ₗ-∷'ₗ-l τⱼ⊆τ)))
  (⊆ₗ-++-comm {τᵢ = τⱼ} {(τ ~> τᵢ) ∷ (τ ~> τᵢ') ∷ τₓ}
    (⊆ₗ-trans {τⱼ = ((τ ~> τᵢ) ∷ (τ ~> τᵢ') ∷ τₓ) ++ (τ ~> τᵢ) ∷ (τ ~> τᵢ') ∷ τₓ}
      (⊆ₗ++-r {τⱼ = ((τ ~> τᵢ) ∷ (τ ~> τᵢ') ∷ τₓ)} τⱼ⊆τ ∷'A⟶B)
      (⊆ₗ-⊆ (⊆-++-ctrct {X = (τ ~> τᵢ) ∷ (τ ~> τᵢ') ∷ τₓ}) ∷'A⟶B)))
  where
  ∷'A⟶B : ((τ ~> τᵢ) ∷ (τ ~> τᵢ') ∷ τₓ) ∷'ₗ (A ⟶ B)
  ∷'A⟶B = cons (arr x (∷'ₗ-++-l x₁)) (cons (arr x (∷'ₗ-++-r {τᵢ = τᵢ} x₁)) x₂)

glb (⊆ₗ-trans τᵢ⊆τᵢ' τᵢ'⊆τᵢ) τⱼ⊆τ = ⊆ₗ-trans (⊆ₗ++-r τᵢ⊆τᵢ' (⊆ₗ-∷'ₗ-l τⱼ⊆τ)) (glb τᵢ'⊆τᵢ τⱼ⊆τ)

mon : ∀ {A τ τ' τᵢ τᵢ'} -> τ ⊆ₗ[ A ] τ' -> τᵢ ⊆ₗ[ A ] τᵢ' -> (τ ++ τᵢ) ⊆ₗ[ A ] (τ' ++ τᵢ')
mon {τ' = τ'} τ⊆τ' τᵢ⊆τᵢ' = glb
  (⊆ₗ-trans τ⊆τ' (⊆ₗ-⊆ (λ x₁ → ∈-cons-l _ x₁) (∷'ₗ-++ (⊆ₗ-∷'ₗ-r τ⊆τ') (⊆ₗ-∷'ₗ-r τᵢ⊆τᵢ'))))
  (⊆ₗ-trans τᵢ⊆τᵢ' (⊆ₗ-⊆ (λ x₁ → ∈-cons-r τ' x₁) (∷'ₗ-++ (⊆ₗ-∷'ₗ-r τ⊆τ') (⊆ₗ-∷'ₗ-r τᵢ⊆τᵢ'))))



sub : ∀ {A Γ Γ'} {m : Λ A} {τ τ'} -> Γ ⊩ m ∶ τ -> τ' ⊆[ A ] τ -> Γ ⊆Γ Γ' -> Γ' ⊩ m ∶ τ'
subₗ : ∀ {A Γ Γ'} {m : Λ A} {τ τ'} -> Γ ⊩ₗ m ∶ τ -> τ' ⊆ₗ[ A ] τ -> Γ ⊆Γ Γ' -> Γ' ⊩ₗ m ∶ τ'

sub (var wf-Γ τᵢ∈Γ τ⊆τᵢ) τ'⊆τ Γ⊆Γ' =
  var (⊆Γ-wfΓ' Γ⊆Γ') τᵢ'∈ (⊆ₗ-trans (⊆ₗ-trans (⊆->⊆ₗ τ'⊆τ) τ⊆τᵢ) τᵢ⊆τᵢ')
  where
  τᵢ'∈ = proj₁ (proj₂ (∈-⊆Γ-trans τᵢ∈Γ Γ⊆Γ'))
  τᵢ⊆τᵢ' = proj₂ (proj₂ (∈-⊆Γ-trans τᵢ∈Γ Γ⊆Γ'))

sub (app Γ⊩s∶τ₁~>τ₂ Γ⊩ₗt∶τ₁ τ⊆τ₂) τ'⊆τ Γ⊆Γ' = app
  (subΓ Γ⊩s∶τ₁~>τ₂ Γ⊆Γ')
  (subₗΓ Γ⊩ₗt∶τ₁ Γ⊆Γ')
  (⊆ₗ-trans (⊆->⊆ₗ τ'⊆τ) τ⊆τ₂)
sub {_} {Γ} {Γ'} (abs {τ = τ} {τ'} L {t} cf) (arr {A} {τ₁₁ = τ₁₁} τ⊆τ₁₁ τ₁₂⊆τ') Γ⊆Γ' = abs
  (L ++ dom Γ')
  (λ x∉ → subₗ
    (cf (∉-cons-l _ _ x∉))
    τ₁₂⊆τ'
    (cons (τ₁₁ , (here refl) , τ⊆τ₁₁) (⊆Γ-∷ (∉-cons-r L _ x∉) (⊆ₗ-∷'ₗ-r τ⊆τ₁₁) Γ⊆Γ'))
  )
sub (Y wf-Γ τ₁⊆τ~>τ τ₂⊆τ) (arr {τ₁₁ = τ₁'} τ₁⊆τ₁' τ₂'⊆τ₂) Γ⊆Γ' =
  Y (⊆Γ-wfΓ' Γ⊆Γ') (⊆ₗ-trans τ₁⊆τ~>τ τ₁⊆τ₁') (⊆ₗ-trans τ₂'⊆τ₂ τ₂⊆τ)
sub {_} {Γ} {Γ'} {m} (~>∩ {A = A} {B} {τ} {τ₁} {τ₂} {τ₁τ₂} x y τ₁τ₂⊆τ₁++τ₂) (arr {τ₁₁ = τ'} {τ₁τ₂'} τ⊆τ' τ₁τ₂'⊆τ₁τ₂) Γ⊆Γ' =
  ~>∩ (sub x (arr τ⊆τ' (⊆ₗ-refl τ₁∷')) Γ⊆Γ') (sub y (arr τ⊆τ' (⊆ₗ-refl τ₂∷')) Γ⊆Γ') (⊆ₗ-trans τ₁τ₂'⊆τ₁τ₂ τ₁τ₂⊆τ₁++τ₂)
  where
  τ~>τ₁ = ⊩-∷' x
  τ~>τ₂ = ⊩-∷' y

  τ∷' = ⊆ₗ-∷'ₗ-l τ⊆τ'
  τ'∷' = ⊆ₗ-∷'ₗ-r τ⊆τ'
  τ₁∷' = proj₂ (arr' τ~>τ₁)
  τ₂∷' = proj₂ (arr' τ~>τ₂)

subₗ Γ⊩ₗm∶τ (nil x) Γ⊆Γ' = nil (⊆Γ-wfΓ' Γ⊆Γ')
subₗ Γ⊩ₗm∶τᵢ (cons (τ , τ∈τᵢ , τ'⊆τ) τ'ᵢ⊆τᵢ) Γ⊆Γ' with ⊩ₗ-∈-⊩ Γ⊩ₗm∶τᵢ τ∈τᵢ
... | Γ⊩m∶τ = cons (sub Γ⊩m∶τ τ'⊆τ Γ⊆Γ') (subₗ Γ⊩ₗm∶τᵢ τ'ᵢ⊆τᵢ Γ⊆Γ')
subₗ (cons x (cons x₁ Γ⊩ₗm∶τ)) (~>∩ (cons (arr x₂ x₃) x₄)) Γ⊆Γ' =
  cons (~>∩ (subΓ x Γ⊆Γ') (subΓ x₁ Γ⊆Γ') (⊆ₗ-refl τ₁++τ₂∷')) (subₗΓ Γ⊩ₗm∶τ Γ⊆Γ')
  where
  τ~>τ₁ = ⊩-∷' x
  τ~>τ₂ = ⊩-∷' x₁
  τ₁++τ₂∷' = ++-∷'ₗ (proj₂ (arr' τ~>τ₁)) (proj₂ (arr' τ~>τ₂))
subₗ Γ⊩ₗm∶τ (⊆ₗ-trans τ'⊆τ τ'⊆τ₁) Γ⊆Γ' = subₗ (subₗ Γ⊩ₗm∶τ τ'⊆τ₁ Γ⊆Γ') τ'⊆τ (⊆Γ-⊆ (⊆Γ-wfΓ' Γ⊆Γ') (λ {x} z → z))



~>∩' : ∀ {A τₗ τᵣ} -> τₗ ∷'ₗ A -> τᵣ ∷'ₗ A -> ∩' ((τₗ ++ τᵣ) ~> (τₗ ++ τᵣ)) ⊆ₗ[ A ⟶ A ] ((τₗ ~> τₗ) ∩ (τᵣ ~> τᵣ))
~>∩' {A} {τₗ} {τᵣ} τₗ∷ τᵣ∷ = ⊆ₗ-trans {τⱼ = ((τₗ ++ τᵣ) ~> τₗ) ∩ ((τₗ ++ τᵣ) ~> τᵣ)}
  (~>∩ (cons (arr (∷'ₗ-++ τₗ∷ τᵣ∷) (∷'ₗ-++ τₗ∷ τᵣ∷)) nil))
  (cons (_ , ((here refl) , (arr (⊆ₗ-⊆ (λ x₁ → ∈-cons-l _ x₁) (∷'ₗ-++ τₗ∷ τᵣ∷)) (⊆ₗ-refl τₗ∷))))
  (cons (_ , ((there (here refl)) , (arr (⊆ₗ-⊆ (λ x₁ → ∈-cons-r τₗ x₁) (∷'ₗ-++ τₗ∷ τᵣ∷)) (⊆ₗ-refl τᵣ∷))))
  (nil (cons (arr τₗ∷ τₗ∷) (cons (arr τᵣ∷ τᵣ∷) nil)))))


Y-inv : ∀ {A Γ τ₁ τ₂} -> Γ ⊩ Y A ∶ (τ₁ ~> τ₂) -> ∃(λ τ -> ((∩' (τ ~> τ)) ⊆ₗ[ A ⟶ A ] τ₁) × τ₂ ⊆ₗ[ A ] τ)
Y-inv (Y {τ = τ} wf-Γ x x₁) = τ , x , x₁
Y-inv {A} {Γ} {τ₁} {τ₂τ₃} (~>∩ {τ₁ = τ₂} {τ₃} Γ⊩Y∶τ₁~>τ₂ Γ⊩Y∶τ₁~>τ₃ τ₂τ₃⊆ₗτ₂++τ₃) =
  (τₗ ++ τᵣ) ,
  (⊆ₗ-trans (⊆ₗ-trans (~>∩' τₗ∷ τᵣ∷) (mon τₗ~>τₗ⊆ₗτ₁ τᵣ~>τᵣ⊆ₗτ₁)) (⊆ₗ-⊆ (⊆-++-ctrct {X = τ₁}) τ₁∷) ,
  ⊆ₗ-trans τ₂τ₃⊆ₗτ₂++τ₃ (mon τ₂⊆ₗτₗ τ₂⊆ₗτᵣ))
  where
  ihₗ : ∃(λ τ -> ((∩' (τ ~> τ)) ⊆ₗ[ A ⟶ A ] τ₁) × τ₂ ⊆ₗ[ A ] τ)
  ihₗ = Y-inv Γ⊩Y∶τ₁~>τ₂

  ihᵣ : ∃(λ τ -> ((∩' (τ ~> τ)) ⊆ₗ[ A ⟶ A ] τ₁) × τ₃ ⊆ₗ[ A ] τ)
  ihᵣ = Y-inv Γ⊩Y∶τ₁~>τ₃

  τₗ = proj₁ ihₗ
  τₗ~>τₗ⊆ₗτ₁ = proj₁ (proj₂ ihₗ)
  τ₂⊆ₗτₗ = proj₂ (proj₂ ihₗ)

  τᵣ = proj₁ ihᵣ
  τᵣ~>τᵣ⊆ₗτ₁ = proj₁ (proj₂ ihᵣ)
  τ₂⊆ₗτᵣ = proj₂ (proj₂ ihᵣ)

  τ₁∷ = ⊆ₗ-∷'ₗ-r τₗ~>τₗ⊆ₗτ₁
  τ₂∷ = ⊆ₗ-∷'ₗ-l τ₂⊆ₗτₗ
  τₗ∷ = ⊆ₗ-∷'ₗ-r τ₂⊆ₗτₗ
  τᵣ∷ = ⊆ₗ-∷'ₗ-r τ₂⊆ₗτᵣ


abs-inv : ∀ {A B Γ τ τ'} {t : Λ B} -> Γ ⊩ lam A t ∶ (τ ~> τ') -> ∃(λ L -> ( ∀ {x} -> (x∉L : x ∉ L) -> ((x , (τ , A)) ∷ Γ) ⊩ₗ Λ[ 0 >> fv {A} x ] t ∶ τ' ))
abs-inv (abs L cf) = L , cf
abs-inv {A} {B} {Γ} {τ} {τ₂τ₃} {t} (~>∩ {τ₁ = τ₂} {τ₃} Γ⊩lam-t Γ⊩lam-t₁ x) =
  (Lₗ ++ Lᵣ ++ dom Γ) ,
  (λ x∉ → subₗ
    (⊩ₗ-++ (cfₗ (∉-cons-l Lₗ _ x∉)) (cfᵣ (∉-cons-l Lᵣ _ (∉-cons-r Lₗ _ x∉))))
    x
    (⊆Γ-⊆ (cons (∉-cons-r Lᵣ _ (∉-cons-r Lₗ _ x∉)) (proj₁ (arr' (⊩-∷' Γ⊩lam-t))) (⊩-wf-Γ Γ⊩lam-t)) (λ x₂ → x₂)))
  where
  ihₗ : ∃(λ L -> ( ∀ {x} -> (x∉L : x ∉ L) -> ((x , (τ , A)) ∷ Γ) ⊩ₗ Λ[ 0 >> fv {A} x ] t ∶ τ₂ ))
  ihₗ = abs-inv Γ⊩lam-t

  ihᵣ : ∃(λ L -> ( ∀ {x} -> (x∉L : x ∉ L) -> ((x , (τ , A)) ∷ Γ) ⊩ₗ Λ[ 0 >> fv {A} x ] t ∶ τ₃ ))
  ihᵣ = abs-inv Γ⊩lam-t₁

  Lₗ = proj₁ ihₗ
  Lᵣ = proj₁ ihᵣ
  cfₗ = proj₂ ihₗ
  cfᵣ = proj₂ ihᵣ
