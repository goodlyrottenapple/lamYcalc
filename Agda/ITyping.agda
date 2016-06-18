module ITyping where

open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.List.Properties
open import Data.List.Any as LAny
open LAny.Membership-≡
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core


open import Core
open import Core-Lemmas
open import Typing
open import Reduction

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

-- list-inj-cons : ∀ {x y τᵢ τⱼ} -> (x ∷ τᵢ) ≡ (y ∷ τⱼ) -> τᵢ ≡ τⱼ
-- list-inj-cons refl = refl
--
-- list-inj : ∀ {x y τᵢ τⱼ} -> (x ∷ τᵢ) ≡ (y ∷ τⱼ) -> x ≡ y
-- ∩-inj refl = refl
--
-- list-∷-≡ : ∀ {x y : IType} {xs ys} -> x ≡ y -> xs ≡ ys -> (x ∷ xs) ≡ (y ∷ ys)
-- list-∷-≡ refl refl = refl


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
    τ₂₁ ⊆ₗ[ A ] τ₁₁ -> τ₁₂ ⊆ₗ[ B ] τ₂₂ -> (τ₁₁ ~> τ₁₂) ∷' (A ⟶ B) -> (τ₂₁ ~> τ₂₂) ∷' (A ⟶ B) ->
    -------------------------------------------------------------------------------------------
                            (τ₁₁ ~> τ₁₂) ⊆[ A ⟶ B ] (τ₂₁ ~> τ₂₂)
  -- ⊆-trans : ∀ {A τ₁ τ₂ τ₃} ->
  --   τ₁ ⊆[ A ] τ₂ -> τ₂ ⊆[ A ] τ₃ ->
  --   -------------------------------
  --             τ₁ ⊆[ A ] τ₃

data _⊆ₗ[_]_ where
  nil : ∀ {A τ} ->
    τ ∷'ₗ A ->
    -----------
    ω ⊆ₗ[ A ] τ
  cons : ∀ {A τᵢ τ' τ'ᵢ} ->
    ∃(λ τ -> (τ ∈ τᵢ) × (τ' ⊆[ A ] τ)) -> τ'ᵢ ⊆ₗ[ A ] τᵢ ->
    -------------------------------------------------------
                    (τ' ∷ τ'ᵢ) ⊆ₗ[ A ] τᵢ


∷'ₗ-∈ : ∀ {A τ τᵢ} -> τ ∈ τᵢ -> τᵢ ∷'ₗ A -> τ ∷' A
∷'ₗ-∈ {τᵢ = []} () _
∷'ₗ-∈ {τ = τ} {τ' ∷ τᵢ} τ∈τ'τᵢ τ'τᵢ∷A with τ' ≟TI τ
∷'ₗ-∈ {A} {τ} {.τ ∷ τᵢ} τ∈τ'τᵢ (cons τ∷A τ'τᵢ∷A) | yes refl = τ∷A
∷'ₗ-∈ {A} {τ} {τ' ∷ τᵢ} τ∈τ'τᵢ (cons τ'∷A τ'τᵢ∷A) | no τ'≠τ = ∷'ₗ-∈ (∈-∷-elim τ τᵢ τ'≠τ τ∈τ'τᵢ) τ'τᵢ∷A


⊆-refl : ∀ {A τ} -> τ ∷' A -> τ ⊆[ A ] τ
⊆ₗ-refl : ∀ {A τ} -> τ ∷'ₗ A -> τ ⊆ₗ[ A ] τ
⊆ₗ-⊆ : ∀ {A τᵢ τⱼ} -> τᵢ ⊆ τⱼ -> τⱼ ∷'ₗ A -> τᵢ ⊆ₗ[ A ] τⱼ

⊆-refl {τ = o} base = base
⊆-refl {τ = τ ~> τ'} (arr τ∷ᵢA τ'∷ᵢB) =
  arr (⊆ₗ-refl τ∷ᵢA) (⊆ₗ-refl τ'∷ᵢB) (arr τ∷ᵢA τ'∷ᵢB) (arr τ∷ᵢA τ'∷ᵢB)

⊆ₗ-refl {τ = []} nil = nil nil
⊆ₗ-refl {A} {τ ∷ τᵢ} ττᵢ∷A = ⊆ₗ-⊆ (λ {x} z → z) ττᵢ∷A

⊆ₗ-⊆ {τᵢ = []} τᵢ⊆τⱼ τⱼ∷A = nil τⱼ∷A
⊆ₗ-⊆ {τᵢ = τ ∷ τᵢ} τᵢ⊆τⱼ τⱼ∷A =
  cons (τ , (τᵢ⊆τⱼ (here refl)) , ⊆-refl (∷'ₗ-∈ (τᵢ⊆τⱼ (here refl)) τⱼ∷A)) (⊆ₗ-⊆ (λ {x} z → τᵢ⊆τⱼ (there z)) τⱼ∷A)


⊆ₗ-∈-∃ : ∀ {A τ τ₁ τ₂} -> τ₁ ⊆ₗ[ A ] τ₂ -> τ ∈ τ₁ -> ∃(λ τ' -> (τ' ∈ τ₂) × (τ ⊆[ A ] τ'))
⊆ₗ-∈-∃ (cons ∃τ τ₁⊆τ₂) (here refl) = ∃τ
⊆ₗ-∈-∃ (cons _ τ₁⊆τ₂) (there τ∈τ₁) = ⊆ₗ-∈-∃ τ₁⊆τ₂ τ∈τ₁


⊆ₗ-ω-⊥ : ∀ {A τ τᵢ} -> (τ ∷ τᵢ) ⊆ₗ[ A ] ω -> ⊥
⊆ₗ-ω-⊥ (cons (_ , () , _) _)

⊆-∷'-r : ∀ {A τ τ'} -> τ ⊆[ A ] τ' -> τ' ∷' A
⊆-∷'-r base = base
⊆-∷'-r (arr _ _ _ x) = x

⊆-∷'-l : ∀ {A τ τ'} -> τ ⊆[ A ] τ' -> τ ∷' A
⊆-∷'-l base = base
⊆-∷'-l (arr _ _ x _) = x

⊆ₗ-∷'ₗ-r : ∀ {A τᵢ τⱼ} -> τᵢ ⊆ₗ[ A ] τⱼ -> τⱼ ∷'ₗ A
⊆ₗ-∷'ₗ-r {τᵢ = []} (nil τⱼ∷A) = τⱼ∷A
⊆ₗ-∷'ₗ-r {τᵢ = τ ∷ τᵢ} (cons x τᵢ⊆τⱼ) = ⊆ₗ-∷'ₗ-r τᵢ⊆τⱼ

⊆ₗ-∷'ₗ-l : ∀ {A τᵢ τⱼ} -> τᵢ ⊆ₗ[ A ] τⱼ -> τᵢ ∷'ₗ A
⊆ₗ-∷'ₗ-l (nil x) = nil
⊆ₗ-∷'ₗ-l (cons (_ , _ , τ'⊆τ) τᵢ⊆τⱼ) = cons (⊆-∷'-l τ'⊆τ) (⊆ₗ-∷'ₗ-l τᵢ⊆τⱼ)


⊆ₗ-trans : ∀ {A τᵢ τⱼ τₖ} ->
  τᵢ ⊆ₗ[ A ] τⱼ -> τⱼ ⊆ₗ[ A ] τₖ ->
  ---------------------------------
            τᵢ ⊆ₗ[ A ] τₖ

⊆-trans : ∀ {A τ₁ τ₂ τ₃} ->
  τ₁ ⊆[ A ] τ₂ -> τ₂ ⊆[ A ] τ₃ ->
  -------------------------------
            τ₁ ⊆[ A ] τ₃

⊆ₗ-trans {τᵢ = []} τᵢ⊆τⱼ τⱼ⊆τₖ = nil (⊆ₗ-∷'ₗ-r τⱼ⊆τₖ)
⊆ₗ-trans {τᵢ = τ' ∷ τᵢ} τᵢ⊆τⱼ (nil x) = ⊥-elim (⊆ₗ-ω-⊥ τᵢ⊆τⱼ)
⊆ₗ-trans {τᵢ = τ ∷ τᵢ} {τⱼ} {τₖ} (cons (τ' , τ'∈τⱼ , τ⊆τ') τᵢ⊆τⱼ) τⱼ⊆τₖ =
  cons (τ'' , (τ''∈τₖ , (⊆-trans τ⊆τ' τ'⊆τ''))) (⊆ₗ-trans τᵢ⊆τⱼ τⱼ⊆τₖ)
    where
    τ'' = proj₁ (⊆ₗ-∈-∃ τⱼ⊆τₖ τ'∈τⱼ)
    τ''∈τₖ = proj₁ (proj₂ (⊆ₗ-∈-∃ τⱼ⊆τₖ τ'∈τⱼ))
    τ'⊆τ'' = proj₂ (proj₂ (⊆ₗ-∈-∃ τⱼ⊆τₖ τ'∈τⱼ))

⊆-trans base base = base
⊆-trans (arr τ₂₁⊆τ₁₁ τ₁₂⊆τ₂₂ τ₁₁~>τ₁₂∷A⟶B _) (arr τ₂₃⊆τ₂₁ τ₂₂⊆τ₂₄ τ₂₁~>τ₂₂∷A⟶B τ₂₃~>τ₂₄∷A⟶B) =
  arr (⊆ₗ-trans τ₂₃⊆τ₂₁ τ₂₁⊆τ₁₁) (⊆ₗ-trans τ₁₂⊆τ₂₂ τ₂₂⊆τ₂₄) τ₁₁~>τ₁₂∷A⟶B τ₂₃~>τ₂₄∷A⟶B



⊆->⊆ₗ : ∀ {A τ τ'} -> τ ⊆[ A ] τ' -> (∩' τ) ⊆ₗ[ A ] (∩' τ')
⊆->⊆ₗ {τ = τ} {τ'} τ⊆τ' = cons (τ' , (here refl , τ⊆τ')) (nil (cons (⊆-∷'-r τ⊆τ') nil))

data Λ : Type -> Set where
  bv : ∀ {A} -> (i : ℕ) -> Λ A
  fv : ∀ {A} -> (x : Atom) -> Λ A
  lam : ∀ {B} -> (A : Type) -> (e : Λ B) -> Λ (A ⟶ B)
  app : ∀ {A B} -> (e₁ : Λ (A ⟶ B)) -> (e₂ : Λ A) -> Λ B
  Y : (t : Type) -> Λ ((t ⟶ t) ⟶ t)


data _~_ : ∀{t} -> Λ t -> PTerm -> Set where
  bv : ∀ {t i} -> (bv {t} i) ~ (bv i)
  fv : ∀ {t x} -> (fv {t} x) ~ (fv x)
  lam : ∀ {t s m m'} -> m ~ m' -> (lam {s} t m) ~ (lam m')
  app : ∀ {t s m n m' n'} -> m ~ m' -> n ~ n' -> (app {t} {s} m n) ~ (app m' n')
  Y : ∀ {t} -> (Y t) ~ (Y t)


Λ[_<<_] : ∀ {t} -> ℕ -> Atom -> Λ t -> Λ t
Λ[ k << x ] (bv i) = bv i
Λ[ k << x ] (fv y) with x ≟ y
... | yes _ = bv k
... | no _ = fv y
Λ[ k << x ] (lam t m) = lam t (Λ[ (suc k) << x ] m)
Λ[ k << x ] (app t1 t2) = app (Λ[ k << x ] t1) (Λ[ k << x ] t2)
Λ[ k << x ] (Y t) = Y t



⊢->Λ : ∀ {Γ m t} -> Γ ⊢ m ∶ t -> Λ t
⊢->Λ {m = bv i} ()
⊢->Λ {m = fv x} {t} Γ⊢m∶t = fv {t} x
⊢->Λ {m = lam m} (abs {_} {τ₁} {τ₂} L cf) =
  lam τ₁ ( Λ[ 0 << ∃fresh (L ++ FV m) ] (⊢->Λ (cf (∉-cons-l _ _ (∃fresh-spec (L ++ FV m)) ))) )
⊢->Λ {m = app s t} (app Γ⊢s Γ⊢t) = app (⊢->Λ Γ⊢s) (⊢->Λ Γ⊢t)
⊢->Λ {m = Y τ} (Y _) = Y τ

-- ⊢->Λ≡ : ∀ {Γ m n t} -> m ≡ n -> {Γ⊢m : Γ ⊢ m ∶ t} -> {Γ⊢n : Γ ⊢ n ∶ t} -> (⊢->Λ Γ⊢m) ≡ (⊢->Λ Γ⊢m)
-- ⊢->Λ≡ refl = λ {Γ⊢m} {Γ⊢n} → refl


Λ*^-*^~ : ∀ {τ x k} t t' -> _~_ {τ} t t' -> Λ[ k << x ] t ~ ([ k << x ] t')
Λ*^-*^~ _ _ bv = bv
Λ*^-*^~ {x = x} (fv y) _ fv with x ≟ y
Λ*^-*^~ (fv x) .(fv x) fv | yes _ = bv
Λ*^-*^~ (fv y) .(fv y) fv | no _ = fv
Λ*^-*^~ _ _ (lam {m = m} {m'} t~t') = lam (Λ*^-*^~ m m' t~t')
Λ*^-*^~ _ _ (app {m = m} {n} {m'} {n'} t~t' t~t'') = app (Λ*^-*^~ m m' t~t') (Λ*^-*^~ n n' t~t'')
Λ*^-*^~ _ _ Y = Y


⊢->Λ~ : ∀ {Γ t τ} -> (Γ⊢t : Γ ⊢ t ∶ τ) -> (⊢->Λ Γ⊢t) ~ t
⊢->Λ~ {t = bv i} ()
⊢->Λ~ {t = fv x} (var _ _) = fv
⊢->Λ~ {t = lam t} (abs {τ₁ = τ₁} {τ₂} L cf) = lam ih
  where
  x = ∃fresh (L ++ FV t)
  x∉ = ∃fresh-spec (L ++ FV t)
  x∷Γ⊢t^'x = cf (∉-cons-l _ _ x∉)

  sub : ∀ {τ x m} -> x ∉ FV t -> _~_ {τ} m t ≡ m ~ (* x ^ (t ^' x))
  sub {_} {x} x∉ rewrite fv-^-*^-refl x t {0} x∉ = refl

  ih : Λ[ 0 << x ] (⊢->Λ x∷Γ⊢t^'x) ~ t
  ih rewrite sub {_} {x} {Λ[ 0 << x ] (⊢->Λ x∷Γ⊢t^'x)} (∉-cons-r L _ x∉) =
    Λ*^-*^~ (⊢->Λ x∷Γ⊢t^'x) (t ^' x) (⊢->Λ~ (cf (∉-cons-l _ _ x∉)))
⊢->Λ~ {t = app t t₁} (app Γ⊢t Γ⊢t₁) = app (⊢->Λ~ Γ⊢t) (⊢->Λ~ Γ⊢t₁)
⊢->Λ~ {t = Y t₁} (Y x) = Y



Λ[_>>_] : ∀ {τ τ'} -> ℕ -> Λ τ' -> Λ τ -> Λ τ
Λ[_>>_] {τ} {τ'} k u (bv i) with k ≟ i | τ ≟T τ'
Λ[ k >> u ] (bv i) | yes _ | yes refl = u
... | yes _ | no _ = bv i
... | no _ | _ = bv i
Λ[ k >> u ] (fv x) = fv x
Λ[ k >> u ] (lam A t) = lam A (Λ[ (suc k) >> u ] t)
Λ[ k >> u ] (app t1 t2) = app (Λ[ k >> u ] t1) (Λ[ k >> u ] t2)
Λ[ k >> u ] (Y t) = Y t


data _⊩_∶_ : ∀ {A} -> ICtxt -> Λ A -> IType -> Set
data _⊩ₗ_∶_ : ∀ {A} -> ICtxt -> Λ A -> List IType -> Set


data _⊩_∶_ where
  var : ∀ {A Γ x τ} {τᵢ : List IType} ->
    (wf-Γ : Wf-ICtxt Γ) -> (τᵢ∈Γ : (x , (τᵢ , A)) ∈ Γ) -> (τ⊆τᵢ : (∩' τ) ⊆ₗ[ A ] τᵢ) ->
    -----------------------------------------------------------------------------------
                                    Γ ⊩ fv {A} x ∶ τ
  app : ∀ {A B Γ s t τ τ₁ τ₂} ->
    Γ ⊩ s ∶ (τ₁ ~> τ₂) -> Γ ⊩ₗ t ∶ τ₁ -> (∩' τ) ⊆ₗ[ B ] τ₂ -> τ₁ ∷'ₗ A ->
    ---------------------------------------------------------------------
                        Γ ⊩ (app {A} {B} s t) ∶ τ
  abs : ∀ {A B Γ τ τ'} (L : FVars) -> ∀ {t : Λ B} ->
    ( cf : ∀ {x} -> (x∉L : x ∉ L) -> ((x , (τ , A)) ∷ Γ) ⊩ₗ Λ[ 0 >> fv {A} x ] t ∶ τ' ) -> (τ ~> τ') ∷' (A ⟶ B) ->
    --------------------------------------------------------------------------------------------------------------
                                                Γ ⊩ lam A t ∶ (τ ~> τ')
  Y : ∀ {Γ A τ τ₁ τ₂} ->
    (wf-Γ : Wf-ICtxt Γ) -> ∃(λ τ' -> (τ' ∈ τ₁) × ((τ ~> τ) ⊆[ A ⟶ A ] τ')) -> τ₁ ∷'ₗ (A ⟶ A) -> τ₂ ⊆ₗ[ A ] τ -> --  τ₁ ⊆[ (A ⟶ A) ⟶ A ]((∩' (τ ~> τ)) ~> τ)
    -----------------------------------------------------------------------------------------
                                    Γ ⊩ Y A ∶ (τ₁ ~> τ₂)

data _⊩ₗ_∶_ where
  nil : ∀ {A Γ} {m : Λ A} ->
    (wf-Γ : Wf-ICtxt Γ) ->
    ----------------------
          Γ ⊩ₗ m  ∶ ω
  cons : ∀ {A Γ τ τᵢ} {m : Λ A} ->
    Γ ⊩ m  ∶ τ -> Γ ⊩ₗ m  ∶ τᵢ ->
    --------------------------------
          Γ ⊩ₗ m  ∶ (τ ∷ τᵢ)


data ΛTerm : ∀ {τ} -> Λ τ -> Set where
  var : ∀ {A x} -> ΛTerm (fv {A} x)
  lam : ∀ {A B} (L : FVars) -> ∀ {e : Λ B} ->
    (cf : ∀ {x} -> (x∉L : x ∉ L) -> ΛTerm (Λ[ 0 >> fv {A} x ] e)) -> ΛTerm (lam A e)
  app : ∀ {A B} {e₁ : Λ (A ⟶ B)} {e₂ : Λ A} -> ΛTerm e₁ -> ΛTerm e₂ -> ΛTerm (app e₁ e₂)
  Y : ∀ {t} -> ΛTerm (Y t)



data _⊆Γ_ : ICtxt -> ICtxt -> Set where
  nil : ∀ {Γ} ->
    (wf-Γ : Wf-ICtxt Γ) ->
    ----------------------
          [] ⊆Γ Γ
  cons : ∀ {A x τ' Γ Γ'} ->
    ∃(λ τ -> ((x , (τ , A)) ∈ Γ') × (τ' ⊆ₗ[ A ] τ)) -> Γ ⊆Γ Γ' ->
    ------------------------------------------------------------
                      ((x , (τ' , A)) ∷ Γ) ⊆Γ Γ'


⊩ₗ-wf-Γ : ∀ {A Γ} {m : Λ A} {τ} -> Γ ⊩ₗ m ∶ τ -> Wf-ICtxt Γ
⊩ₗ-wf-Γ (nil wf-Γ) = wf-Γ
⊩ₗ-wf-Γ (cons _ Γ⊩ₗm∶τ) = ⊩ₗ-wf-Γ Γ⊩ₗm∶τ


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

-- ⊆Γ-refl {[]} _ = nil nil
-- ⊆Γ-refl {(x , τ , A) ∷ Γ} (cons _ τ∷A wf-Γ) = cons (τ , (here refl , ⊆ₗ-refl τ∷A)) {!   !}


⊩-∷' : ∀ {A Γ} {m : Λ A} {τ} -> Γ ⊩ m ∶ τ -> τ ∷' A
⊩ₗ-∷'ₗ : ∀ {A Γ} {m : Λ A} {τ} -> Γ ⊩ₗ m ∶ τ -> τ ∷'ₗ A

⊩-∷' (var _ _ τ⊆τᵢ) = ∷'ₗ-∈ (here refl) (⊆ₗ-∷'ₗ-l τ⊆τᵢ)
⊩-∷' (app _ _ τ⊆τᵢ _) = ∷'ₗ-∈ (here refl) (⊆ₗ-∷'ₗ-l τ⊆τᵢ)
⊩-∷' (abs _ _ x) = x
⊩-∷' (Y _ _ τ₁∷A⟶A τ₂⊆τ) = arr τ₁∷A⟶A (⊆ₗ-∷'ₗ-l τ₂⊆τ)

⊩ₗ-∷'ₗ (nil _) = nil
⊩ₗ-∷'ₗ (cons Γ⊩m∶τ Γ⊩ₗm∶τᵢ) = cons (⊩-∷' Γ⊩m∶τ) (⊩ₗ-∷'ₗ Γ⊩ₗm∶τᵢ)


⊩ₗ-∈-⊩ : ∀ {A Γ} {m : Λ A} {τ τᵢ} -> Γ ⊩ₗ m ∶ τᵢ -> τ ∈ τᵢ -> Γ ⊩ m ∶ τ
⊩ₗ-∈-⊩ (nil _) ()
⊩ₗ-∈-⊩ (cons Γ⊩m∶τ x) (here refl) = Γ⊩m∶τ
⊩ₗ-∈-⊩ (cons _ Γ⊩ₗm∶τᵢ) (there τ∈τᵢ) = ⊩ₗ-∈-⊩ Γ⊩ₗm∶τᵢ τ∈τᵢ


data _->Λβ_ : ∀ {τ} -> Λ τ ↝ Λ τ where
  redL : ∀ {A B} {n : Λ A} {m m' : Λ (A ⟶ B)} -> ΛTerm n -> m ->Λβ m' -> app m n ->Λβ app m' n
  redR : ∀ {A B} {m : Λ (A ⟶ B)} {n n' : Λ A} -> ΛTerm m -> n ->Λβ n' -> app m n ->Λβ app m n'
  abs : ∀ L {A B} {m m' : Λ B} -> ( ∀ {x} -> x ∉ L -> Λ[ 0 >> fv {A} x ] m ->Λβ Λ[ 0 >> fv {A} x ] m' ) ->
    lam A m ->Λβ lam A m'
  beta : ∀ {A B} {m : Λ (A ⟶ B)} {n : Λ A} -> ΛTerm (lam A m) -> ΛTerm n -> app (lam A m) n ->Λβ (Λ[ 0 >> n ] m)
  Y : ∀ {A} {m : Λ (A ⟶ A)} -> ΛTerm m -> app (Y A) m ->Λβ app m (app (Y A) m)


∈-⊆Γ-trans : ∀ {A x τᵢ} {Γ Γ'} -> (x , (τᵢ , A)) ∈ Γ -> Γ ⊆Γ Γ' -> ∃(λ τᵢ' -> ((x , (τᵢ' , A)) ∈ Γ') × τᵢ ⊆ₗ[ A ] τᵢ')
∈-⊆Γ-trans (here refl) (cons x _) = x
∈-⊆Γ-trans (there x∈L) (cons _ L⊆L') = ∈-⊆Γ-trans x∈L L⊆L'


⊆Γ-∷ : ∀ {A x τᵢ Γ Γ'} -> x ∉ dom Γ' -> τᵢ ∷'ₗ A -> Γ ⊆Γ Γ' -> Γ ⊆Γ ((x , τᵢ , A) ∷ Γ')
⊆Γ-∷ {Γ = []} x∉Γ' τᵢ∷A Γ⊆Γ' = nil (cons x∉Γ' τᵢ∷A (⊆Γ-wfΓ' Γ⊆Γ'))
⊆Γ-∷ {Γ = (x , τᵢ , A) ∷ Γ} x∉Γ' τᵢ∷A (cons (proj₁ , proj₂ , proj₃) Γ⊆Γ') =
  cons (proj₁ , ((there proj₂) , proj₃)) (⊆Γ-∷ x∉Γ' τᵢ∷A Γ⊆Γ')


subΓ : ∀ {A Γ Γ'} {m : Λ A} {τ} -> Γ ⊩ m ∶ τ -> Γ ⊆Γ Γ' -> Γ' ⊩ m ∶ τ
subᵢΓ : ∀ {A Γ Γ'} {m : Λ A} {τ} -> Γ ⊩ₗ m ∶ τ -> Γ ⊆Γ Γ' -> Γ' ⊩ₗ m ∶ τ

subΓ (var wf-Γ τᵢ∈Γ τ⊆τᵢ) Γ⊆Γ' = var (⊆Γ-wfΓ' Γ⊆Γ') τᵢ'∈ (⊆ₗ-trans τ⊆τᵢ τᵢ⊆τᵢ')
  where
  τᵢ'∈ = proj₁ (proj₂ (∈-⊆Γ-trans τᵢ∈Γ Γ⊆Γ'))
  τᵢ⊆τᵢ' = proj₂ (proj₂ (∈-⊆Γ-trans τᵢ∈Γ Γ⊆Γ'))

subΓ (app Γ⊩m∶τ x x₁ x₂) Γ⊆Γ' = app (subΓ Γ⊩m∶τ Γ⊆Γ') (subᵢΓ x Γ⊆Γ') x₁ x₂
subΓ {Γ' = Γ'} (abs {τ = τ} L cf (arr τ∷A τ'∷B)) Γ⊆Γ' = abs
  (L ++ dom Γ')
  (λ x∉ → subᵢΓ
    (cf (∉-cons-l _ _ x∉))
    (cons
      (τ , (here refl) , (⊆ₗ-refl τ∷A))
      (⊆Γ-∷ (∉-cons-r L _ x∉) τ∷A Γ⊆Γ')))
  (arr τ∷A τ'∷B)
subΓ (Y x x₁ x₂ x₃) Γ⊆Γ' = Y (⊆Γ-wfΓ' Γ⊆Γ') x₁ x₂ x₃

subᵢΓ (nil wf-Γ) Γ⊆Γ' = nil (⊆Γ-wfΓ' Γ⊆Γ')
subᵢΓ (cons x Γ⊩ₗm∶τ) Γ⊆Γ' = cons (subΓ x Γ⊆Γ') (subᵢΓ Γ⊩ₗm∶τ Γ⊆Γ')


∈-⊆ₗ-trans : ∀ {A τ τᵢ τⱼ} -> τ ∈ τᵢ -> τᵢ ⊆ₗ[ A ] τⱼ -> ∃(λ τ' -> (τ' ∈ τⱼ) × τ ⊆[ A ] τ')
∈-⊆ₗ-trans (here refl) (cons x _) = x
∈-⊆ₗ-trans (there τ∈τᵢ) (cons _ τᵢ⊆τⱼ) = ∈-⊆ₗ-trans τ∈τᵢ τᵢ⊆τⱼ


sub : ∀ {A Γ Γ'} {m : Λ A} {τ τ'} -> Γ ⊩ m ∶ τ -> τ' ⊆[ A ] τ -> Γ ⊆Γ Γ' -> Γ' ⊩ m ∶ τ'
subᵢ : ∀ {A Γ Γ'} {m : Λ A} {τ τ'} -> Γ ⊩ₗ m ∶ τ -> τ' ⊆ₗ[ A ] τ -> Γ ⊆Γ Γ' -> Γ' ⊩ₗ m ∶ τ'

sub (var wf-Γ τᵢ∈Γ τ⊆τᵢ) τ'⊆τ Γ⊆Γ' =
  var (⊆Γ-wfΓ' Γ⊆Γ') τᵢ'∈ (⊆ₗ-trans (⊆ₗ-trans (⊆->⊆ₗ τ'⊆τ) τ⊆τᵢ) τᵢ⊆τᵢ')
  where
  τᵢ'∈ = proj₁ (proj₂ (∈-⊆Γ-trans τᵢ∈Γ Γ⊆Γ'))
  τᵢ⊆τᵢ' = proj₂ (proj₂ (∈-⊆Γ-trans τᵢ∈Γ Γ⊆Γ'))

sub (app Γ⊩s∶τ₁~>τ₂ Γ⊩ₗt∶τ₁ τ⊆τ₂ τ∷A) τ'⊆τ Γ⊆Γ' = app
  (subΓ Γ⊩s∶τ₁~>τ₂ Γ⊆Γ')
  (subᵢΓ Γ⊩ₗt∶τ₁ Γ⊆Γ')
  (⊆ₗ-trans (⊆->⊆ₗ τ'⊆τ) τ⊆τ₂)
  τ∷A
sub {_} {Γ} {Γ'} (abs {τ = τ} {τ'} L {t} cf τ~>τ'∷A⟶B) (arr {A} {τ₁₁ = τ₁₁} τ⊆τ₁₁ τ₁₂⊆τ' (arr τ₁₁∷A τ₁₂∷B) x₃) Γ⊆Γ' = abs
  (L ++ dom Γ')
  (λ x∉ → subᵢ
    (cf (∉-cons-l _ _ x∉))
    τ₁₂⊆τ'
    (cons (τ₁₁ , (here refl) , τ⊆τ₁₁) (⊆Γ-∷ (∉-cons-r L _ x∉) τ₁₁∷A Γ⊆Γ')))
  (arr τ₁₁∷A τ₁₂∷B)
sub (Y wf-Γ (τ' , τ'∈τ₁ , τ~>τ⊆τ') τ₁∷A⟶A τ₂⊆τ) (arr {τ₁₁ = τ₁'} τ₁⊆τ₁' τ₂'⊆τ₂ (arr ∩τ₁'∷A⟶A τ₂'∷A) x₄) Γ⊆Γ' =
  Y ((⊆Γ-wfΓ' Γ⊆Γ')) (τ'' , (τ''∈τ₁' , ⊆-trans τ~>τ⊆τ' τ'⊆τ'')) ∩τ₁'∷A⟶A (⊆ₗ-trans τ₂'⊆τ₂ τ₂⊆τ)
  where
  τ'' = proj₁ (∈-⊆ₗ-trans τ'∈τ₁ τ₁⊆τ₁')
  τ''∈τ₁' = proj₁ (proj₂ (∈-⊆ₗ-trans τ'∈τ₁ τ₁⊆τ₁'))
  τ'⊆τ'' = proj₂ (proj₂ (∈-⊆ₗ-trans τ'∈τ₁ τ₁⊆τ₁'))

subᵢ Γ⊩ₗm∶τ (nil x) Γ⊆Γ' = nil (⊆Γ-wfΓ' Γ⊆Γ')
subᵢ Γ⊩ₗm∶τᵢ (cons (τ , τ∈τᵢ , τ'⊆τ) τ'ᵢ⊆τᵢ) Γ⊆Γ' with ⊩ₗ-∈-⊩ Γ⊩ₗm∶τᵢ τ∈τᵢ
... | Γ⊩m∶τ = cons (sub Γ⊩m∶τ τ'⊆τ Γ⊆Γ') (subᵢ Γ⊩ₗm∶τᵢ τ'ᵢ⊆τᵢ Γ⊆Γ')






~>∩ : ∀ {X A B C} -> (A ~> B) ∷' X -> (A ~> C) ∷' X ->
  ∩' (A ~> (B ++ C)) ⊆ₗ[ X ] ((A ~> B) ∷ (A ~> C) ∷ [])
~>∩ A~>B∷X A~>C∷X = cons ({!   !} , ({!   !} , {!   !})) (nil (cons A~>B∷X (cons A~>C∷X nil)))


Γ⊩Ym-max : ∀ {A Γ} {m : Λ (A ⟶ A)} {τ} -> Γ ⊩ app (Y A) m ∶ τ -> ∃(λ τ' -> Γ ⊩ m ∶ (τ' ~> τ') × (∩' τ) ⊆ₗ[ A ] τ')
Γ⊩Ym-max {A} {Γ} {m} {τ} (app {τ₁ = τ₁ᵢ~>τ₂ᵢ} {τ'}
  (Y {τ = τ''} wf-Γ (_ , τ₁~>τ₂∈τ₁ᵢ~>τ₂ᵢ , arr {τ₂₁ = τ₁} {τ₂} τ₁⊆τ'' τ''⊆τ₂ τ''~>τ''∷A⟶A (arr τ₁∷A τ₂∷A)) τ₁ᵢ~>τ₂ᵢ∷A⟶A τ'⊆τ'')
  Γ⊩ₗm∶τ₁ᵢ~>τ₂ᵢ
  τ⊆τ' τ₁ᵢ~>τ₂ᵢ∷A⟶A₂) =
  τ₂ , Γ⊩m∶τ₂~>τ₂ , τ⊆τ₂

  where
  Γ⊆Γ-refl = ⊆Γ-⊆ wf-Γ (λ {x} z → z)
  τ⊆τ'' = ⊆ₗ-trans τ⊆τ' τ'⊆τ''
  τ⊆τ₂ = ⊆ₗ-trans τ⊆τ'' τ''⊆τ₂

  Γ⊩m∶τ₁~>τ₂ : Γ ⊩ m ∶ (τ₁ ~> τ₂)
  Γ⊩m∶τ₁~>τ₂ = ⊩ₗ-∈-⊩ Γ⊩ₗm∶τ₁ᵢ~>τ₂ᵢ τ₁~>τ₂∈τ₁ᵢ~>τ₂ᵢ

  Γ⊩m∶τ₂~>τ₂ : Γ ⊩ m ∶ (τ₂ ~> τ₂)
  Γ⊩m∶τ₂~>τ₂ = sub Γ⊩m∶τ₁~>τ₂ (arr (⊆ₗ-trans τ₁⊆τ'' τ''⊆τ₂) (⊆ₗ-refl τ₂∷A) (arr τ₂∷A τ₂∷A) (arr τ₁∷A τ₂∷A)) Γ⊆Γ-refl



Γ⊩ₗYm-max : ∀ {A Γ} {m : Λ (A ⟶ A)} {τ} -> ¬(τ ≡ ω) -> Γ ⊩ₗ app (Y A) m ∶ τ -> ∃(λ τ' -> Γ ⊩ m ∶ (τ' ~> τ') × τ ⊆ₗ[ A ] τ')
Γ⊩ₗYm-max τ≠ω (nil wf-Γ) = ⊥-elim (τ≠ω refl)
Γ⊩ₗYm-max τ≠ω (cons x (nil wf-Γ)) = Γ⊩Ym-max x
Γ⊩ₗYm-max {A} {Γ} {m} τ≠ω (cons {τ = τ} x (cons {τ = τ₂} {τᵢ} x₁ Γ⊩ₗYm∶τ)) =
  {!   !}
  where
  ih : ∃(λ τ' -> Γ ⊩ m ∶ (τ' ~> τ') × (τ₂ ∷ τᵢ) ⊆ₗ[ A ] τ')
  ih = Γ⊩ₗYm-max {!   !} (cons {τ = τ₂} {τᵢ} x₁ Γ⊩ₗYm∶τ)

  τᵢ' = proj₁ ih
  Γ⊩m∶τᵢ'~>τᵢ' = proj₁ (proj₂ ih)
  τ₂τᵢ⊆τᵢ' = proj₂ (proj₂ ih)

  τ' = proj₁ (Γ⊩Ym-max x)
  Γ⊩m∶τ'~>τ' = proj₁ (proj₂ (Γ⊩Ym-max x))
  τ⊆τ' = proj₂ (proj₂ (Γ⊩Ym-max x))



⊩->β : ∀ {A Γ} {m m' : Λ A} {τ} -> Γ ⊩ m' ∶ τ -> m ->Λβ m' -> Γ ⊩ m ∶ τ
⊩->β Γ⊩m'∶τ (redL x m->βm') = {!   !}
⊩->β Γ⊩m'∶τ (redR x m->βm') = {!   !}
⊩->β Γ⊩m'∶τ (abs L x) = {!   !}
⊩->β Γ⊩m'∶τ (beta x x₁) = {!   !}
⊩->β {τ = τ} (app Γ⊩m∶[]~>τᵢ (nil wf-Γ) τ⊆τᵢ []∷A) (Y _) = app
  (Y {τ = ∩' τ} {(ω ~> ∩' τ) ∷ []} {∩' τ}
    wf-Γ
    ((ω ~> ∩' τ) , here refl , arr (nil τ∷A) (⊆ₗ-refl τ∷A) (arr τ∷A τ∷A) (arr nil τ∷A))
    (cons (arr []∷A τ∷A) nil)
    (⊆ₗ-refl τ∷A))
  (cons (sub Γ⊩m∶[]~>τᵢ (arr (nil []∷A) τ⊆τᵢ (arr []∷A τ∷A) (arr []∷A (⊆ₗ-∷'ₗ-r τ⊆τᵢ))) (⊆Γ-⊆ wf-Γ (λ {x} z → z))) (nil wf-Γ))
  (⊆ₗ-refl τ∷A)
  (cons (arr []∷A τ∷A) nil)

  where
  τ∷A = ⊆ₗ-∷'ₗ-l τ⊆τᵢ

⊩->β {A} {Γ} {τ = τ} (app {s = m} {τ₁ = τ' ∷ τ'ᵢ} {τᵢ} Γ⊩m∶τ'~>τᵢ Γ⊩ₗYm∶τ' τ⊆τᵢ τ'∷A) (Y _) = {!   !}
  where
  Γ⊆Γ-refl = ⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗYm∶τ') (λ {x} z → z)

  τ'' = proj₁ (Γ⊩ₗYm-max (λ x → {!   !}) Γ⊩ₗYm∶τ')

  Γ⊩m∶τ''~>τ'' : Γ ⊩ m ∶ (τ'' ~> τ'')
  Γ⊩m∶τ''~>τ'' = proj₁ (proj₂ (Γ⊩ₗYm-max {!   !} Γ⊩ₗYm∶τ'))

  τ'τ'ᵢ⊆τ'' : (τ' ∷ τ'ᵢ) ⊆ₗ[ A ] τ''
  τ'τ'ᵢ⊆τ'' = proj₂ (proj₂ (Γ⊩ₗYm-max {!   !} Γ⊩ₗYm∶τ'))

  Γ⊩m∶τ''~>τᵢ : Γ ⊩ m ∶ (τ'' ~> ∩' τ)
  Γ⊩m∶τ''~>τᵢ = sub Γ⊩m∶τ'~>τᵢ (arr τ'τ'ᵢ⊆τ'' τ⊆τᵢ (arr (⊆ₗ-∷'ₗ-r τ'τ'ᵢ⊆τ'') (⊆ₗ-∷'ₗ-l τ⊆τᵢ)) (arr τ'∷A (⊆ₗ-∷'ₗ-r τ⊆τᵢ))) Γ⊆Γ-refl

-- ⊩->β {τ = τ} (app Γ⊩m∶[]~>τᵢ (nil wf-Γ) τ⊆τᵢ []∷A) (Y _) = app
--   (Y {τ = ∩' τ} {(ω ~> ∩' τ) ∷ []} {∩' τ}
--     wf-Γ
--     ((ω ~> ∩' τ) , here refl , arr (nil τ∷A) (⊆ₗ-refl τ∷A) (arr τ∷A τ∷A) (arr nil τ∷A))
--     (cons (arr []∷A τ∷A) nil)
--     (⊆ₗ-refl τ∷A))
--   (cons (sub Γ⊩m∶[]~>τᵢ (arr (nil []∷A) τ⊆τᵢ (arr []∷A τ∷A) (arr []∷A (⊆ₗ-∷'ₗ-r τ⊆τᵢ))) (⊆Γ-⊆ wf-Γ (λ {x} z → z))) (nil wf-Γ))
--   (⊆ₗ-refl τ∷A)
--   (cons (arr []∷A τ∷A) nil)
--
--
-- -- ⊩->β (app {τ₁ = ∩ (τ₁ ∷ τ₁ᵢ)} Γ⊩m∶τ₁ᵢ~>τ₂ (cons (app (Y wf-Γ (proj₁ , () , proj₃) x₁ x₂) (nil wf-Γ₁) τ₁⊆τ₁₂ x₅) Γ⊩Ym∶τ₁ᵢ) τ⊆τ₂ τ₁∷A) (Y x)
-- -- ⊩->β {τ = τ} (app {τ₁ = ∩ (τ₁ ∷ τ₁ᵢ)} {τ₂} Γ⊩m∶τ₁ᵢ~>τ₂ (cons (app {τ₁ = ∩ (τ₁₁ ∷ τ₁₁ᵢ)} {τ₁₂} (Y {τ = τ'} wf-Γ (τ'' , τ''∈ τ₁₁, proj₃) x₁ x₂) (cons Γ⊩m∶τ₁₁ Γ⊩ₗm∶τ₁₁ᵢ) τ₁⊆τ₁₂ x₅) Γ⊩Ym∶τ₁ᵢ) τ⊆τ₂ τ₁∷A) (Y _) =
-- ⊩->β {A} {Γ} {τ = τ} (app {s = m} {τ₁ = ∩ (τ₁ ∷ τ₁ᵢ)} {τ₂}
--   Γ⊩m∶τ₁ᵢτ₁ᵢ~>τ₂
--   (cons
--     (app {τ₁ = ∩ (τ₁₁)} {τ₁₂}
--       (Y {τ = τ'} wf-Γ (_ , τ''∈τ₁₁ , arr {τ₂₁ = τ''₁} {τ''₂} τ''₁⊆τ' τ'⊆τ''₂ τ'~>τ'∷A⟶A (arr τ''₁∷A τ''₂∷A)) τ₁₁∷A⟶A τ₁₂⊆τ')
--       Γ⊩ₗm∶τ₁₁ τ₁⊆τ₁₂ τ₁₁∷A⟶A₂)
--     Γ⊩Ym∶τ₁ᵢ)
--   τ⊆τ₂
--   τ₁∷A) (Y _) =
--   {!   !}
--
--   where
--   Γ⊆Γ-refl = ⊆Γ-⊆ wf-Γ (λ {x} z → z)
--
--   Γ⊩m∶τ''₁~>τ''₂ : Γ ⊩ m ∶ (τ''₁ ~> τ''₂)
--   Γ⊩m∶τ''₁~>τ''₂ = ⊩ₗ-∈-⊩ Γ⊩ₗm∶τ₁₁ τ''∈τ₁₁
--
--   Γ⊩m∶τ''₂~>τ''₂ : Γ ⊩ m ∶ (τ''₂ ~> τ''₂)
--   Γ⊩m∶τ''₂~>τ''₂ = sub Γ⊩m∶τ''₁~>τ''₂ (arr (⊆ₗ-trans τ''₁⊆τ' τ'⊆τ''₂) (⊆ₗ-refl τ''₂∷A) (arr τ''₂∷A τ''₂∷A) (arr τ''₁∷A τ''₂∷A)) Γ⊆Γ-refl
--
--   Γ⊩m∶τ₁~>τ₂ : Γ ⊩ m ∶ (∩' τ₁ ~> τ₂)
--   Γ⊩m∶τ₁~>τ₂ = sub Γ⊩m∶τ₁ᵢτ₁ᵢ~>τ₂ (arr {!   !} {!   !} {!   !} {!   !}) Γ⊆Γ-refl












-- ⊩->β Γ⊩m'∶τ (redL x m->βm') = {!   !}
-- ⊩->β Γ⊩m'∶τ (redR x m->βm') = {!   !}
-- ⊩->β Γ⊩m'∶τ (abs L x) = {!   !}
-- ⊩->β Γ⊩m'∶τ (beta x x₁) = {!   !}
-- ⊩->β (app Γ⊩m'∶ω~>τ₂ (nil wf-Γ) τ⊆τ₂ nil) (Y trm-m) = {!   !}
-- ⊩->β (app Γ⊩m∶τ₃τᵢ~>τ₅ (cons _ (app (Y _ τ₂⊆τ₁ τ₁⊆τ) (cons _ Γ⊩m∶τ~>τ₁ (nil wf-Γ)) τ₃⊆τ₂ (cons τ~>τ₁∷A⟶A _)) Γ⊩ₗYm∶∩τᵢ) τ₄⊆τ₅ τ₃τᵢ∷A) (Y trm-m) = {!   !}













-- ⊩->β Γ⊩m'∶τ (redL x m->βm') = {!   !}
-- ⊩->β Γ⊩m'∶τ (redR x m->βm') = {!   !}
-- ⊩->β Γ⊩m'∶τ (abs L x) = {!   !}
-- ⊩->β Γ⊩m'∶τ (beta x x₁) = {!   !}
-- -- ⊩->β (app Γ⊩m∶τ₁~>τ (app (Y wf-Γ (arr (arr ::' ::'') ::''') τ≤τ₁ τ₂≤τ₁) Γ⊩m'∶τ₂ x₄) x₅) (Y x₆) = {!   !}
-- ⊩->β (app {s = m} {τ₂ = τ} Γ⊩m∶τ₁~>τ (app {τ₂ = τ₁} (Y {τ = τ₂} {τ₃} wf-Γ (arr (arr τ₂∷A τ₃∷A) _) τ≤τ₁ τ₂≤τ₁) Γ⊩m∶τ₂~>τ₃ _) (arr {A = A} τ₁∷A τ∷A)) (Y x₆) =
--   app {A = A ⟶ A}
--     (Y {_} {A} {∩ (τ₂ ∷ τ₁ ∷ [])} {∩ (τ₃ ∷ τ ∷ [])} {τ}
--       wf-Γ
--       (arr (arr (∩-cons τ₂∷A (∩-cons τ₁∷A ∩-nil)) (∩-cons τ₃∷A (∩-cons τ∷A ∩-nil))) τ∷A)
--       {!   !}
--       (∩-∈ (there (here refl))))
--     {!   !}
--     (arr (arr (∩-cons τ₂∷A (∩-cons τ₁∷A ∩-nil)) (∩-cons τ₃∷A (∩-cons τ∷A ∩-nil))) τ∷A)
--
-- ⊩->β (app Γ⊩m'∶τ (∩-nil ¬Y-shape wf-Γ) x) (Y x₁) = ⊥-elim (¬Y-shape intro₁)
-- ⊩->β (app Γ⊩m'∶τ (∩-cons ¬Y-shape wf-Γ Γ⊩m'∶τ₁ Γ⊩m'∶τ₂) x) (Y x₁) = ⊥-elim (¬Y-shape intro₁)
-- ⊩->β (∩-nil ¬Y-shape wf-Γ) (Y x) = ⊥-elim (¬Y-shape intro₂)
-- ⊩->β (∩-cons ¬Y-shape wf-Γ Γ⊩m'∶τ Γ⊩m'∶τ₁) (Y x) = ⊥-elim (¬Y-shape intro₂)

-- ⊩->β Γ⊩m'∶τ (redL trm-n m->βm') = ⊩->β-redL Γ⊩m'∶τ m->βm'
--   where
--   ⊩->β-redL : ∀ {A B Γ} {m m' : Λ (A ⟶ B)} {n : Λ A} {τ} -> Γ ⊩ app m' n ∶ τ -> m ->Λβ m' -> Γ ⊩ app m n ∶ τ
--   ⊩->β-redL (app Γ⊩m'n∶τ Γ⊩m'n∶τ₁ x x₁) (redL x₂ m->Λβm') =
--     app (⊩->β-redL Γ⊩m'n∶τ m->Λβm') Γ⊩m'n∶τ₁ x x₁
--   ⊩->β-redL (∩-nil ¬Y-shape wf-Γ) (redL x m->Λβm') = {!   !}
--   ⊩->β-redL (∩-cons ¬Y-shape wf-Γ Γ⊩m'n∶τ Γ⊩m'n∶τ₁) (redL x m->Λβm') = {!   !}
--   ⊩->β-redL Γ⊩m'n∶τ (redR x m->Λβm') = {!   !}
--   ⊩->β-redL Γ⊩m'n∶τ (abs L x) = {!   !}
--   ⊩->β-redL Γ⊩m'n∶τ (beta x x₁) = {!   !}
--   ⊩->β-redL Γ⊩m'n∶τ (Y x) = {!   !}
-- ⊩->β Γ⊩m'∶τ (redR trm-m n->βn') = {!   !}
-- ⊩->β Γ⊩m'∶τ (abs L x) = {!   !}
-- ⊩->β Γ⊩m'∶τ (beta x x₁) = {!   !}
-- ⊩->β (app {s = m} {τ₂ = τ} Γ⊩m∶τ₁~>τ (app (Y {_} {_} {τ₂} {τ₃} {τ₁} wf-Γ τ₂∷A τ₃∷A τ₁∷A τ₂≤∩τ₃ τ₁≤∩τ₃) Γ⊩m∶τ₂~>τ₃ x τ₂~>τ₃∷A) (arr {A = A} _ τ∷A) _) (Y trm-m) =
--   -- app {A = A ⟶ A} (Y wf-Γ τ₁∷A τ∷A τ∷A {!   !} {!   !}) Γ⊩m∶τ₁~>τ (arr (arr τ₁∷A τ∷A) τ∷A) (arr τ₁∷A τ∷A)
--   app {A = A ⟶ A}
--     (Y {_} {A} {∩ (τ₁ ∷ τ₂ ∷ τ₃ ∷ [])} {∩ (τ ∷ τ₃ ∷ [])} {τ}
--       wf-Γ
--       {!   !}
--       (∩-cons τ∷A (∩-cons τ₃∷A ∩-nil))
--       τ∷A
--       {!   !}
--       {!   !})
--     {!   !}
--     (arr {!   !} {!   !})
--     {!   !}
--
-- ⊩->β (app Γ⊩m∶τ~>τ' (∩-nil ¬Y-shape wf-Γ) x τ∷A) (Y trm-m) = ⊥-elim (¬Y-shape intro₁)
-- ⊩->β (app Γ⊩m∶τ~>τ' (∩-cons ¬Y-shape wf-Γ Γ⊩Ym∶τ' Γ⊩Ym∶τ'') x τ∷A) (Y trm-m) = ⊥-elim (¬Y-shape intro₁)
-- ⊩->β (∩-nil ¬Y-shape wf-Γ) (Y x) = ⊥-elim (¬Y-shape intro₂)
-- ⊩->β (∩-cons ¬Y-shape wf-Γ Γ⊩m'∶τ Γ⊩m'∶τ₁) (Y x) = ⊥-elim (¬Y-shape intro₂)
