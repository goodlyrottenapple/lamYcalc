module Typed-Core where
open import Data.List
open import Data.Nat
open import Data.List.Any as LAny
open LAny.Membership-≡
open import Relation.Nullary
open import Relation.Binary.Core

open import Core
open import Core-Lemmas
open import Typing

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
