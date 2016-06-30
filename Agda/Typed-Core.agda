module Typed-Core where

open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.List.Any as LAny
open LAny.Membership-≡
open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

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
Λ[ k >> u ] (bv i) with k ≟ i
Λ[_>>_] {τ} {τ'} k u (bv .k) | yes refl with τ ≟T τ'
Λ[ k >> u ] (bv .k) | yes refl | yes refl = u
Λ[ k >> u ] (bv .k) | yes refl | no _ = bv k
Λ[ k >> u ] (bv i) | no _ = bv i
-- Λ[ k >> u ] {τ} {τ'} (bv i) | yes _ | yes refl = u
-- Λ[ k >> u ] {τ} {τ'} (bv i) | yes _ | no _ = bv i
-- ... | no _  = bv i
Λ[ k >> u ] (fv x) = fv x
Λ[ k >> u ] (lam A t) = lam A (Λ[ (suc k) >> u ] t)
Λ[ k >> u ] (app t1 t2) = app (Λ[ k >> u ] t1) (Λ[ k >> u ] t2)
Λ[ k >> u ] (Y t) = Y t

_Λ[_::=_] : ∀ {τ τ'} -> Λ τ -> Atom -> Λ τ' -> Λ τ
bv i Λ[ x ::= u ] = bv i
fv y Λ[ x ::= u ] with x ≟ y
_Λ[_::=_] {τ} {τ'} (fv y) .y u | yes refl with τ ≟T τ'
fv y Λ[ .y ::= u ] | yes refl | yes refl = u
fv y Λ[ .y ::= u ] | yes refl | no _ = fv y
fv y Λ[ x ::= u ] | no _ = fv y
-- _Λ[_::=_] {τ} {τ'} (fv y) x u with x ≟ y | τ ≟T τ'

-- fv y Λ[ x ::= u ] | yes _ | yes refl = u
-- ... | yes _ | no _ = fv y
-- ... | no _ | _ = fv y
lam A t Λ[ x ::= u ] = lam A (t Λ[ x ::= u ])
app t1 t2 Λ[ x ::= u ] = app (t1 Λ[ x ::= u ]) (t2 Λ[ x ::= u ])
Y t₁ Λ[ x ::= u ] = Y t₁


ΛFV : ∀ {τ} -> Λ τ -> FVars
ΛFV (bv i) = []
ΛFV (fv x) = x ∷ []
ΛFV (lam A e) = ΛFV e
ΛFV (app e₁ e₂) = ΛFV e₁ ++ ΛFV e₂
ΛFV (Y t) = []


data ΛTerm : ∀ {τ} -> Λ τ -> Set where
  var : ∀ {A x} -> ΛTerm (fv {A} x)
  lam : ∀ {A B} (L : FVars) -> ∀ {e : Λ B} ->
    (cf : ∀ {x} -> (x∉L : x ∉ L) -> ΛTerm (Λ[ 0 >> fv {A} x ] e)) -> ΛTerm (lam A e)
  app : ∀ {A B} {e₁ : Λ (A ⟶ B)} {e₂ : Λ A} -> ΛTerm e₁ -> ΛTerm e₂ -> ΛTerm (app e₁ e₂)
  Y : ∀ {t} -> ΛTerm (Y t)


Λlam-inj : ∀ {A B : Type} {t u : Λ B} -> (Λ.lam A t) ≡ (Λ.lam A u) -> t ≡ u
Λlam-inj refl = refl


Λlam-eq : {A B : Type} {t u : Λ B} -> t ≡ u -> (Λ.lam A t) ≡ (Λ.lam A u)
Λlam-eq refl = refl


Λapp-inj-l : ∀ {A B : Type} {t₁ u₁ : Λ (A ⟶ B)} {t₂ u₂ : Λ A} -> (Λ.app t₁ t₂) ≡ (Λ.app u₁ u₂) -> t₁ ≡ u₁
Λapp-inj-l refl = refl


Λapp-inj-r : ∀ {A B : Type} {t₁ u₁ : Λ (A ⟶ B)} {t₂ u₂ : Λ A} -> (Λ.app t₁ t₂) ≡ (Λ.app u₁ u₂) -> t₂ ≡ u₂
Λapp-inj-r refl = refl


Λapp-eq : ∀ {A B : Type} {t₁ u₁ : Λ (A ⟶ B)} {t₂ u₂ : Λ A} -> t₁ ≡ u₁ -> t₂ ≡ u₂ -> (Λ.app t₁ t₂) ≡ (Λ.app u₁ u₂)
Λapp-eq refl refl = refl




^-ΛTerm-eq-aux : ∀ {τ τ' τ''} j (t : Λ τ') i (u : Λ τ'') (e : Λ τ) → ¬ (i ≡ j) -> Λ[ j >> t ] e ≡ Λ[ i >> u ] (Λ[ j >> t ] e) ->
  e ≡ Λ[ i >> u ] e
^-ΛTerm-eq-aux j t i u (bv k) i≠j eq with i ≟ k
^-ΛTerm-eq-aux j t i u (bv ._) i≠j eq | yes refl with j ≟ i
^-ΛTerm-eq-aux j t ._ u (bv ._) i≠j eq | yes refl | yes refl = ⊥-elim (i≠j refl)
^-ΛTerm-eq-aux j t i u (bv ._) i≠j eq | yes refl | no _ with i ≟ i
^-ΛTerm-eq-aux j t i u (bv ._) i≠j eq | yes refl | no _ | yes refl = eq
^-ΛTerm-eq-aux j t i u (bv ._) i≠j eq | yes refl | no _ | no i≠i = ⊥-elim (i≠i refl)
^-ΛTerm-eq-aux j t i u (bv k) i≠j eq | no _ = refl
^-ΛTerm-eq-aux j t i u (fv x) i≠j eq = refl
^-ΛTerm-eq-aux j t i u (lam A e) i≠j eq
  with ^-ΛTerm-eq-aux (suc j) t (suc i) u e
           (λ eq' -> i≠j (suc-inj i j eq')) (Λlam-inj eq)
... | eq'' = Λlam-eq eq''
^-ΛTerm-eq-aux j t i u (app e₁ e₂) i≠j eq
  with ^-ΛTerm-eq-aux j t i u e₁ i≠j (Λapp-inj-l eq)
     | ^-ΛTerm-eq-aux j t i u e₂ i≠j (Λapp-inj-r eq)
... | eq₁ | eq₂
  = Λapp-eq eq₁ eq₂
^-ΛTerm-eq-aux j t i u (Y s) i≠j eq = refl


^-ΛTerm-eq : ∀ {τ τ'} k (t : Λ τ') {e : Λ τ} → ΛTerm e → e ≡ Λ[ k >> t ] e
^-ΛTerm-eq k t var = refl
^-ΛTerm-eq k t {lam A e} (lam L cf) = body
  where
    y = ∃fresh L

    y∉ : y ∉ L
    y∉ = ∃fresh-spec L

    body : lam A e ≡ Λ[ k >> t ] (lam A e)
    body with ^-ΛTerm-eq (suc k) t {Λ[ 0 >> fv y ] e} (cf y∉)
    ... | eq with ^-ΛTerm-eq-aux 0 (fv y) (suc k) t e (λ ()) eq
    ...   | eq' = Λlam-eq eq'
^-ΛTerm-eq k t (app trm-u trm-v) with
  ^-ΛTerm-eq k t trm-u | ^-ΛTerm-eq k t trm-v
... | e1 | e2 = Λapp-eq e1 e2
^-ΛTerm-eq k t₁ Y = refl



Λsubst-open : ∀ {τ τ' τ''} x (t : Λ τ') k (u : Λ τ'') (e : Λ τ) -> ΛTerm t ->
  (Λ[ k >> u ] e) Λ[ x ::= t ] ≡ Λ[ k >> (u Λ[ x ::= t ]) ] (e Λ[ x ::= t ])

Λsubst-open x t k u (bv i) trm-t with k ≟ i
Λsubst-open {τ} {τ'} {τ''} x t k u (bv .k) trm-t | yes refl with τ ≟T τ''
Λsubst-open x t k u (bv .k) trm-t | yes refl | yes refl = refl
Λsubst-open x t k u (bv .k) trm-t | yes refl | no _ = refl
Λsubst-open x t k u (bv i) trm-t | no _ = refl

Λsubst-open x t k u (fv y) trm-t with x ≟ y
Λsubst-open {τ} {τ'} x t k u (fv .x) trm-t | yes refl with τ ≟T τ'
Λsubst-open x t k u (fv .x) trm-t | yes refl | yes refl = ^-ΛTerm-eq k (u Λ[ x ::= t ]) trm-t
Λsubst-open x t k u (fv .x) trm-t | yes refl | no _ = refl
Λsubst-open x t k u (fv y) trm-t | no _ = refl

Λsubst-open x t k u (lam A e) trm-t rewrite
  Λsubst-open x t (suc k) u e trm-t = refl
Λsubst-open x t k u (app v w) trm-t rewrite
  Λsubst-open x t k u v trm-t |
  Λsubst-open x t k u w trm-t = refl
Λsubst-open x t₁ k u (Y t) trm-t = refl


Λsubst-open-var : ∀ {τ τ' τ''} x y (u : Λ τ') (e : Λ τ) -> ¬ (x ≡ y) -> ΛTerm u ->
  (Λ[ 0 >> fv {τ''} x ] (e Λ[ y ::= u ])) ≡ (Λ[ 0 >> fv {τ''} x ] e) Λ[ y ::= u ]
Λsubst-open-var {τ'' = τ''} x y u e x≠y lu
  with Λsubst-open {τ'' = τ''} y u 0 (fv x) e lu
...  | eq with y ≟ x
Λsubst-open-var x ._ u e x≠y lu | eq | yes refl = ⊥-elim (x≠y refl)
Λsubst-open-var x y u e x≠y lu | eq | no _ = sym eq

Λsubst-open-var2 : ∀ {τ τ' τ''} x y (u : Λ τ') (e : Λ τ) -> ¬ (x ≡ y) -> ΛTerm u ->
  (Λ[ 0 >> fv {τ''} x ] e) Λ[ y ::= u ] ≡ (Λ[ 0 >> fv {τ''} x ] (e Λ[ y ::= u ]))
Λsubst-open-var2 {τ'' = τ''} x y u e x≠y lu rewrite Λsubst-open-var {τ'' = τ''} x y u e x≠y lu = refl


Λ^-^-swap : ∀ {τ τ' τ''} k n x y (m : Λ τ) -> ¬(k ≡ n) -> ¬(x ≡ y) -> Λ[ k >> fv {τ'} x ] (Λ[ n >> fv {τ''} y ] m) ≡ Λ[ n >> fv {τ''} y ] (Λ[ k >> fv {τ'} x ] m)
Λ^-^-swap k n x y (bv i) k≠n x≠y with n ≟ i
Λ^-^-swap {τ} {τ'} {τ''} k n x y (bv .n) k≠n x≠y | yes refl with τ ≟T τ''
Λ^-^-swap k n x y (bv .n) k≠n x≠y | yes refl | yes refl with k ≟ n
Λ^-^-swap n .n x y (bv .n) k≠n x≠y | yes refl | yes refl | yes refl = ⊥-elim (k≠n refl)
Λ^-^-swap k n x y (bv .n) k≠n x≠y | yes refl | yes refl | no _ with n ≟ n
Λ^-^-swap {τ} k n x y (bv .n) k≠n x≠y | yes refl | yes refl | no _ | yes refl with τ ≟T τ
Λ^-^-swap k n x y (bv .n) k≠n x≠y | yes refl | yes refl | no _ | yes refl | yes refl = refl
Λ^-^-swap k n x y (bv .n) k≠n x≠y | yes refl | yes refl | no _ | yes refl | no τ≠τ = ⊥-elim (τ≠τ refl)
Λ^-^-swap k n x y (bv .n) k≠n x≠y | yes refl | yes refl | no _ | no n≠n = ⊥-elim (n≠n refl)

Λ^-^-swap k n x y (bv .n) k≠n x≠y | yes refl | no τ≠τ'' with k ≟ n
Λ^-^-swap n .n x y (bv .n) k≠n x≠y | yes refl | no τ≠τ'' | yes refl = ⊥-elim (k≠n refl)
Λ^-^-swap k n x y (bv .n) k≠n x≠y | yes refl | no τ≠τ'' | no _ with n ≟ n
Λ^-^-swap {τ} {τ'} {τ''} k n x y (bv .n) k≠n x≠y | yes refl | no τ≠τ'' | no _ | yes refl with τ ≟T τ''
Λ^-^-swap k n x y (bv .n) k≠n x≠y | yes refl | no τ≠τ'' | no ¬p | yes refl | yes refl = ⊥-elim (τ≠τ'' refl)
Λ^-^-swap k n x y (bv .n) k≠n x≠y | yes refl | no τ≠τ'' | no ¬p₁ | yes refl | no _ = refl
Λ^-^-swap k n x y (bv .n) k≠n x≠y | yes refl | no τ≠τ'' | no _ | no n≠n = ⊥-elim (n≠n refl)

Λ^-^-swap k n x y (bv i) k≠n x≠y | no n≠i with k ≟ n
Λ^-^-swap n .n x y (bv i) k≠n x≠y | no n≠i | yes refl = ⊥-elim (k≠n refl)
Λ^-^-swap k n x y (bv i) k≠n x≠y | no n≠i | no _ with k ≟ i
Λ^-^-swap {τ} {τ'} k n x y (bv .k) k≠n x≠y | no n≠i | no _ | yes refl with τ ≟T τ'
Λ^-^-swap k n x y (bv .k) k≠n x≠y | no n≠i | no _ | yes refl | yes refl = refl
Λ^-^-swap k n x y (bv .k) k≠n x≠y | no n≠i | no _ | yes refl | no τ≠τ' with n ≟ k
Λ^-^-swap k .k x y (bv .k) k≠n x≠y | no n≠i | no _ | yes refl | no τ≠τ' | yes refl = ⊥-elim (k≠n refl)
Λ^-^-swap k n x y (bv .k) k≠n x≠y | no n≠i | no _ | yes refl | no τ≠τ' | no _ = refl
Λ^-^-swap k n x y (bv i) k≠n x≠y | no n≠i | no _ | no k≠i with n ≟ i
Λ^-^-swap k i x y (bv .i) k≠n x≠y | no n≠i | no _ | no k≠i | yes refl = ⊥-elim (n≠i refl)
Λ^-^-swap k n x y (bv i) k≠n x≠y | no n≠i | no _ | no k≠i | no _ = refl

Λ^-^-swap k n x y (fv z) k≠n x≠y = refl
Λ^-^-swap {_} {τ'} {τ''} k n x y (lam {B} A m) k≠n x≠y = cong (lam A) (Λ^-^-swap {B} {τ'} {τ''} (suc k) (suc n) x y m (λ sk≡sn → k≠n (≡-suc sk≡sn)) x≠y)
Λ^-^-swap {_} {τ'} {τ''} k n x y (app {τ₁} {τ₂} t1 t2) k≠n x≠y rewrite
  Λ^-^-swap {τ₁ ⟶ τ₂} {τ'} {τ''} k n x y t1 k≠n x≠y | Λ^-^-swap {τ₁} {τ'} {τ''} k n x y t2 k≠n x≠y = refl
Λ^-^-swap k n x y (Y _) k≠n x≠y = refl
