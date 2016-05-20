module Core-Lemmas where

open import Data.Empty
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡

open import Core

lam-inj : {t u : PTerm} -> (PTerm.lam t) ≡ (PTerm.lam u) -> t ≡ u
lam-inj refl = refl

lam-inj2 : ∀ {t u} -> _≡_ {A = PTerm} (lam t) (lam u) -> t ≡ u
lam-inj2 = lam-inj

lam-eq : {t u : PTerm} -> t ≡ u -> (PTerm.lam t) ≡ (PTerm.lam u)
lam-eq refl = refl

app-inj-l : {t₁ t₂ u₁ u₂ : PTerm} -> (PTerm.app t₁ t₂) ≡ (PTerm.app u₁ u₂) -> t₁ ≡ u₁
app-inj-l refl = refl

app-inj-r : {t₁ t₂ u₁ u₂ : PTerm} -> (PTerm.app t₁ t₂) ≡ (PTerm.app u₁ u₂) -> t₂ ≡ u₂
app-inj-r refl = refl

app-eq : ∀ {t₁ t₂ u₁ u₂} -> t₁ ≡ u₁ -> t₂ ≡ u₂ -> (PTerm.app t₁ t₂) ≡ (PTerm.app u₁ u₂)
app-eq refl refl = refl


fv-subst-eq : ∀ x y t -> x ≡ y -> fv x [ y ::= t ] ≡ t
fv-subst-eq x _ t refl with x ≟ x
... | yes refl = refl
... | no p = ⊥-elim (p refl)

fv-subst-neq : ∀ x y t -> ¬(x ≡ y) -> fv x [ y ::= t ] ≡ fv x
fv-subst-neq x y t x≠y with y ≟ x
fv-subst-neq x .x t x≠y | yes refl = ⊥-elim (x≠y refl)
fv-subst-neq x y t x≠y | no p = refl

fv-x-eq-y : (x y : ℕ) -> x ∈ (y ∷ []) -> (x ≡ y)
fv-x-eq-y y .y (here refl) = refl
fv-x-eq-y x y (there ())

fv-x-neq-y : ∀ (x y : ℕ) {L} -> x ∉ (y ∷ L) -> ¬ (x ≡ y)
fv-x-neq-y x y x∉y∷L x≡y = x∉y∷L (here x≡y)

∈-cons-l : ∀ {A : Set} {x : A} {xs} ys -> x ∈ xs -> x ∈ (xs ++ ys)
∈-cons-l ys (here eq) = here eq
∈-cons-l ys (there x∈xs') = there (∈-cons-l ys x∈xs')

∉-cons-l : ∀ {A : Set} {x : A} xs ys -> x ∉ xs ++ ys -> x ∉ xs
∉-cons-l _ ys x∉xs++ys (here eq) = x∉xs++ys (here eq)
∉-cons-l .(x' ∷ xs') ys x∉xs++ys (there {x'} {xs'} x∈xs') = ∉-cons-l xs' ys (λ z → x∉xs++ys (there z)) x∈xs'

∉-cons-r : ∀ {A : Set} {x : A} xs ys -> x ∉ xs ++ ys -> x ∉ ys
∉-cons-r [] ys x∉xs++ys x∈ys = x∉xs++ys x∈ys
∉-cons-r (_ ∷ xs) ys x∉xs++ys x∈ys = ∉-cons-r xs ys (λ z → x∉xs++ys (there z)) x∈ys


subst-fresh : ∀ x t u -> (x∉FVt : x ∉ (FV t)) -> (t [ x ::= u ]) ≡ t
subst-fresh x (bv i) u x∉FVt = refl
subst-fresh x (fv y) u x∉FVt with x ≟ y
subst-fresh x (fv y) u x∉FVt | yes p = ⊥-elim (x∉FVt (here p))
subst-fresh x (fv y) u x∉FVt | no ¬p = refl
subst-fresh x (lam s) u x∉FVt rewrite subst-fresh x s u x∉FVt = refl
subst-fresh x (app t1 t2) u x∉FVt rewrite
  subst-fresh x t1 u (∉-cons-l (FV t1) (FV t2) x∉FVt) |
  subst-fresh x t2 u (∉-cons-r (FV t1) (FV t2) x∉FVt) = refl
subst-fresh x (Y t₁) u x∉FVt = refl

subst-fresh2 : ∀ x t u -> (x∉FVt : x ∉ (FV t)) -> t ≡ (t [ x ::= u ])
subst-fresh2 x t u x∉FVt rewrite subst-fresh x t u x∉FVt = refl


suc-inj : ∀ i j → suc i ≡ suc j → i ≡ j
suc-inj i ._ refl = refl

open-term-aux : ∀ j t i u e → ¬ (i ≡ j) -> [ j >> t ] e ≡ [ i >> u ] ([ j >> t ] e) ->
  e ≡ [ i >> u ] e
open-term-aux j t i u (bv k) i≠j eq with i ≟ k
open-term-aux j t i u (bv ._) i≠j eq | yes refl with j ≟ i
open-term-aux j t ._ u (bv ._) i≠j eq | yes refl | yes refl = ⊥-elim (i≠j refl)
open-term-aux j t i u (bv ._) i≠j eq | yes refl | no _ with i ≟ i
open-term-aux j t i u (bv ._) i≠j eq | yes refl | no _ | yes refl = eq
open-term-aux j t i u (bv ._) i≠j eq | yes refl | no _ | no i≠i = ⊥-elim (i≠i refl)
open-term-aux j t i u (bv k) i≠j eq | no _ = refl
open-term-aux j t i u (fv x) i≠j eq = refl
open-term-aux j t i u (lam e) i≠j eq
  with open-term-aux (suc j) t (suc i) u e
           (λ eq' -> i≠j (suc-inj i j eq')) (lam-inj eq)
... | eq'' = lam-eq eq''
open-term-aux j t i u (app e₁ e₂) i≠j eq
  with open-term-aux j t i u e₁ i≠j (app-inj-l eq)
     | open-term-aux j t i u e₂ i≠j (app-inj-r eq)
... | eq₁ | eq₂
  = app-eq eq₁ eq₂
open-term-aux j t i u (Y s) i≠j eq = refl



open-term : ∀ k t {e} → Term e → e ≡ [ k >> t ] e
open-term k t var = refl
open-term k t {lam e} (lam L cf) = body
  where
    y = ∃fresh L

    y∉ : y ∉ L
    y∉ = ∃fresh-spec L

    body : lam e ≡ [ k >> t ] (lam e)
    body with open-term (suc k) t {[ 0 >> fv y ] e} (cf y∉)
    ... | eq with open-term-aux 0 (fv y) (suc k) t e (λ ()) eq
    ...   | eq' = lam-eq eq'
open-term k t (app trm-u trm-v) with
  open-term k t trm-u | open-term k t trm-v
... | e1 | e2 = app-eq e1 e2
open-term k t₁ Y = refl


subst-open : ∀ x t k u e -> Term t ->
  ([ k >> u ] e) [ x ::= t ] ≡ [ k >> (u [ x ::= t ]) ] (e [ x ::= t ])
subst-open x t k u (bv i) trm-t with k ≟ i
... | yes _ = refl
... | no _ = refl
subst-open x t k u (fv y) trm-t with x ≟ y
... | yes _ = open-term k (u [ x ::= t ]) trm-t
... | no _ = refl
subst-open x t k u (lam e) trm-t rewrite
  subst-open x t (suc k) u e trm-t = refl
subst-open x t k u (app v w) trm-t rewrite
  subst-open x t k u v trm-t |
  subst-open x t k u w trm-t = refl
subst-open x t k u (Y t₁) trm-t = refl

subst-open2 : ∀ x t k u e -> Term t ->
  [ k >> (u [ x ::= t ]) ] (e [ x ::= t ]) ≡ ([ k >> u ] e) [ x ::= t ]
subst-open2 x t k u e trm-t rewrite subst-open x t k u e trm-t = refl

subst-open-var : ∀ x y u e -> ¬ (x ≡ y) -> Term u ->
  ((e [ y ::= u ]) ^' x) ≡ (e ^' x) [ y ::= u ]
subst-open-var x y u e x≠y lu
  with subst-open y u 0 (fv x) e lu
...  | eq with y ≟ x
subst-open-var x ._ u e x≠y lu | eq | yes refl = ⊥-elim (x≠y refl)
subst-open-var x y u e x≠y lu | eq | no _ = sym eq

subst-open-var2 : ∀ x y u e -> ¬ (x ≡ y) -> Term u ->
  (e ^' x) [ y ::= u ] ≡ ((e [ y ::= u ]) ^' x)
subst-open-var2 x y u e x≠y lu rewrite subst-open-var x y u e x≠y lu = refl


subst-intro : ∀ x t e -> x ∉ FV e -> Term t ->
  e ^ t ≡ (e ^' x) [ x ::= t ]
subst-intro x t e x∉ lt
  with subst-open x t 0 (fv x) e lt
... | eq with x ≟ x
...      | yes refl rewrite subst-fresh x e t x∉ = sym eq
...      | no x≠x = ⊥-elim (x≠x refl)


subst-intro2 : ∀ x t e -> x ∉ FV e -> Term t ->
  (e ^' x) [ x ::= t ] ≡ e ^ t
subst-intro2 x t e x∉ lt rewrite subst-intro x t e x∉ lt = refl
