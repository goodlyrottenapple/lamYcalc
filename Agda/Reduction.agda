module Reduction where

open import Data.Empty
open import Data.Nat
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Core
open import Core-Lemmas

_↝_ : Set -> Set -> Set₁
A ↝ B = A -> B -> Set

data _->β_ : PTerm ↝ PTerm where
  redL : ∀ {n m m'} -> Term n → m ->β m' -> app m n ->β app m' n
  redR : ∀ {m n n'} -> Term m → n ->β n' -> app m n ->β app m n'
  abs : ∀ L {m m'} -> ( ∀ {x} -> x ∉ L -> (m ^' x) ->β (m' ^' x) ) ->
    lam m ->β lam m'
  beta : ∀ {m n} -> Term (lam m) -> Term n -> app (lam m) n ->β (m ^ n)
  Y : ∀ {m σ} -> Term m -> app (Y σ) m ->β app m (app (Y σ) m)

test : ∀ {x} -> lam (app (lam (bv 0)) (fv x)) ->β lam (fv x)
test = abs [] (λ _ -> beta (lam [] (λ x∉L -> var)) var)


data _->||_ : PTerm ↝ PTerm where
  refl : ∀ {x} -> fv x ->|| fv x
  reflY : ∀ {σ} -> Y σ ->|| Y σ
  app : ∀ {m m' n n'} -> m ->|| m' -> n ->|| n' -> app m n ->|| app m' n'
  abs : ∀ L {m m'} -> ( ∀ {x} -> x ∉ L -> (m ^' x) ->|| (m' ^' x) ) ->
    lam m ->|| lam m'
  beta : ∀ L {m m' n n'} -> (cf : ∀ {x} -> x ∉ L -> (m ^' x) ->|| (m' ^' x) ) -> n ->|| n' ->
    (app (lam m) n) ->|| (m' ^ n')
  Y : ∀ {m m' σ} -> m ->|| m' -> app (Y σ) m ->|| app m' (app (Y σ) m')

data NotAbsY : PTerm -> Set where
  fv : ∀ {x} -> NotAbsY (fv x)
  bv : ∀ {n} -> NotAbsY (bv n)
  app : ∀ {t1 t2} -> NotAbsY (app t1 t2)

data _>>>_ : PTerm ↝ PTerm where
  refl : ∀ {x} -> fv x >>> fv x
  reflY : ∀ {σ} -> Y σ >>> Y σ
  app : ∀ {m m' n n'} -> NotAbsY m -> m >>> m' -> n >>> n' -> app m n >>> app m' n'
  abs : ∀ L {m m'} -> ( ∀ {x} -> x ∉ L -> (m ^' x) >>> (m' ^' x) ) ->
    lam m >>> lam m'
  beta : ∀ L {m m' n n'} -> (cf : ∀ {x} -> x ∉ L -> (m ^' x) >>> (m' ^' x) ) -> n >>> n' ->
    app (lam m) n >>> (m' ^ n')
  Y : ∀ {m m' σ} -> m >>> m' -> app (Y σ) m >>> app m' (app (Y σ) m')


subst-Term : ∀ {x e u} -> Term e -> Term u -> Term (e [ x ::= u ])
subst-Term {x} {_} {u} (var {y}) Term-u with x ≟ y
subst-Term var Term-u | yes refl = Term-u
subst-Term var Term-u | no p = var
subst-Term {x} {_} {u} (lam L {e} cf) Term-u = lam (x ∷ L) body
  where
  body : {y : ℕ} -> y ∉ x ∷ L → Term ((e [ x ::= u ]) ^' y)
  body {y} y∉x∷L rewrite subst-open-var y x u e (fv-x-neq-y y x y∉x∷L) Term-u =
    subst-Term (cf (λ z → y∉x∷L (there z))) Term-u


subst-Term (app Term-e Term-e₁) Term-u =
  app (subst-Term Term-e Term-u) (subst-Term Term-e₁ Term-u)
subst-Term Y Term-u = Y

^-Term : ∀ {m n} -> Term (lam m) -> Term n -> Term (m ^ n)
^-Term {m} {n} (lam L cf) Term-n = body
  where
  y = ∃fresh (L ++ FV m)

  y∉ : y ∉ (L ++ FV m)
  y∉ = ∃fresh-spec (L ++ FV m)


  body : Term (m ^ n)
  body rewrite subst-intro y n m (∉-cons-r L (FV m) y∉) Term-n =
    subst-Term {y} {m ^' y} {n} (cf (∉-cons-l L (FV m) y∉)) Term-n

  -- subst-Term {y} {m ^' y} {n}


->||-Term-l : ∀ {m m'} -> m ->|| m' -> Term m
->||-Term-l refl = var
->||-Term-l reflY = Y
->||-Term-l (app m->||m' m->||m'') = app (->||-Term-l m->||m') (->||-Term-l m->||m'')
->||-Term-l (abs L x) = lam L (λ {x₁} x∉L → ->||-Term-l (x x∉L))
->||-Term-l (beta L x m->||m') =
  app (lam L (λ {x₁} x∉L → ->||-Term-l (x x∉L)))
      (->||-Term-l m->||m')
->||-Term-l (Y {m} {m'} m->||m') = app Y (->||-Term-l m->||m')

->||-Term-r : ∀ {m m'} -> m ->|| m' -> Term m'
->||-Term-r refl = var
->||-Term-r reflY = Y
->||-Term-r (app m->||m' m->||m'') = app (->||-Term-r m->||m') (->||-Term-r m->||m'')
->||-Term-r (abs L x) = lam L (λ {x₁} x∉L → ->||-Term-r (x x∉L))
->||-Term-r (beta L {m} {m'} {n} {n'} cf m->||m') =
  ^-Term {m'} {n'} (lam L (λ {x₁} x∉L → ->||-Term-r (cf x∉L))) (->||-Term-r m->||m')
->||-Term-r (Y m->||m') = app (->||-Term-r m->||m') (app Y (->||-Term-r m->||m'))

lem2-5-1 : ∀ s s' t t' (x : ℕ) -> s ->|| s' -> t ->|| t' ->
  (s [ x ::= t ]) ->|| (s' [ x ::= t' ])
lem2-5-1 _ _ t t' y (refl {x}) t->||t' with x ≟ y
lem2-5-1 .(fv x) .(fv x) t t' x refl t->||t' | yes refl rewrite
  fv-subst-eq x x t refl | fv-subst-eq x x t' refl = t->||t'
lem2-5-1 _ _ t t' y (refl {x}) t->||t'             | no x≠y rewrite
  fv-subst-neq x y t x≠y | fv-subst-neq x y t' x≠y = refl
lem2-5-1 _ _ t t' x reflY t->||t' = reflY
lem2-5-1 _ _ t t' x (app {m} {m'} {n} {n'} ss' ss'') t->||t' = app (lem2-5-1 m m' t t' x ss' t->||t') (lem2-5-1 n n' t t' x ss'' t->||t')
lem2-5-1 _ _ t t' x (abs L {m} {m'} cf) t->||t' = abs (x ∷ L) body
  where
  x∉FVy : (y : ℕ) -> (y ∉ x ∷ L) -> x ∉ FV (fv y)
  x∉FVy y y∉x∷L x∈FVy with fv-x-eq-y x y x∈FVy
  x∉FVy .x y∉x∷L x∈FVy | refl = y∉x∷L (here refl)

  body : {y : ℕ} -> (y ∉ x ∷ L) -> ((m [ x ::= t ]) ^' y) ->|| ((m' [ x ::= t' ]) ^' y)
  body {y} y∉x∷L rewrite
    subst-fresh2 x (fv y) t (x∉FVy y y∉x∷L) |
    subst-open2 x t 0 (fv y) m (->||-Term-l t->||t') |
    subst-fresh x (fv y) t (x∉FVy y y∉x∷L) |
    subst-fresh2 x (fv y) t' (x∉FVy y y∉x∷L) |
    subst-open2 x t' 0 (fv y) m' (->||-Term-r t->||t') |
    subst-fresh x (fv y) t' (x∉FVy y y∉x∷L) =
      lem2-5-1 (m ^' y) (m' ^' y) t t' x (cf (λ z → y∉x∷L (there z))) t->||t'

lem2-5-1 _ _ t t' x (beta L {m} {m'} {n} {n'} cf n->||n') t->||t' rewrite
  subst-open x t' 0 n' m' (->||-Term-r t->||t') =
    beta (x ∷ L) {_} {m' [ x ::= t' ]}  body body₂
  where
  body : {y : ℕ} -> y ∉ x ∷ L -> ((m [ x ::= t ]) ^' y) ->|| ((m' [ x ::= t' ]) ^' y)
  body {y} y∉x∷L rewrite
    subst-open-var y x t m (fv-x-neq-y y x y∉x∷L) (->||-Term-l t->||t') |
    subst-open-var y x t' m' (fv-x-neq-y y x y∉x∷L) (->||-Term-r t->||t') =
      lem2-5-1 (m ^' y) (m' ^' y) t t' x (cf (λ z → y∉x∷L (there z))) t->||t'

  body₂ : (n [ x ::= t ]) ->|| (n' [ x ::= t' ])
  body₂ = lem2-5-1 n n' t t' x n->||n' t->||t'

lem2-5-1 _ _ t t' x (Y {m} {m'} ss') t->||t' = Y (lem2-5-1 m m' t t' x ss' t->||t')


lem2-5-1-^ : ∀ s s' t t' L -> (∀ {x} -> x ∉ L -> (s ^' x) ->|| (s' ^' x)) -> t ->|| t' ->
  (s ^ t) ->|| (s' ^ t')
lem2-5-1-^ s s' t t' L cf t->||t' = body
  where
  x = ∃fresh (L ++ FV s ++ FV s')

  x∉ : x ∉ (L ++ FV s ++ FV s')
  x∉ = ∃fresh-spec (L ++ FV s ++ FV s')

  body : (s ^ t) ->|| (s' ^ t')
  body rewrite
    subst-intro x t s (∉-cons-l (FV s) (FV s') (∉-cons-r L (FV s ++ FV s') x∉)) (->||-Term-l t->||t') |
    subst-intro x t' s' (∉-cons-r (FV s) (FV s') (∉-cons-r L (FV s ++ FV s') x∉)) (->||-Term-r t->||t') =
      lem2-5-1 (s ^' x) (s' ^' x) t t' x (cf (∉-cons-l L (FV s ++ FV s') x∉)) t->||t'
