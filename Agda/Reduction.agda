module Reduction where

open import Data.Empty
open import Data.Nat
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product


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
  body {y} y∉x∷L rewrite subst-open-var y x u e (fv-x≠y y x y∉x∷L) Term-u =
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
->||-Term-l (abs L x) = lam L (λ x∉L → ->||-Term-l (x x∉L))
->||-Term-l (beta L x m->||m') =
  app (lam L (λ {x₁} x∉L → ->||-Term-l (x x∉L)))
      (->||-Term-l m->||m')
->||-Term-l (Y {m} {m'} m->||m') = app Y (->||-Term-l m->||m')

->||-Term-r : ∀ {m m'} -> m ->|| m' -> Term m'
->||-Term-r refl = var
->||-Term-r reflY = Y
->||-Term-r (app m->||m' m->||m'') = app (->||-Term-r m->||m') (->||-Term-r m->||m'')
->||-Term-r (abs L x) = lam L (λ x∉L → ->||-Term-r (x x∉L))
->||-Term-r (beta L {m} {m'} {n} {n'} cf m->||m') =
  ^-Term {m'} {n'} (lam L (λ {x₁} x∉L → ->||-Term-r (cf x∉L))) (->||-Term-r m->||m')
->||-Term-r (Y m->||m') = app (->||-Term-r m->||m') (app Y (->||-Term-r m->||m'))


>>>-Term-l : ∀ {m m'} -> m >>> m' -> Term m
>>>-Term-l refl = var
>>>-Term-l reflY = Y
>>>-Term-l (app nAbsY m>>>m' m>>>m'') = app (>>>-Term-l m>>>m') (>>>-Term-l m>>>m'')
>>>-Term-l (abs L x) = lam L (λ x∉L → >>>-Term-l (x x∉L))
>>>-Term-l (beta L x m>>>m') =
  app (lam L (λ {x₁} x∉L → >>>-Term-l (x x∉L)))
      (>>>-Term-l m>>>m')
>>>-Term-l (Y {m} {m'} m>>>m') = app Y (>>>-Term-l m>>>m')

>>>-Term-r : ∀ {m m'} -> m >>> m' -> Term m'
>>>-Term-r refl = var
>>>-Term-r reflY = Y
>>>-Term-r (app nAbsY m>>>m' m>>>m'') = app (>>>-Term-r m>>>m') (>>>-Term-r m>>>m'')
>>>-Term-r (abs L x) = lam L (λ x∉L → >>>-Term-r (x x∉L))
>>>-Term-r (beta L {m} {m'} {n} {n'} cf m>>>m') =
  ^-Term {m'} {n'} (lam L (λ {x₁} x∉L → >>>-Term-r (cf x∉L))) (>>>-Term-r m>>>m')
>>>-Term-r (Y m>>>m') = app (>>>-Term-r m>>>m') (app Y (>>>-Term-r m>>>m'))


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
  x∉FVy y y∉x∷L x∈FVy with fv-x≡y x y x∈FVy
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
    subst-open-var y x t m (fv-x≠y y x y∉x∷L) (->||-Term-l t->||t') |
    subst-open-var y x t' m' (fv-x≠y y x y∉x∷L) (->||-Term-r t->||t') =
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


NotAbsY-subst : ∀ {x y m} -> NotAbsY m -> NotAbsY (m [ x ::= fv y ])
NotAbsY-subst {x} (fv {y}) with x ≟ y
NotAbsY-subst {x} {y} fv | yes refl rewrite
  fv-subst-eq x x (fv y) refl = fv
NotAbsY-subst fv | no _ = fv
NotAbsY-subst bv = bv
NotAbsY-subst app = app


lem2-5-1>>> : ∀ s s' (x y : ℕ) -> s >>> s' -> (s [ x ::= fv y ]) >>> (s' [ x ::= fv y ])
lem2-5-1>>> _ _ x y (refl {z}) with x ≟ z
lem2-5-1>>> .(fv x) .(fv x) x y refl | yes refl rewrite
  fv-subst-eq x x (fv y) refl = refl
lem2-5-1>>> _ _ x y (refl {z}) | no z≠x = refl
lem2-5-1>>> _ _ x y reflY = reflY
lem2-5-1>>> _ _ x y (app {m} {m'} {n} {n'} ¬absY ss' ss'') =
  app (NotAbsY-subst ¬absY) (lem2-5-1>>> m m' x y ss') (lem2-5-1>>> n n' x y ss'')
lem2-5-1>>> _ _ x y (abs L {m} {m'} cf) = abs (x ∷ L) body
  where
  x∉FVz : (z : ℕ) -> (z ∉ x ∷ L) -> x ∉ FV (fv z)
  x∉FVz z z∉x∷L x∈FVz with fv-x≡y x z x∈FVz
  x∉FVz .x z∉x∷L x∈FVz | refl = z∉x∷L (here refl)

  body : {z : ℕ} -> (z ∉ x ∷ L) -> ((m [ x ::= fv y ]) ^' z) >>> ((m' [ x ::= fv y ]) ^' z)
  body {z} z∉x∷L rewrite
    subst-fresh2 x (fv z) (fv y) (x∉FVz z z∉x∷L) |
    subst-open2 x (fv y) 0 (fv z) m var |
    subst-fresh x (fv z) (fv y) (x∉FVz z z∉x∷L) |
    subst-fresh2 x (fv z) (fv y) (x∉FVz z z∉x∷L) |
    subst-open2 x (fv y) 0 (fv z) m' var |
    subst-fresh x (fv z) (fv y) (x∉FVz z z∉x∷L) =
      lem2-5-1>>> (m ^' z) (m' ^' z) x y (cf (λ z₁ → z∉x∷L (there z₁)))

lem2-5-1>>> _ _ x y (beta L {m} {m'} {n} {n'} cf n>>>n') rewrite
  subst-open x (fv y) 0 n' m' var =
    beta (x ∷ L) {_} {m' [ x ::= fv y ]} body body₂
  where
  body : {z : ℕ} -> z ∉ x ∷ L -> ((m [ x ::= fv y ]) ^' z) >>> ((m' [ x ::= fv y ]) ^' z)
  body {z} z∉x∷L rewrite
    subst-open-var z x (fv y) m (fv-x≠y z x z∉x∷L) var |
    subst-open-var z x (fv y) m' (fv-x≠y z x z∉x∷L) var =
      lem2-5-1>>> (m ^' z) (m' ^' z) x y (cf (λ z₁ → z∉x∷L (there z₁)))

  body₂ : (n [ x ::= fv y ]) >>> (n' [ x ::= fv y ])
  body₂ = lem2-5-1>>> n n' x y n>>>n'

lem2-5-1>>> _ _ x y (Y {m} {m'} ss') = Y (lem2-5-1>>> m m' x y ss')



*^-^->>> : ∀ {x y t d k} -> t >>> d -> y ∉ x ∷ (FV t ++ FV d) -> ([ k >> fv y ] ([ k << x ] t)) >>> ([ k >> fv y ] ([ k << x ] d))
*^-^->>> {x} {y} {t} {d} {k} t>>>d y∉ rewrite
  *^-^≡subst t x y {k} (>>>-Term-l t>>>d) | *^-^≡subst d x y {k} (>>>-Term-r t>>>d) = lem2-5-1>>> t d x y t>>>d

∃>>> : ∀ {a} -> Term a -> ∃(λ d -> a >>> d)
∃>>> (var {x}) = fv x , refl
∃>>> (lam L {t} cf) = body
  where
  x = ∃fresh (L ++ FV t)

  x∉ : x ∉ (L ++ FV t)
  x∉ = ∃fresh-spec (L ++ FV t)

  d-spec : ∃(λ d -> (t ^' x) >>> d)
  d-spec = ∃>>> (cf (∉-cons-l L (FV t) x∉))

  d : PTerm
  d = proj₁ d-spec

  subst1 : ∀ x y t k -> x ∉ FV t -> (t ^' y) ≡ (([ k << x ] ([ k >> fv x ] t)) ^' y)
  subst1 x y t k x∉FVt rewrite fv-^-*^-refl x t {k} x∉FVt = refl

  cf' : ∀ {y} -> y ∉ x ∷ (FV d ++ FV t) -> (t ^' y) >>> ((* x ^ d) ^' y)
  cf' {y} y∉ rewrite subst1 x y t 0 (∉-cons-r L (FV t) x∉) =
    *^-^->>> {x} {y} {t ^' x} {d} {0} (proj₂ d-spec)
      (∉-∷ x (FV (t ^' x) ++ FV d) (fv-x≠y y x y∉)
        (∉-cons-intro (FV (t ^' x)) (FV d)
          (fv-^ {0} {y} {x} t (∉-cons-r (FV d) _ (∉-∷-elim _ y∉)) (fv-x≠y _ _ y∉))
          (∉-cons-l _ (FV t) (∉-∷-elim _ y∉))))

  body : ∃(λ d -> (lam t) >>> d)
  body = lam (* x ^ d) , (abs (x ∷ (FV d ++ FV t)) cf')

∃>>> (app {t1} {t2} trm-t1 trm-t2) with trm-t1 | ∃>>> trm-t1 | ∃>>> trm-t2
∃>>> (app trm-t1 trm-t2) | (var {x}) | d1 , t1>>>d1 | d2 , t2>>>d2 = app (fv x) d2 , app fv refl t2>>>d2
∃>>> (app {_} {t2} trm-t1 trm-t2) | lam L cf | _ , abs L₁ {t1} {d1} cf₁ | d2 , t2>>>d2 =
  d1 ^ d2 , beta L₁ {t1} {d1} {t2} {d2} cf₁ t2>>>d2
∃>>> (app {_} {t2} trm-t1 trm-t2) | app {p1} {p2} trm-p1 trm-p2 | d1 , t1>>>d1 | d2 , t2>>>d2 =
  app d1 d2 , app app t1>>>d1 t2>>>d2
∃>>> (app trm-t1 trm-t2) | (Y {t}) | d1 , t1>>>d1 | d2 , t2>>>d2 = app d2 (app (Y t) d2) , Y t2>>>d2
∃>>> (Y {t}) = Y t , reflY
