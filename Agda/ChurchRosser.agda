module ChurchRosser where
open import Data.Empty
open import Data.Product
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Core
open import Core-Lemmas
open import Reduction
open import Typing

data _* (R : PTerm ↝ PTerm) : PTerm ↝ PTerm where
  base : ∀ {a b} -> R a b -> (R *) a b
  refl : ∀ {a} -> (R *) a a
  trans : ∀ {a b c} -> (R *) a b -> (R *) b c -> (R *) a c

->β*-⊢ : ∀ {Γ m m' τ} -> Γ ⊢ m ∶ τ -> (_->β_ *) m m' -> Γ ⊢ m' ∶ τ
->β*-⊢ Γ⊢m∶τ (base m->βm') = ->β-⊢ Γ⊢m∶τ m->βm'
->β*-⊢ Γ⊢m∶τ refl = Γ⊢m∶τ
->β*-⊢ Γ⊢m∶τ (trans m->β*m' m->β*m'') = ->β*-⊢ (->β*-⊢ Γ⊢m∶τ m->β*m') m->β*m''

DP : (R : PTerm ↝ PTerm)(T : PTerm ↝ PTerm) -> Set
DP R T = ∀ {a b c} -> R a b -> T a c -> ∃ (λ d → (T b d) × (R c d))

DP->||->||-imp-DP->||->||* : DP (_->||_) (_->||_) -> DP (_->||_) (_->||_ *)
DP->||->||-imp-DP->||->||* DP->||->|| {b = b} a->||b (base a->||c) = d , (base b->||d , c->||d)
  where
  d = proj₁ (DP->||->|| a->||b a->||c)
  b->||d = proj₁ (proj₂ (DP->||->|| a->||b a->||c))
  c->||d = proj₂ (proj₂ (DP->||->|| a->||b a->||c))

DP->||->||-imp-DP->||->||* DP->||->|| {b = b} a->||b refl = b , (refl , a->||b)
DP->||->||-imp-DP->||->||* DP->||->|| {a} {b} {c} a->||b (trans {b = g} a->||*g g->||*c) =
  d , ((trans b->||*g' g'->||*d) , c->||d)
  where
  left-IH : ∃ (λ g' → (_->||_ *) b g' × (g ->|| g'))
  left-IH = DP->||->||-imp-DP->||->||* DP->||->|| a->||b a->||*g

  g' = proj₁ left-IH
  b->||*g' = proj₁ (proj₂ left-IH)
  g->||g' = proj₂ (proj₂ left-IH)

  right-IH : ∃ (λ d → (_->||_ *) g' d × (c ->|| d))
  right-IH = DP->||->||-imp-DP->||->||* DP->||->|| g->||g' g->||*c

  d = proj₁ right-IH
  g'->||*d = proj₁ (proj₂ right-IH)
  c->||d = proj₂ (proj₂ right-IH)


DP->||->||-imp-DP->||*->||* : DP (_->||_) (_->||_) -> DP (_->||_ *) (_->||_ *)
DP->||->||-imp-DP->||*->||* DP->||->|| (base a->||b) a->||*c = d , (b->||*d , base c->||d)
  where
  d = proj₁ (DP->||->||-imp-DP->||->||* DP->||->|| a->||b a->||*c)
  b->||*d = proj₁ (proj₂ (DP->||->||-imp-DP->||->||* DP->||->|| a->||b a->||*c))
  c->||d = proj₂ (proj₂ (DP->||->||-imp-DP->||->||* DP->||->|| a->||b a->||*c))

DP->||->||-imp-DP->||*->||* DP->||->|| refl a->||*c = _ , (a->||*c , refl)
DP->||->||-imp-DP->||*->||* DP->||->|| {a} {b} {c} (trans {b = g} a->||*g g->||*b) a->||*c =
  d , b->||*d , (trans c->||*g' g'->||*d)
  where
  left-IH : ∃ (λ g' → (_->||_ *) g g' × (_->||_ *) c g')
  left-IH = DP->||->||-imp-DP->||*->||* DP->||->|| a->||*g a->||*c

  g' = proj₁ left-IH
  c->||*g' = proj₂ (proj₂ left-IH)
  g->||*g' = proj₁ (proj₂ left-IH)

  right-IH : ∃ (λ d → (_->||_ *) b d × (_->||_ *) g' d)
  right-IH = DP->||->||-imp-DP->||*->||* DP->||->|| g->||*b g->||*g'

  d = proj₁ right-IH
  g'->||*d = proj₂ (proj₂ right-IH)
  b->||*d = proj₁ (proj₂ right-IH)


->||-refl : ∀ {s} -> Term s -> s ->|| s
->||-refl var = refl
->||-refl (lam L cf) = abs L (λ {x} z → ->||-refl (cf z))
->||-refl (app trm-s trm-s₁) = app (->||-refl trm-s) (->||-refl trm-s₁)
->||-refl Y = reflY

->β-imp->|| : ∀ {m m'} -> m ->β m' -> m ->|| m'
->β-imp->|| (redL trm-n m->βm') = app (->β-imp->|| m->βm') (->||-refl trm-n)
->β-imp->|| (redR trm-m n->βn') = app (->||-refl trm-m) (->β-imp->|| n->βn')
->β-imp->|| (abs L x) = abs L (λ {x₁} z → ->β-imp->|| (x z))
->β-imp->|| (beta {m} (lam L cf) trm-n) =
  beta L {m' = m} (λ {x} x∉L → ->||-refl (cf x∉L)) (->||-refl trm-n)
->β-imp->|| (Y trm-m) = Y (->||-refl trm-m)

->β*-imp->||* : ∀ {m m'} -> (_->β_ *) m m' -> (_->||_ *) m m'
->β*-imp->||* (base m->βm') = base (->β-imp->|| m->βm')
->β*-imp->||* refl = refl
->β*-imp->||* (trans m->β*m' m->β*m'') =
  trans (->β*-imp->||* m->β*m') (->β*-imp->||* m->β*m'')

redL* : ∀ {m m' n} -> (_->β_ *) m m' -> Term n -> (_->β_ *) (app m n) (app m' n)
redL* (base x) trm-n = base (redL trm-n x)
redL* refl trm-n = refl
redL* (trans m->β*o o->β*m') trm-n = trans (redL* m->β*o trm-n) (redL* o->β*m' trm-n)

redR* : ∀ {m n n'} -> (_->β_ *) n n' -> Term m -> (_->β_ *) (app m n) (app m n')
redR* (base x) trm-m = base (redR trm-m x)
redR* refl trm-m = refl
redR* (trans n->β*o o->β*n) trm-m = trans (redR* n->β*o trm-m) (redR* o->β*n trm-m)

abs' : ∀ {m m' x} -> m ->β m' -> (lam (* x ^ m)) ->β (lam (* x ^ m'))
abs' {m} {m'} {x} m->βm' = abs [] body
  where
  body : ∀ {y} -> y ∉ [] -> ((* x ^ m) ^' y) ->β ((* x ^ m') ^' y)
  body {y} y∉ rewrite
    *^-^≡subst m x y {0} (->β-Term-l m->βm') |
    *^-^≡subst m' x y {0} (->β-Term-r m->βm') = lem2-5-1->β m m' x y m->βm'

abs*' : ∀ {m m' x} -> (_->β_ *) m m' -> (_->β_ *) (lam (* x ^ m)) (lam (* x ^ m'))
abs*' (base m->βm') = base (abs' m->βm')
abs*' refl = refl
abs*' (trans m->β*m' m->β*m'') = trans (abs*' m->β*m') (abs*' m->β*m'')

abs* : ∀ {m m'} L -> (cf : ∀ {x} -> x ∉ L -> (_->β_ *) (m ^' x) (m' ^' x)) -> (_->β_ *) (lam m) (lam m')
abs* {m} {m'} L cf = body
  where
  x = ∃fresh (L ++ FV m ++ FV m')

  x∉ : x ∉ (L ++ FV m ++ FV m')
  x∉ = ∃fresh-spec (L ++ FV m ++ FV m')

  subst : ∀ m -> x ∉ FV m -> _≡_ {_} {PTerm} (lam m) (lam (* x ^ (m ^' x)))
  subst m x∉m rewrite
    fv-^-*^-refl x m {0} x∉m = _≡_.refl

  body : (_->β_ *) (lam m) (lam m')
  body rewrite
    subst m (∉-cons-l _ _ (∉-cons-r L _ x∉)) |
    subst m' (∉-cons-r (FV m) _ (∉-cons-r L _ x∉)) = abs*' (cf (∉-cons-l _ _ x∉))


->||-imp->β* : ∀ {m m'} -> m ->|| m' -> (_->β_ *) m m'
->||-imp->β* refl = refl
->||-imp->β* reflY = refl
->||-imp->β* (app {m} {m'} {n} {n'} m->||m' n->||n') =
  trans {b = (app m n')}
    (redR* (->||-imp->β* n->||n') (->||-Term-l m->||m'))
    (redL* (->||-imp->β* m->||m') (->||-Term-r n->||n'))
->||-imp->β* (abs L cf) = abs* L (λ x∉ → ->||-imp->β* (cf x∉))
->||-imp->β* (beta L {m} {m'} {n} {n'} cf n->||n') =
  trans {b = app (lam m') n}
    (redL* (abs* L (λ {x} z → ->||-imp->β* (cf z))) (->||-Term-l n->||n'))
    (trans {b = app (lam m') n'}
      (redR* (->||-imp->β* n->||n') (lam L (λ x∉L → ->||-Term-r (cf x∉L))))
      (base (beta (lam L (λ x∉L → ->||-Term-r (cf x∉L))) (->||-Term-r n->||n'))))
->||-imp->β* (Y {m} {m'} {τ} m->||m') =
  trans {b = app m (app (Y τ) m)}
    (base (Y (->||-Term-l m->||m')))
    (trans {b = app m' (app (Y τ) m)}
      (redL* (->||-imp->β* m->||m') (app Y (->||-Term-l m->||m')))
      (redR* (redR* (->||-imp->β* m->||m') Y) (->||-Term-r m->||m')))


->||*-imp->β* : ∀ {m m'} -> (_->||_ *) m m' -> (_->β_ *) m m'
->||*-imp->β* (base m->||m') = ->||-imp->β* m->||m'
->||*-imp->β* refl = refl
->||*-imp->β* (trans m->||*m' n->||*n') = trans (->||*-imp->β* m->||*m') (->||*-imp->β* n->||*n')


church-rosser-⊢ : ∀ {Γ τ a b c} -> Γ ⊢ a ∶ τ -> (_->β_ *) a b -> (_->β_ *) a c ->
  ∃(λ d -> ((_->β_ *) b d × (_->β_ *) c d) × Γ ⊢ d ∶ τ)
church-rosser-⊢ {Γ} {τ} {a} {b} {c} Γ⊢a∶τ a->β*b a->β*c =
  d , (b->β*d , c->β*d) , ->β*-⊢ Γ⊢a∶τ a->β*d
  where
  a->||*b = ->β*-imp->||* a->β*b
  a->||*c = ->β*-imp->||* a->β*c

  d-spec : ∃ (λ d → ((_->||_ *) b d) × ((_->||_ *) c d))
  d-spec = DP->||->||-imp-DP->||*->||* lem2-5-2 a->||*b a->||*c

  d = proj₁ d-spec
  b->||*d = proj₁ (proj₂ d-spec)
  c->||*d = proj₂ (proj₂ d-spec)
  a->||*d = trans a->||*b b->||*d
  a->β*d = ->||*-imp->β* a->||*d
  b->β*d = ->||*-imp->β* b->||*d
  c->β*d = ->||*-imp->β* c->||*d
