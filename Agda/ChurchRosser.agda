module ChurchRosser where
open import Data.Empty
open import Data.Product

open import Core
open import Reduction

data _* (R : PTerm ↝ PTerm) : PTerm ↝ PTerm where
  base : ∀ {a b} -> R a b -> (R *) a b
  refl : ∀ {a} -> (R *) a a
  trans : ∀ {a b c} -> (R *) a b -> (R *) b c -> (R *) a c

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
