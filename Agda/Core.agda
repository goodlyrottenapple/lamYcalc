module Core where

open import Data.Empty
open import Data.Nat
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Data.Sum
open import Data.Nat.Properties

Atom = ℕ

data Type : Set where
  σ : Type
  _⟶_ : (t₁ : Type) -> (t₂ : Type) -> Type

data PTerm : Set where
  bv : (i : ℕ) -> PTerm
  fv : (x : Atom) -> PTerm
  lam : (e : PTerm) -> PTerm
  app : (e₁ : PTerm) -> (e₂ : PTerm) -> PTerm
  Y : (t₁ : Type) -> PTerm

[_>>_] : ℕ -> PTerm -> PTerm -> PTerm
[ k >> u ] (bv i) with k ≟ i
... | yes _ = u
... | no _ = bv i
[ k >> u ] (fv x) = fv x
[ k >> u ] (lam t) = lam ([ (suc k) >> u ] t)
[ k >> u ] (app t1 t2) = app ([ k >> u ] t1) ([ k >> u ] t2)
[ k >> u ] (Y t) = Y t

_^_ : PTerm -> PTerm -> PTerm
t ^ u = [ 0 >> u ] t

_^'_ : PTerm -> Atom -> PTerm
t ^' x = t ^ (fv x)

[_<<_] : ℕ -> Atom -> PTerm -> PTerm
[ k << x ] (bv i) = bv i
[ k << x ] (fv y) with x ≟ y
... | yes _ = bv k
... | no _ = fv y
[ k << x ] (lam t) = lam ([ (suc k) << x ] t)
[ k << x ] (app t1 t2) = app ([ k << x ] t1) ([ k << x ] t2)
[ k << x ] (Y t) = Y t

*_^_ : Atom -> PTerm -> PTerm
* x ^ t = [ 0 << x ] t

_[_::=_] : PTerm -> Atom -> PTerm -> PTerm
bv i [ x ::= u ] = bv i
fv y [ x ::= u ] with x ≟ y
... | yes _ = u
... | no _ = fv y
lam t [ x ::= u ] = lam (t [ x ::= u ])
app t1 t2 [ x ::= u ] = app (t1 [ x ::= u ]) (t2 [ x ::= u ])
Y t₁ [ x ::= u ] = Y t₁

FVars = List Atom

FV : PTerm -> FVars
FV (bv i) = []
FV (fv x) = x ∷ []
FV (lam e) = FV e
FV (app e₁ e₂) = FV e₁ ++ FV e₂
FV (Y t) = []

data Term : PTerm -> Set where
  var : ∀ {x} -> Term (fv x)
  lam : (L : FVars) -> ∀ {e} ->
    (cf : ∀ {x} -> (x∉L : x ∉ L) -> Term (e ^' x)) -> Term (lam e)
  app : ∀ {e₁ e₂} -> Term e₁ -> Term e₂ -> Term (app e₁ e₂)
  Y : ∀ {t} -> Term (Y t)


postulate ∃fresh : FVars -> Atom
postulate ∃fresh-spec : ∀ L -> ∃fresh L ∉ L

∪ : FVars -> Atom
∪ [] = 0
∪ (x ∷ xs) = x ⊔ (∪ xs)

∃fresh-impl : FVars -> Atom
∃fresh-impl list = suc (∪ list)

_∨_ = _⊎_

ℕ-meet-dist : ∀ {x y z : ℕ} -> (x ≤ y) ∨ (x ≤ z) -> x ≤ y ⊔ z
ℕ-meet-dist {zero} x≤y⊎x≤z = z≤n
ℕ-meet-dist {suc x} {zero} {zero} (inj₁ ())
ℕ-meet-dist {suc x} {zero} {zero} (inj₂ ())
ℕ-meet-dist {suc x} {zero} {suc z} (inj₁ ())
ℕ-meet-dist {suc x} {zero} {suc z} (inj₂ sx≤sz) = sx≤sz
ℕ-meet-dist {suc x} {suc y} {zero} (inj₁ sx≤sy) = sx≤sy
ℕ-meet-dist {suc x} {suc y} {zero} (inj₂ ())
ℕ-meet-dist {suc x} {suc y} {suc z} (inj₁ (s≤s x≤y)) = s≤s (ℕ-meet-dist (inj₁ x≤y))
ℕ-meet-dist {suc x} {suc y} {suc z} (inj₂ (s≤s y≤z)) = s≤s (ℕ-meet-dist {_} {y} {z} (inj₂ y≤z))

≤-refl : ∀ {x : ℕ} -> x ≤ x
≤-refl {zero} = z≤n
≤-refl {suc x} = s≤s ≤-refl

∈-cons : ∀ {L} {x y : ℕ} -> x ∈ (y ∷ L) -> ¬(x ≡ y) -> x ∈ L
∈-cons {[]} (here refl) ¬x≡y = ⊥-elim (¬x≡y refl)
∈-cons {[]} (there ()) ¬x≡y
∈-cons {y ∷ L} {x} (here refl) ¬x≡y = ⊥-elim (¬x≡y refl)
∈-cons {y ∷ L} {x} (there x∈L) ¬x≡y = x∈L

∃fresh-impl-spec' : ∀ x L -> x ∈ L -> x ≤ ∪ L
∃fresh-impl-spec' x [] ()
∃fresh-impl-spec' x (y ∷ L) x∈y∷L with x ≟ y
∃fresh-impl-spec' x (.x ∷ L) x∈y∷L | yes refl = ℕ-meet-dist {x} {x} (inj₁ ≤-refl)
∃fresh-impl-spec' x (y ∷ L) x∈y∷L | no ¬x≡y = ℕ-meet-dist {x} {y} (inj₂ (∃fresh-impl-spec' x L (∈-cons x∈y∷L ¬x≡y)))

∃fresh-impl-spec'' : ∀ x L -> x ∈ L -> ¬ (x ≡ ∃fresh-impl L)
∃fresh-impl-spec'' .(suc (∪ L)) L x∈L refl = 1+n≰n {∪ L} (∃fresh-impl-spec' (suc (∪ L)) L x∈L)

∃fresh-impl-spec : ∀ L -> ∃fresh-impl L ∉ L
∃fresh-impl-spec L ∃fresh-implL∈L = ∃fresh-impl-spec'' (∃fresh-impl L) L ∃fresh-implL∈L refl
