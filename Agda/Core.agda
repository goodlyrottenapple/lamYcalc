module Core where

open import Data.Empty
open import Data.Nat
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

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

cls : Atom -> PTerm -> PTerm
cls x = [ 0 << x ]

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
