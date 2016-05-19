module Core-Lemmas where

open import Data.Empty
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡

open import Core

∈-cons-l : ∀ {A : Set} {x : A} {xs} ys -> x ∈ xs -> x ∈ (xs ++ ys)
∈-cons-l ys (here eq) = here eq
∈-cons-l ys (there x∈xs') = there (∈-cons-l ys x∈xs')

∉-cons-l : ∀ {A : Set} {x : A} xs ys -> x ∉ xs ++ ys -> x ∉ xs
∉-cons-l _ ys x∉xs++ys (here eq) = x∉xs++ys (here eq)
∉-cons-l .(x' ∷ xs') ys x∉xs++ys (there {x'} {xs'} x∈xs') = ∉-cons-l xs' ys (λ z → x∉xs++ys (there z)) x∈xs'

∉-cons-r : ∀ {A : Set} {x : A} xs ys -> x ∉ xs ++ ys -> x ∉ ys
∉-cons-r [] ys x∉xs++ys x∈ys = x∉xs++ys x∈ys
∉-cons-r (_ ∷ xs) ys x∉xs++ys x∈ys = ∉-cons-r xs ys (λ z → x∉xs++ys (there z)) x∈ys


subst-fresh : ∀ x t u -> (x∉FVt : x ∉ (FV t)) -> (t [ x / u ]) ≡ t
subst-fresh x (bv i)      u x∉FVt = refl
subst-fresh x (fv y)      u x∉FVt with x ≟ y
subst-fresh x (fv .x)     u x∉FVt | yes refl = ⊥-elim (x∉FVt (here refl))
...                               | no z = refl
subst-fresh x (lam t)     u x∉FVt rewrite
  subst-fresh x t u x∉FVt = refl
subst-fresh x (app t1 t2) u x∉FVt rewrite
  subst-fresh x t1 u (∉-cons-l (FV t1) (FV t2) x∉FVt) |
  subst-fresh x t2 u (∉-cons-r (FV t1) (FV t2) x∉FVt) = refl
subst-fresh x (Y t₁)      u x∉FVt = refl
