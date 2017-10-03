module ITyping-Norm where

open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.List.Properties
open import Data.List.Any as LAny
open LAny.Membership-≡
open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality using (sym)

open import Core
open import Core-Lemmas
open import ChurchRosser
open import Typing
open import Typed-Core
open import ITyping-Core
open import ITyping-Subst


data NF : ∀ {A} -> Λ A -> Set where
  bvN : ∀ {t i} -> NF (bv {t} i)
  fvN : ∀ {t x} -> NF (fv {t} x)
  lamN : ∀ L {A B} {m : Λ B} ->
    ( cf : ∀ {x} -> (x∉L : x ∉ L) -> NF (Λ[ 0 >> fv {A} x ] m) ) -> NF (lam A m)
  appBvN : ∀ {t s i m} -> NF m -> NF (app {t} {s} (bv i) m)
  appFvN : ∀ {t s i m} -> NF m -> NF (app {t} {s} (fv i) m)
  YN : ∀ {t} -> NF (Y t)

HasNF : ∀ {A} (m : Λ A) -> Set
HasNF m = ¬ (∃ (λ m' -> m ->Λβ m'))

bvHasNF : ∀ {t i} -> HasNF (bv {t} i)
bvHasNF (m' , ())

fvHasNF : ∀ {t i} -> HasNF (fv {t} i)
fvHasNF (m' , ())

NF->HasNF : ∀ {A} {m : Λ A} -> NF m -> HasNF m
NF->HasNF bvN (m' , ())
NF->HasNF fvN (m' , ())
NF->HasNF (lamN L cf) (_ , (abs L' {m = m} {m'} cf')) = ih (Λ[ 0 >> fv x ] m' , cf' x∉L')
  where
  x = ∃fresh (L ++ L')

  x∉ : x ∉ L ++ L'
  x∉ = ∃fresh-spec (L ++ L')

  x∉L : x ∉ L
  x∉L = ∉-cons-l _ L' x∉

  x∉L' : x ∉ L'
  x∉L' = ∉-cons-r L L' x∉

  ih : HasNF (Λ[ 0 >> fv x ] m)
  ih = NF->HasNF (cf x∉L)
NF->HasNF (appBvN {i = i} _) (_ , redL {m' = m'} _ bvi->Λβm') = ih (m' , bvi->Λβm')
  where
  ih : HasNF (bv i)
  ih = bvHasNF
NF->HasNF (appBvN NFn) (_ , redR {n = n} {n'} _ n->Λβn') = ih (n' , n->Λβn')
  where
  ih : HasNF n
  ih = NF->HasNF NFn
NF->HasNF (appFvN {i = i} _) (_ , redL {m' = m'} _ bvi->Λβm') = ih (m' , bvi->Λβm')
  where
  ih : HasNF (fv i)
  ih = fvHasNF
NF->HasNF (appFvN NFn) (_ , redR {n = n} {n'} _ n->Λβn') = ih (n' , n->Λβn')
  where
  ih : HasNF n
  ih = NF->HasNF NFn
NF->HasNF YN (m' , ())

--Type->∃IType : ∀ A -> ∃(λ τ ->  τ ∷' A)
--Type->∃ITypeₗ : ∀ A -> ∃(λ τ ->  τ ∷'ₗ A)

--Type->∃IType σ = o , base
--Type->∃IType (A ⟶ A₁) = (ω ~> ω) , arr nil nil
--Type->∃ITypeₗ σ = ω , nil
--Type->∃ITypeₗ (A ⟶ A₁) = ω , nil


_∈Γ_ : ∀ {A} → Atom → List (Atom × A) → Set _
x ∈Γ xs = x ∈ (dom xs)


_∈Γ?_ : ∀ {A} → Decidable {A = Atom} (_∈Γ_ {A})
x ∈Γ? [] = no λ ()
x ∈Γ? ((x' , y) ∷ xs) with x ≟ x'
x ∈Γ? ((.x , y) ∷ xs) | yes refl = yes (here refl)
x ∈Γ? ((x' , y) ∷ xs) | no _ with x ∈Γ? xs
x ∈Γ? ((x' , y) ∷ xs) | no _ | yes x∈xs = yes (there x∈xs)
x ∈Γ? ((x' , y) ∷ xs) | no x≠x' | no x∉xs =
  no (λ x∈x'∷xs → x∉xs (∈-∷-elim x (dom xs) (λ x'≡x → x≠x' (sym x'≡x)) x∈x'∷xs))


⊆-list-trans : {A : Set}{xs ys zs : List A} -> xs ⊆ ys -> ys ⊆ zs -> xs ⊆ zs
⊆-list-trans {A} {xs} {ys} {zs} xs⊆ys ys⊆zs = λ {x} z → ys⊆zs (xs⊆ys z)

∈Γ-∃ : ∀ {x Γ} -> x ∈Γ Γ -> Wf-ICtxt Γ -> ∃(λ Γ' -> ∃(λ τ -> ∃(λ A -> Γ ⊆ ((x , τ , A) ∷ Γ') × ((x , τ , A) ∷ Γ') ⊆ Γ × Wf-ICtxt ((x , τ , A) ∷ Γ')))) 
∈Γ-∃ {Γ = []} () _
∈Γ-∃ {Γ = (_ , τ , A) ∷ Γ} (here refl) wf-Γ = Γ , τ , A , (λ {x} z → z) , (λ {x} z → z) , wf-Γ
∈Γ-∃ {x} {(y , τ , A) ∷ Γ} (there x∈Γ) (cons y∉ τ∷A wf-Γ) with ∈Γ-∃ x∈Γ wf-Γ
∈Γ-∃ {x} {(y , τ , A) ∷ Γ} (there x∈Γ) (cons y∉ τ∷A wf-Γ) |
  Γ' , τ' , A' , Γ⊆x,τ,A∷Γ' , x,τ,A∷Γ'⊆Γ , wf-x,τ,A∷Γ'  =
  ((y , τ , A) ∷ Γ') ,
  τ' ,
  A' ,
  ⊆-list-trans (cons-⊆ Γ⊆x,τ,A∷Γ') (help _ _ Γ') ,
  ⊆-list-trans (help _ _ Γ') (cons-⊆ x,τ,A∷Γ'⊆Γ) ,
  wfI-Γ-exchange (cons (λ y∈x∷Γ' → y∉ (help₂ y∈x∷Γ' x,τ,A∷Γ'⊆Γ)) τ∷A wf-x,τ,A∷Γ')
  where
  help : {A : Set} (x y : A) (xs : List A) -> x ∷ y ∷ xs ⊆ y ∷ x ∷ xs
  help x y₁ xs (here refl) = there (here refl)
  help x₁ y xs (there (here refl)) = here refl
  help x₁ y xs (there (there x'∈x∷y∷xs)) = there (there x'∈x∷y∷xs)

  help₁ : ∀ {x} {Γ : ICtxt} -> x ∈ dom Γ -> ∃(λ τ -> (x , τ) ∈ Γ)
  help₁ {Γ = []} ()
  help₁ {Γ = (_ , τ) ∷ Γ} (here refl) = τ , here refl
  help₁ {Γ = y ∷ Γ} (there x∈domΓ) with help₁ x∈domΓ
  help₁ {x} {y ∷ Γ} (there x∈domΓ) | τ , x∈Γ = τ , there x∈Γ

  help₂ : ∀ {x} {Γ Γ' : ICtxt} -> x ∈ dom Γ -> Γ ⊆ Γ' -> x ∈ dom Γ'
  help₂ x∈domΓ Γ⊆Γ' with help₁ x∈domΓ
  help₂ x∈domΓ Γ⊆Γ' | τ , x∈Γ = ∈-imp-∈dom (Γ⊆Γ' x∈Γ)

NF->⊩ : ∀ {A} {m : Λ A} -> NF m -> ΛTerm m -> ∃ (λ Γ -> ∃ (λ τ -> Γ ⊩ m ∶ τ))
NF->⊩ bvN ()
NF->⊩ {σ} (fvN {x = x}) var =
  [ (x , [ o ] , σ) ] ,
  o ,
  var
    (cons (λ ()) (cons base nil) nil)
    (here refl)
    (cons (o , here refl , base) (nil (cons base nil)))
NF->⊩ {A ⟶ B} (fvN {x = x}) var =
  [ (x , [ ω ~> ω ] , A ⟶ B) ] ,
  ω ~> ω ,
  var
    (cons (λ ()) (cons (arr nil nil) nil) nil)
    (here refl)
     (cons ((ω ~> ω) , here refl , arr (nil nil) (nil nil)) (nil (cons (arr nil nil) nil)))
NF->⊩ (lamN L {A} {B} {m} cf) (lam L' cf') = body x∉FVm Γ⊩m^x∶τ
  -- Γ ,
  -- (ω ~> [ τ ]) ,
  -- abs
  --   (x ∷ L ++ L')
  --   (λ x∉L'' →
  --     cons
  --     {!Γ⊩m^x∶τ!}
  --       (nil (cons {!x∉L''!} nil {!!})))
  where
  x = ∃fresh (ΛFV m ++ L ++ L')

  x∉ : x ∉ ΛFV m ++ L ++ L'
  x∉ = ∃fresh-spec (ΛFV m ++ L ++ L')

  x∉FVm : x ∉ ΛFV m
  x∉FVm = ∉-cons-l _ _ x∉

  x∉L : x ∉ L
  x∉L = ∉-cons-l _ _ (∉-cons-r (ΛFV m) _ x∉)

  x∉L' : x ∉ L'
  x∉L' = ∉-cons-r L L' (∉-cons-r (ΛFV m) _ x∉)

  ih : ∃ (λ Γ -> ∃ (λ τ -> Γ ⊩ (Λ[ 0 >> fv x ] m) ∶ τ))
  ih = NF->⊩ (cf x∉L) (cf' x∉L')

  Γ = proj₁ ih
  τ = proj₁ (proj₂ ih)
  Γ⊩m^x∶τ = proj₂ (proj₂ ih)

  body : ∀ {Γ A B τ x} {m : Λ B} -> x ∉ ΛFV m -> Γ ⊩ (Λ[ 0 >> fv {A} x ] m) ∶ τ -> ∃ (λ Γ -> ∃ (λ τ -> Γ ⊩ (lam A m) ∶ τ))
  body {Γ} {A} {B} {τ} {x = x} x∉FVm Γ⊩m^x∶τ with x ∈Γ? Γ
  body {Γ} {τ = τ} {x} {m} x∉FVm Γ⊩m^x∶τ | yes x∈Γ with ∈Γ-∃ x∈Γ (⊩-wf-Γ Γ⊩m^x∶τ)
  body {Γ} {τ = τ} {x} {m} x∉FVm Γ⊩m^x∶τ | yes x∈Γ | Γ' , τ' , A' , Γ⊆x∷Γ' , _ , wf-x∷Γ' =
    Γ' ,
    (τ' ~> [ τ ]) ,
    abs
      {!!}
      (λ {y} y∉L → cons
      (aux {x = x}
        m
        (proj₂ (∃~T m))
        {!!}
        {!!}
        {!!}
        {!!}
        {!x∷Γ'⊩m^x∶τ!})
        (nil (cons {!!} {!!} {!!})))
    where
    Γ⊆Γx∷Γ' = ⊆Γ-⊆ wf-x∷Γ' Γ⊆x∷Γ'

    x∷Γ'⊩m^x∶τ : ((x , τ' , A') ∷ Γ') ⊩ Λ[ 0 >> fv x ] m ∶ τ
    x∷Γ'⊩m^x∶τ = subΓ Γ⊩m^x∶τ Γ⊆Γx∷Γ'

  body {Γ} {τ = τ} {x} {m} x∉FVm Γ⊩m^x∶τ | no x∉Γ =
    Γ ,
    (ω ~> [ τ ]) ,
    (abs (x ∷ (dom Γ ++ ΛFV m)) (λ {y} y∉L →
      cons
        (aux {x = x}
          m
          (proj₂ (∃~T m))
          (∉-∷-elim _ (∉-cons-l _ _ y∉L))
          x∉FVm
          (∉-cons-r (dom Γ) (ΛFV m) (∉-∷-elim _ y∉L))
          (λ x≡y → y∉L (here (sym x≡y)))
          (subΓ Γ⊩m^x∶τ (⊆Γ-⊆ (cons x∉Γ nil (⊩-wf-Γ Γ⊩m^x∶τ)) (λ {x₁} → there))))
          (nil (cons (∉-∷-elim _ (∉-cons-l _ _ y∉L)) nil (⊩-wf-Γ Γ⊩m^x∶τ)))))

NF->⊩ (appBvN NFm) (app () trm-m)
NF->⊩ (appFvN {A} {B} {x} {m} NFm) (app trm trm-m) = {!!}
  -- (x , [ [ τ ] ~> ω ] , A ⟶ B) ∷ Γ ,
  -- [ τ ] ~> ω ,
  -- app
  --   (var {!!} {!!} {!!})
  --   (cons {!!} (nil {!!}))
  --   {!!}
  -- where
  -- ih : ∃ (λ Γ -> ∃ (λ τ -> Γ ⊩ m ∶ τ))
  -- ih = NF->⊩ NFm trm-m

  -- Γ = proj₁ ih
  -- τ = proj₁ (proj₂ ih)
  -- Γ⊩m∶τ = proj₂ (proj₂ ih)
NF->⊩ (YN {t = A}) Y =
  [] ,
  [ ω ~> ω ] ~> ω ,
  Y {τ = ω}
    nil
    (cons ((ω ~> ω) , here refl , arr (nil nil) (nil nil)) (nil (cons (arr nil nil) nil)))
    (nil nil)

--HasNF->⊩ : ∀ {A Γ τ} {m n : Λ A} -> NF n -> m ->Λβ n -> Γ ⊩ n ∶ τ -> Γ ⊩ m ∶ τ
--HasNF->⊩ = {!!}


P : ∀ A -> IType -> Λ A -> Set
Pₗ : ∀ {A} -> List IType -> Λ A -> Set

P σ o m = [] ⊩ m ∶ o × NF m
P σ (_ ~> _) _ = ⊥
P (_ ⟶ _) o _ = ⊥
P (A ⟶ B) (τ ~> τ') m = [] ⊩ m ∶ (τ ~> τ') × (∀ {n : Λ A} -> Pₗ τ n -> Pₗ τ' (app m n))

Pₗ [] m = [] ⊩ₗ m ∶ ω
Pₗ {A} (τ ∷ τᵢ) m = P A τ m × Pₗ τᵢ m

--data P where
--  base : ∀ {A} {m : Λ A} -> [] ⊩ m ∶ o -> NF m -> P o m
--  arr : ∀ {A B τ τ'} {m : Λ (A ⟶ B)} ->
--    [] ⊩ m ∶ (τ ~> τ') ->
--    (∀ {n : Λ A} -> Pₗ τ n -> Pₗ τ' (app m n)) ->
--    P (τ ~> τ') m

--data Pₗ where
--  nil : ∀ {A} {m : Λ A} -> [] ⊩ₗ m ∶ ω -> Pₗ ω m
--  cons : ∀ {A τ τᵢ} {m : Λ A} -> P τ m -> Pₗ τᵢ m -> Pₗ (τ ∷ τᵢ) m
