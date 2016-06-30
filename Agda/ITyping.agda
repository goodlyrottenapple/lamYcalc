module ITyping where

open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.List.Properties
open import Data.List.Any as LAny
open LAny.Membership-≡
open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality using (sym)

open import Core
open import Core-Lemmas
open import Typing
open import Typed-Core
open import ITyping-Core
open import Reduction using (_↝_)


wfI-Γ-exchange : ∀ {Γ x y τ₁ τ₂} -> Wf-ICtxt ((x , τ₁) ∷ (y , τ₂) ∷ Γ) -> Wf-ICtxt ((y , τ₂) ∷ (x , τ₁) ∷ Γ)
wfI-Γ-exchange (cons x∉ x₂ (cons x∉₁ x₃ wf-Γ)) = cons ((∉-∷ _ _ (λ y≡x → fv-x≠y _ _ x∉ (≡-sym y≡x)) x∉₁)) x₃ (cons (∉-∷-elim _ x∉) x₂ wf-Γ)


exchange-⊩ₗ : ∀ {A Γ x y τ₁ τ₂ X Y δ} {m : Λ A} -> ((x , τ₁ , X) ∷ (y , τ₂ , Y) ∷ Γ) ⊩ₗ m ∶ δ -> ((y , τ₂ , Y) ∷ (x , τ₁ , X) ∷ Γ) ⊩ₗ m ∶ δ
exchange-⊩ₗ {_} {Γ} {x} {y} {τ₁} {τ₂} {A} {B} {_} {m} x∷y∷Γ⊩ₗm∶δ = subₗ x∷y∷Γ⊩ₗm∶δ (⊆ₗ-refl (⊩ₗ-∷'ₗ x∷y∷Γ⊩ₗm∶δ)) (⊆Γ-⊆ (wfI-Γ-exchange (⊩ₗ-wf-Γ x∷y∷Γ⊩ₗm∶δ)) ⊆-aux)
  where
  ⊆-aux : (x , (τ₁ , A)) ∷ ((y , (τ₂ , B)) ∷ Γ) ⊆ (y , (τ₂ , B)) ∷ ((x , τ₁ , A) ∷ Γ)
  ⊆-aux (here px) = there (here px)
  ⊆-aux (there (here px)) = here px
  ⊆-aux (there (there ∈)) = there (there ∈)


subst-⊩ : ∀ {A B Γ τ τᵢ x} {m : Λ A} {n : Λ B} -> ΛTerm m -> ΛTerm n -> ((x , (τᵢ , B)) ∷ Γ) ⊩ m ∶ τ -> Γ ⊩ₗ n ∶ τᵢ ->
  Γ ⊩ (m Λ[ x ::= n ]) ∶ τ
subst-⊩ₗ : ∀ {A B Γ τ τᵢ x} {m : Λ A} {n : Λ B} -> ΛTerm m -> ΛTerm n -> ((x , (τᵢ , B)) ∷ Γ) ⊩ₗ m ∶ τ -> Γ ⊩ₗ n ∶ τᵢ ->
  Γ ⊩ₗ (m Λ[ x ::= n ]) ∶ τ

subst-⊩ {x = x} var trm-n (var {x = y} wf-Γ τᵢ∈Γ τ⊆τᵢ) Γ⊩ₗn∶τᵢ with x ≟ y
subst-⊩ {A} {B} var trm-n (var (cons x∉ x₂ wf-Γ) (here px) τ⊆τᵢ) Γ⊩ₗn∶τᵢ | yes refl with A ≟T B
subst-⊩ var trm-n (var (cons x∉ x₂ wf-Γ) (here refl) τ⊆τᵢ) Γ⊩ₗn∶τᵢ | yes refl | yes refl = ⊩ₗ-∈-⊩ (subₗ Γ⊩ₗn∶τᵢ τ⊆τᵢ (⊆Γ-⊆ wf-Γ (λ {x} z → z))) (here refl)
subst-⊩ var trm-n (var (cons x∉ x₂ wf-Γ) (here refl) τ⊆τᵢ) Γ⊩ₗn∶τᵢ | yes refl | no A≠B = ⊥-elim (A≠B refl)
subst-⊩ var trm-n (var (cons x∉ x₂ wf-Γ) (there τᵢ∈Γ) τ⊆τᵢ) Γ⊩ₗn∶τᵢ | yes refl = ⊥-elim (∉-dom x∉ τᵢ∈Γ)
subst-⊩ var trm-n (var (cons x∉ x₂ wf-Γ) (here refl) τ⊆τᵢ) Γ⊩ₗn∶τᵢ | no x≠y = ⊥-elim (x≠y refl)
subst-⊩ var trm-n (var (cons x∉ x₂ wf-Γ) (there τᵢ∈Γ) τ⊆τᵢ) Γ⊩ₗn∶τᵢ | no x≠y = var wf-Γ τᵢ∈Γ τ⊆τᵢ
subst-⊩ var trm-n (~>∩ x y z) Γ⊩ₗn∶τᵢ = ~>∩ (subst-⊩ var trm-n x Γ⊩ₗn∶τᵢ) (subst-⊩ var trm-n y Γ⊩ₗn∶τᵢ) z
subst-⊩ {B = B} {Γ} {τᵢ = τᵢ} {x} {n = n} (lam L cf) trm-n (abs {A} {τ = τ} {τ'} L' {m} cf' (arr τ∷' τ'∷')) Γ⊩ₗn∶τᵢ = abs (x ∷ L ++ L' ++ dom Γ) body (arr τ∷' τ'∷')
  where
  body : ∀ {x'} -> x' ∉ x ∷ L ++ L' ++ dom Γ -> ((x' , τ , A) ∷ Γ) ⊩ₗ Λ[ 0 >> (fv {A} x') ] (m Λ[ x ::= n ]) ∶ τ'
  body {x'} x'∉ rewrite
    Λsubst-open-var {τ'' = A} x' x n m (fv-x≠y _ _ x'∉) trm-n = subst-⊩ₗ {τᵢ = τᵢ}
    (cf (∉-∷-elim _ (∉-cons-l _ _ x'∉)))
    trm-n
    (exchange-⊩ₗ (cf' (∉-cons-l _ _ (∉-cons-r L _ (∉-∷-elim _ x'∉)))))
    (subₗ Γ⊩ₗn∶τᵢ (⊆ₗ-refl (⊩ₗ-∷'ₗ Γ⊩ₗn∶τᵢ)) (⊆Γ-⊆ (cons (∉-cons-r L' _ (∉-cons-r L _ (∉-∷-elim _ x'∉))) τ∷' (⊩ₗ-wf-Γ Γ⊩ₗn∶τᵢ)) (λ {x₂} → there)))

subst-⊩ (lam L cf) trm-n (~>∩ x∷Γ⊩m∶τ x∷Γ⊩m∶τ₁ x₁) Γ⊩ₗn∶τᵢ = ~>∩ (subst-⊩ (lam L cf) trm-n x∷Γ⊩m∶τ Γ⊩ₗn∶τᵢ) (subst-⊩ (lam L cf) trm-n x∷Γ⊩m∶τ₁ Γ⊩ₗn∶τᵢ) x₁
subst-⊩ (app trm-m trm-m₁) trm-n (app x∷Γ⊩m∶τ x₁ x₂ x₃) Γ⊩ₗn∶τᵢ = app (subst-⊩ trm-m trm-n x∷Γ⊩m∶τ Γ⊩ₗn∶τᵢ) (subst-⊩ₗ trm-m₁ trm-n x₁ Γ⊩ₗn∶τᵢ) x₂ x₃
subst-⊩ (app trm-m trm-m₁) trm-n (~>∩ x∷Γ⊩m∶τ x∷Γ⊩m∶τ₁ x₁) Γ⊩ₗn∶τᵢ = ~>∩ (subst-⊩ (app trm-m trm-m₁) trm-n x∷Γ⊩m∶τ Γ⊩ₗn∶τᵢ) (subst-⊩ (app trm-m trm-m₁) trm-n x∷Γ⊩m∶τ₁ Γ⊩ₗn∶τᵢ) x₁
subst-⊩ Y trm-n (Y (cons x∉ x₁ wf-Γ) x₂ x₃) Γ⊩ₗn∶τᵢ = Y wf-Γ x₂ x₃
subst-⊩ Y trm-n (~>∩ x∷Γ⊩m∶τ x∷Γ⊩m∶τ₁ x₁) Γ⊩ₗn∶τᵢ = ~>∩ (subst-⊩ Y trm-n x∷Γ⊩m∶τ Γ⊩ₗn∶τᵢ) (subst-⊩ Y trm-n x∷Γ⊩m∶τ₁ Γ⊩ₗn∶τᵢ) x₁

subst-⊩ₗ trm-m trm-n (nil (cons x∉ x₁ wf-Γ)) Γ⊩ₗn∶τᵢ = nil wf-Γ
subst-⊩ₗ trm-m trm-n (cons x₁ x∷Γ⊩ₗm∶τ) Γ⊩ₗn∶τᵢ = cons (subst-⊩ trm-m trm-n x₁ Γ⊩ₗn∶τᵢ) (subst-⊩ₗ trm-m trm-n x∷Γ⊩ₗm∶τ Γ⊩ₗn∶τᵢ)


∈-imp-∈dom : ∀ {Γ} {A : Type} {x : Atom} {τ : List IType} -> (x , (τ , A)) ∈ Γ -> x ∈ dom Γ
∈-imp-∈dom (here refl) = here refl
∈-imp-∈dom (there x,τ,A∈Γ) = there (∈-imp-∈dom x,τ,A∈Γ)

aux : ∀ {A B Γ τ τ' x y k} (m : Λ B) -> y ∉ dom Γ -> x ∉ ΛFV m -> y ∉ ΛFV m -> ¬(x ≡ y) ->
  ((x , τ , A) ∷ Γ) ⊩ Λ[ k >> fv {A} x ] m ∶ τ' -> ((y , τ , A) ∷ Γ) ⊩ Λ[ k >> fv {A} y ] m ∶ τ'
auxₗ : ∀ {A B Γ τ τ' x y k} (m : Λ B) -> y ∉ dom Γ -> x ∉ ΛFV m -> y ∉ ΛFV m -> ¬(x ≡ y) ->
  ((x , τ , A) ∷ Γ) ⊩ₗ Λ[ k >> fv {A} x ] m ∶ τ' -> ((y , τ , A) ∷ Γ) ⊩ₗ Λ[ k >> fv {A} y ] m ∶ τ'
aux (bv i) y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ' = {!   !}
aux (fv x₁) y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ' = {!   !}
aux {y = y} {k} (lam A' m) y∉Γ x∉FVm y∉FVm x≠y (abs L cf x₁) = abs L (λ {x} x∉L -> {!   !}) x₁
aux (lam A m) y∉Γ x∉FVm y∉FVm x≠y (~>∩ x∷Γ⊩m^'x∶τ' x∷Γ⊩m^'x∶τ'' x₁) = ~>∩ (aux (lam A m) y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ') (aux (lam A m) y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ'') x₁
aux (app m m₁) y∉Γ x∉FVm y∉FVm x≠y (app x∷Γ⊩m^'x∶τ' x₁ x₂ x₃) = app (aux m y∉Γ {!   !} {!   !} x≠y x∷Γ⊩m^'x∶τ') (auxₗ m₁ y∉Γ {!   !} {!   !} x≠y x₁) x₂ x₃
aux (app m m₁) y∉Γ x∉FVm y∉FVm x≠y (~>∩ x∷Γ⊩m^'x∶τ' x∷Γ⊩m^'x∶τ'' x₁) = ~>∩ (aux (app m m₁) y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ') (aux (app m m₁) y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ'') x₁
aux (Y _) y∉Γ x∉FVm y∉FVm x≠y(Y (cons x∉ x₁ wf-Γ) x₂ x₃) = Y (cons y∉Γ x₁ wf-Γ) x₂ x₃
aux {k = k} (Y B) y∉Γ x∉FVm y∉FVm x≠y (~>∩ x∷Γ⊩m^'x∶τ' x∷Γ⊩m^'x∶τ'' x₁) = ~>∩ (aux {k = k} (Y B) y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ') (aux {k = k} (Y B) y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ'') x₁

auxₗ m y∉Γ _ _ _ (nil (cons x∉ x₁ wf-Γ)) = nil (cons y∉Γ x₁ wf-Γ)
auxₗ m y∉Γ x∉FVm y∉FVm x≠y (cons x₁ x∷Γ⊩ₗm^'x∶τ') = cons (aux m y∉Γ x∉FVm y∉FVm x≠y x₁) (auxₗ m y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩ₗm^'x∶τ')

-- {-# TERMINATING #-}
-- subst-⊩-2 : ∀ {A B Γ τ x} {m : Λ A} {n : Λ B} -> ΛTerm m -> ΛTerm n -> x ∉ dom Γ -> Γ ⊩ (m Λ[ x ::= n ]) ∶ τ ->
--   ∃(λ τᵢ -> ( ((x , τᵢ , B) ∷ Γ) ⊩ m ∶ τ ) × ( Γ ⊩ₗ n ∶ τᵢ ))
-- subst-⊩ₗ-2 : ∀ {A B Γ τ x} {m : Λ A} {n : Λ B} -> ΛTerm m -> ΛTerm n -> x ∉ dom Γ -> Γ ⊩ₗ (m Λ[ x ::= n ]) ∶ τ ->
--   ∃(λ τᵢ -> ( ((x , τᵢ , B) ∷ Γ) ⊩ₗ m ∶ τ ) × ( Γ ⊩ₗ n ∶ τᵢ ))
--
-- subst-⊩-2 {A} {B} {x = x} (var {x = y}) trm-n x∉Γ Γ⊩m[x::=n] with x ≟ y | A ≟T B
-- subst-⊩-2 {τ = τ} var trm-n x∉Γ Γ⊩m[x::=n] | yes refl | yes refl = (∩' τ) ,
--   (var (cons x∉Γ (cons (⊩-∷' Γ⊩m[x::=n]) nil) (⊩-wf-Γ Γ⊩m[x::=n])) (here refl) (⊆ₗ-refl (cons (⊩-∷' Γ⊩m[x::=n]) nil)) ,
--   (cons Γ⊩m[x::=n] (nil (⊩-wf-Γ Γ⊩m[x::=n]))))
-- subst-⊩-2 var trm-n x∉Γ Γ⊩m[x::=n] | yes refl | no _ = ⊥-elim (x∉Γ (contr Γ⊩m[x::=n]))
--   where
--   contr : ∀ {Γ A x τ} -> Γ ⊩ (fv {A} x) ∶ τ -> x ∈ dom Γ
--   contr (var wf-Γ τᵢ∈Γ τ⊆τᵢ) = ∈-imp-∈dom τᵢ∈Γ
--   contr (~>∩ Γ⊩x∶τ Γ⊩x∶τ₁ x₁) = contr Γ⊩x∶τ₁
--
-- ... | no _ | _ = ω , ((sub Γ⊩m[x::=n] (⊆-refl (⊩-∷' Γ⊩m[x::=n])) (⊆Γ-⊆ (cons x∉Γ nil (⊩-wf-Γ Γ⊩m[x::=n])) (λ {x₁} → there))) , (nil (⊩-wf-Γ Γ⊩m[x::=n])))
-- subst-⊩-2 {A ⟶ B} {C} {Γ} {τ ~> τ'} {x} {_} {n} (lam L {m} cf) trm-n x∉Γ (abs L' cf' (arr τ∷' τ'∷')) = τᵢ , (abs {!   !} {!   !} {!   !}) , {!   !}
--   where
--   x' = ∃fresh-impl (x ∷ L ++ L' ++ dom Γ)
--
--   x'∉ : x' ∉ (x ∷ L ++ L' ++ dom Γ)
--   x'∉ = ∃fresh-impl-spec (x ∷ L ++ L' ++ dom Γ)
--
--   ih' : ((x' , τ , A) ∷ Γ) ⊩ₗ (Λ[ 0 >> fv {A} x' ] m) Λ[ x ::= n ] ∶ τ'
--   ih' rewrite Λsubst-open-var2 {τ'' = A} x' x n m (fv-x≠y _ _ x'∉) trm-n = cf' (∉-cons-l L' _ (∉-cons-r L _ (∉-∷-elim _ x'∉)))
--
--   ih : ∃(λ τᵢ₁ ->
--     (((x , τᵢ₁ , C) ∷ (suc (x ⊔ ∪ (L ++ L' ++ dom Γ)) , τ , A) ∷ Γ) ⊩ₗ Λ[ 0 >> fv x' ] m ∶ τ') × (((suc (x ⊔ ∪ (L ++ L' ++ dom Γ)) , τ , A) ∷ Γ) ⊩ₗ n ∶ τᵢ₁))
--   ih = subst-⊩ₗ-2 (cf (∉-cons-l L _ (∉-∷-elim _ x'∉))) trm-n (∉-∷ _ (dom Γ) (λ x₂ -> fv-x≠y _ _ x'∉ (sym x₂)) x∉Γ) ih'
--
--   τᵢ = proj₁ ih
--
--   -- x∷x'∷Γ⊩ₗm^x∶τ' : ((x , τᵢ , C) ∷ (x' , τ , A) ∷ Γ) ⊩ₗ Λ[ 0 >> fv x' ] m ∶ τ'
--   -- x∷x'∷Γ⊩ₗm^x∶τ' = proj₁ (proj₂ ih)
--
--   -- helper₁ : ∀ {x'} -> x' ∉ x ∷ L ++ L' ++ dom Γ -> ((x' , τ , A) ∷ Γ) ⊩ₗ (Λ[ 0 >> fv {A} x' ] m) Λ[ x ::= n ] ∶ τ'
--   -- helper₁ {x'} x'∉ rewrite Λsubst-open-var2 {τ'' = A} x' x n m (fv-x≠y _ _ x'∉) trm-n = cf' (∉-cons-l L' _ (∉-cons-r L _ (∉-∷-elim _ x'∉)))
--   --
--   -- helper₂ : ∀ {x'} -> x' ∉ x ∷ L ++ L' ++ dom Γ -> ∃(λ τᵢ ->
--   --   (((x , τᵢ , C) ∷ (x' , τ , A) ∷ Γ) ⊩ₗ Λ[ 0 >> fv x' ] m ∶ τ') × (((x' , τ , A) ∷ Γ) ⊩ₗ n ∶ τᵢ))
--   -- helper₂ {x'} x'∉ = subst-⊩ₗ-2 (cf (∉-cons-l L _ (∉-∷-elim _ x'∉))) trm-n (∉-∷ _ (dom Γ) (λ x₂ -> fv-x≠y _ _ x'∉ (sym x₂)) x∉Γ) ih'
--   --   where
--   --   ih' = helper₁ x'∉
--
--
-- subst-⊩-2 {B = B} {Γ} {x = x} (lam L {e = m} cf) trm-n x∉Γ (~>∩ Γ⊩m[x::=n] Γ⊩m[x::=n]₁ x₁) = τₗ ++ τᵣ ,
--   sub
--     (~>∩
--       (sub {Γ' = ((x , τₗ ++ τᵣ , B) ∷ Γ)} x∷Γ⊩m∶τₗ (⊆-refl (⊩-∷' Γ⊩m[x::=n])) ⊆Γₗ)
--       (sub x∷Γ⊩m∶τᵣ (⊆-refl (⊩-∷' Γ⊩m[x::=n]₁)) ⊆Γᵣ)
--       (⊆ₗ-refl (++-∷'ₗ (proj₂ (arr' (⊩-∷' Γ⊩m[x::=n]))) (proj₂ (arr' (⊩-∷' Γ⊩m[x::=n]₁))))))
--     (arr (⊆ₗ-refl τ∷) x₁ (arr τ∷ (⊆ₗ-∷'ₗ-l x₁)) (arr τ∷ (⊆ₗ-∷'ₗ-r x₁)))
--     (⊆Γ-⊆ wf-x∷Γ (λ x₃ → x₃)) ,
--   ⊩ₗ-++ Γ⊩n∶τₗ Γ⊩n∶τᵣ
--   where
--   ihₗ = subst-⊩-2 (lam L {e = m} cf) trm-n x∉Γ Γ⊩m[x::=n]
--   ihᵣ = subst-⊩-2 (lam L {e = m} cf) trm-n x∉Γ Γ⊩m[x::=n]₁
--   τₗ = proj₁ ihₗ
--   τᵣ = proj₁ ihᵣ
--   x∷Γ⊩m∶τₗ = proj₁ (proj₂ ihₗ)
--   x∷Γ⊩m∶τᵣ = proj₁ (proj₂ ihᵣ)
--   Γ⊩n∶τₗ = proj₂ (proj₂ ihₗ)
--   Γ⊩n∶τᵣ = proj₂ (proj₂ ihᵣ)
--
--   τₗ++τᵣ∷' : (τₗ ++ τᵣ) ∷'ₗ B
--   τₗ++τᵣ∷' = ++-∷'ₗ (⊩ₗ-∷'ₗ Γ⊩n∶τₗ) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ)
--
--   wf-x∷Γ : Wf-ICtxt ((x , τₗ ++ τᵣ , B) ∷ Γ)
--   wf-x∷Γ = cons x∉Γ τₗ++τᵣ∷' (⊩-wf-Γ Γ⊩m[x::=n]₁)
--
--   ⊆Γₗ : ((x , τₗ , B) ∷ Γ) ⊆Γ ((x , τₗ ++ τᵣ , B) ∷ Γ)
--   ⊆Γₗ = cons ((τₗ ++ τᵣ) , ((here refl) , ⊆ₗ++-l' (⊩ₗ-∷'ₗ Γ⊩n∶τₗ) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))
--
--   ⊆Γᵣ : ((x , τᵣ , B) ∷ Γ) ⊆Γ ((x , τₗ ++ τᵣ , B) ∷ Γ)
--   ⊆Γᵣ = cons ((τₗ ++ τᵣ) , ((here refl) , ⊆ₗ++-r (nil (⊩ₗ-∷'ₗ Γ⊩n∶τₗ)) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))
--
--   τ∷ = proj₁ (arr' (⊩-∷' Γ⊩m[x::=n]₁))
--
-- subst-⊩-2 {B = B} {Γ} {x = x} (app trm-m trm-m₁) trm-n x∉Γ (app Γ⊩e₁[x::=n] Γ⊩ₗe₂[x::=n] x₂ x₃) = τₗ ++ τᵣ ,
--   (app (sub x∷Γ⊩m∶τₗ (⊆-refl (⊩-∷' Γ⊩e₁[x::=n])) ⊆Γₗ) (subₗ x∷Γ⊩m∶τᵣ (⊆ₗ-refl (⊩ₗ-∷'ₗ Γ⊩ₗe₂[x::=n])) ⊆Γᵣ) x₂ x₃) ,
--   (⊩ₗ-++ Γ⊩n∶τₗ Γ⊩n∶τᵣ)
--   where
--   ihₗ = subst-⊩-2 trm-m trm-n x∉Γ Γ⊩e₁[x::=n]
--   ihᵣ = subst-⊩ₗ-2 trm-m₁ trm-n x∉Γ Γ⊩ₗe₂[x::=n]
--   τₗ = proj₁ ihₗ
--   τᵣ = proj₁ ihᵣ
--   x∷Γ⊩m∶τₗ = proj₁ (proj₂ ihₗ)
--   x∷Γ⊩m∶τᵣ = proj₁ (proj₂ ihᵣ)
--   Γ⊩n∶τₗ = proj₂ (proj₂ ihₗ)
--   Γ⊩n∶τᵣ = proj₂ (proj₂ ihᵣ)
--
--   τₗ++τᵣ∷' : (τₗ ++ τᵣ) ∷'ₗ B
--   τₗ++τᵣ∷' = ++-∷'ₗ (⊩ₗ-∷'ₗ Γ⊩n∶τₗ) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ)
--
--   wf-x∷Γ : Wf-ICtxt ((x , τₗ ++ τᵣ , B) ∷ Γ)
--   wf-x∷Γ = cons x∉Γ τₗ++τᵣ∷' (⊩-wf-Γ Γ⊩e₁[x::=n])
--
--   ⊆Γₗ : ((x , τₗ , B) ∷ Γ) ⊆Γ ((x , τₗ ++ τᵣ , B) ∷ Γ)
--   ⊆Γₗ = cons ((τₗ ++ τᵣ) , ((here refl) , ⊆ₗ++-l' (⊩ₗ-∷'ₗ Γ⊩n∶τₗ) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))
--
--   ⊆Γᵣ : ((x , τᵣ , B) ∷ Γ) ⊆Γ ((x , τₗ ++ τᵣ , B) ∷ Γ)
--   ⊆Γᵣ = cons ((τₗ ++ τᵣ) , ((here refl) , ⊆ₗ++-r (nil (⊩ₗ-∷'ₗ Γ⊩n∶τₗ)) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))
--
-- subst-⊩-2 {B = B} {Γ} {x = x} (app trm-m trm-m₁) trm-n x∉Γ (~>∩ Γ⊩m[x::=n] Γ⊩m[x::=n]₁ x₁) = τₗ ++ τᵣ ,
--   sub
--     (~>∩
--       (sub {Γ' = ((x , τₗ ++ τᵣ , B) ∷ Γ)} x∷Γ⊩m∶τₗ (⊆-refl (⊩-∷' Γ⊩m[x::=n])) ⊆Γₗ)
--       (sub x∷Γ⊩m∶τᵣ (⊆-refl (⊩-∷' Γ⊩m[x::=n]₁)) ⊆Γᵣ)
--       (⊆ₗ-refl (++-∷'ₗ (proj₂ (arr' (⊩-∷' Γ⊩m[x::=n]))) (proj₂ (arr' (⊩-∷' Γ⊩m[x::=n]₁))))))
--     (arr (⊆ₗ-refl τ∷) x₁ (arr τ∷ (⊆ₗ-∷'ₗ-l x₁)) (arr τ∷ (⊆ₗ-∷'ₗ-r x₁)))
--     (⊆Γ-⊆ wf-x∷Γ (λ x₃ → x₃)) ,
--   ⊩ₗ-++ Γ⊩n∶τₗ Γ⊩n∶τᵣ
--   where
--   ihₗ = subst-⊩-2 (app trm-m trm-m₁) trm-n x∉Γ Γ⊩m[x::=n]
--   ihᵣ = subst-⊩-2 (app trm-m trm-m₁) trm-n x∉Γ Γ⊩m[x::=n]₁
--   τₗ = proj₁ ihₗ
--   τᵣ = proj₁ ihᵣ
--   x∷Γ⊩m∶τₗ = proj₁ (proj₂ ihₗ)
--   x∷Γ⊩m∶τᵣ = proj₁ (proj₂ ihᵣ)
--   Γ⊩n∶τₗ = proj₂ (proj₂ ihₗ)
--   Γ⊩n∶τᵣ = proj₂ (proj₂ ihᵣ)
--
--   τₗ++τᵣ∷' : (τₗ ++ τᵣ) ∷'ₗ B
--   τₗ++τᵣ∷' = ++-∷'ₗ (⊩ₗ-∷'ₗ Γ⊩n∶τₗ) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ)
--
--   wf-x∷Γ : Wf-ICtxt ((x , τₗ ++ τᵣ , B) ∷ Γ)
--   wf-x∷Γ = cons x∉Γ τₗ++τᵣ∷' (⊩-wf-Γ Γ⊩m[x::=n]₁)
--
--   ⊆Γₗ : ((x , τₗ , B) ∷ Γ) ⊆Γ ((x , τₗ ++ τᵣ , B) ∷ Γ)
--   ⊆Γₗ = cons ((τₗ ++ τᵣ) , ((here refl) , ⊆ₗ++-l' (⊩ₗ-∷'ₗ Γ⊩n∶τₗ) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))
--
--   ⊆Γᵣ : ((x , τᵣ , B) ∷ Γ) ⊆Γ ((x , τₗ ++ τᵣ , B) ∷ Γ)
--   ⊆Γᵣ = cons ((τₗ ++ τᵣ) , ((here refl) , ⊆ₗ++-r (nil (⊩ₗ-∷'ₗ Γ⊩n∶τₗ)) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))
--
--   τ∷ = proj₁ (arr' (⊩-∷' Γ⊩m[x::=n]₁))
--
-- subst-⊩-2 Y trm-n x∉Γ Γ⊩m[x::=n] = ω , (sub Γ⊩m[x::=n] (⊆-refl (⊩-∷' Γ⊩m[x::=n])) (⊆Γ-⊆ (cons x∉Γ nil (⊩-wf-Γ Γ⊩m[x::=n])) (λ {x} → there))) , (nil (⊩-wf-Γ Γ⊩m[x::=n]))
--
-- subst-⊩ₗ-2 trm-m trm-n x∉Γ (nil wf-Γ) = ω , ((nil (cons x∉Γ nil wf-Γ)) , (nil wf-Γ))
-- subst-⊩ₗ-2 {B = B} {Γ} {x = x} trm-m trm-n x∉Γ (cons x' Γ⊩ₗm∶τ) =
--   τ ++ τₗ , (cons (sub x∷Γ⊩m∶τ (⊆-refl (⊩-∷' x')) ⊆Γ') (subₗ x∷Γ⊩m∶τₗ (⊆ₗ-refl (⊩ₗ-∷'ₗ Γ⊩ₗm∶τ)) ⊆Γₗ)) , ⊩ₗ-++ Γ⊩n∶τ Γ⊩n∶τₗ
--   where
--   ih = subst-⊩-2 trm-m trm-n x∉Γ x'
--   ihₗ = subst-⊩ₗ-2 trm-m trm-n x∉Γ Γ⊩ₗm∶τ
--   τ = proj₁ ih
--   τₗ = proj₁ ihₗ
--   x∷Γ⊩m∶τ = proj₁ (proj₂ ih)
--   x∷Γ⊩m∶τₗ = proj₁ (proj₂ ihₗ)
--   Γ⊩n∶τ = proj₂ (proj₂ ih)
--   Γ⊩n∶τₗ = proj₂ (proj₂ ihₗ)
--
--   τ++τₗ∷' : (τ ++ τₗ) ∷'ₗ B
--   τ++τₗ∷' = ++-∷'ₗ (⊩ₗ-∷'ₗ Γ⊩n∶τ) (⊩ₗ-∷'ₗ Γ⊩n∶τₗ)
--
--   wf-x∷Γ : Wf-ICtxt ((x , τ ++ τₗ , B) ∷ Γ)
--   wf-x∷Γ = cons x∉Γ τ++τₗ∷' (⊩-wf-Γ x')
--
--   ⊆Γ' : ((x , τ , B) ∷ Γ) ⊆Γ ((x , τ ++ τₗ , B) ∷ Γ)
--   ⊆Γ' = cons ((τ ++ τₗ) , ((here refl) , ⊆ₗ++-l' (⊩ₗ-∷'ₗ Γ⊩n∶τ) (⊩ₗ-∷'ₗ Γ⊩n∶τₗ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))
--
--   ⊆Γₗ : ((x , τₗ , B) ∷ Γ) ⊆Γ ((x , τ ++ τₗ , B) ∷ Γ)
--   ⊆Γₗ = cons ((τ ++ τₗ) , ((here refl) , ⊆ₗ++-r (nil (⊩ₗ-∷'ₗ Γ⊩n∶τ)) (⊩ₗ-∷'ₗ Γ⊩n∶τₗ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))

-----------------------------------------------------------------

^-⊩-2 : ∀ {A B Γ τ} {m : Λ B} {n : Λ A} -> ΛTerm (lam A m) -> ΛTerm n -> Γ ⊩ (Λ[ 0 >> n ] m) ∶ τ ->
  ∃(λ τᵢ -> (Γ ⊩ lam A m ∶ (τᵢ ~> ∩' τ) × ( Γ ⊩ₗ n ∶ τᵢ )))
^-⊩-2 trm-lam-m trm-n Γ⊩m^n∶τ = {!   !}


-- ω , ((abs (dom Γ) (λ x∉L → cons {!   !} (nil (cons x∉L nil {!   !}))) (arr nil {!   !})) , (nil {!  !}))

-------------------------------------------------------------------------------


Γ⊩Ym-max : ∀ {A Γ} {m : Λ (A ⟶ A)} {τ} -> Γ ⊩ app (Y A) m ∶ τ -> ∃(λ τ' -> Γ ⊩ₗ m ∶ ∩' (τ' ~> τ') × (∩' τ) ⊆ₗ[ A ] τ')
Γ⊩Ym-max {A} {Γ} {m} {τ} (app Γ⊩Y∶τ₁~>τ₂ Γ⊩ₗm∶τ₁ τ⊆ₗτ₂ τ₁∷'A⟶A) = τ' , (subₗ Γ⊩ₗm∶τ₁ τ'~>τ'⊆ₗτ₁ (⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗm∶τ₁) (λ {x} z → z)) , ⊆ₗ-trans τ⊆ₗτ₂ τ₂⊆ₗτ)
  where
  body = Y-inv Γ⊩Y∶τ₁~>τ₂
  τ' = proj₁ body
  τ'~>τ'⊆ₗτ₁ = proj₁ (proj₂ body)
  τ₂⊆ₗτ = proj₂ (proj₂ body)

Γ⊩Ym-max {A ⟶ B} {Γ} {m} (~>∩ {τ = τ} {τ₁} {τ₂} {τ₁τ₂} Γ⊩Ym∶τ~>τ₁ Γ⊩Ym∶τ~>τ₂ τ₁τ₂⊆ₗτ₁++τ₂) =
  (τ₁' ++ τ₂') ,
  (subₗ (cons (⊩ₗ-∈-⊩ Γ⊩ₗm∶τ₁'~>τ₁' (here refl)) Γ⊩ₗm∶τ₂'~>τ₂') (~>∩' τ₁'∷ τ₂'∷) (⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗm∶τ₁'~>τ₁') (λ {x} z → z)) ,
  ⊆ₗ-trans
    (⊆ₗ-trans
      (cons ((τ ~> (τ₁ ++ τ₂)) , ((here refl) , (arr (⊆ₗ-refl τ∷') τ₁τ₂⊆ₗτ₁++τ₂ (arr τ∷' τ₁τ₂∷') (arr τ∷' τ₁++τ₂∷')))) (nil τ+∷))
      (~>∩ τ+∷))
    (mon τ~>τ₁⊆ₗτ₁' τ~>τ₂⊆ₗτ₂'))

  where
  ihₗ : ∃(λ τ₁' -> Γ ⊩ₗ m ∶ ∩' (τ₁' ~> τ₁') × (∩' (τ ~> τ₁)) ⊆ₗ[ A ⟶ B ] τ₁')
  ihₗ = Γ⊩Ym-max Γ⊩Ym∶τ~>τ₁

  τ₁' = proj₁ ihₗ
  Γ⊩ₗm∶τ₁'~>τ₁' = proj₁ (proj₂ ihₗ)
  τ~>τ₁⊆ₗτ₁' = proj₂ (proj₂ ihₗ)

  ihᵣ : ∃(λ τ₂' -> Γ ⊩ₗ m ∶ ∩' (τ₂' ~> τ₂') × (∩' (τ ~> τ₂)) ⊆ₗ[ A ⟶ B ] τ₂')
  ihᵣ = Γ⊩Ym-max Γ⊩Ym∶τ~>τ₂

  τ₂' = proj₁ ihᵣ
  Γ⊩ₗm∶τ₂'~>τ₂' = proj₁ (proj₂ ihᵣ)
  τ~>τ₂⊆ₗτ₂' = proj₂ (proj₂ ihᵣ)

  τ₁'∷ = ⊆ₗ-∷'ₗ-r τ~>τ₁⊆ₗτ₁'
  τ₂'∷ = ⊆ₗ-∷'ₗ-r τ~>τ₂⊆ₗτ₂'
  τ∷' = proj₁ (arr' (⊩-∷' Γ⊩Ym∶τ~>τ₂))

  τ₁τ₂∷' = ⊆ₗ-∷'ₗ-l τ₁τ₂⊆ₗτ₁++τ₂
  τ₁++τ₂∷' = ⊆ₗ-∷'ₗ-r τ₁τ₂⊆ₗτ₁++τ₂

  τ+∷ : ((τ ~> (τ₁ ++ τ₂)) ∷ []) ∷'ₗ (A ⟶ B)
  τ+∷ = cons (arr τ∷' τ₁++τ₂∷') nil


¬ω⊆-impl¬ω : ∀ {A τ τ'} -> ¬(τ ≡ ω) -> τ ⊆ₗ[ A ] τ' -> ¬(τ' ≡ ω)
¬ω⊆-impl¬ω τ≠ω (nil x) τ'≡ω = τ≠ω refl
¬ω⊆-impl¬ω τ≠ω (cons (_ , () , _) τ⊆ₗτ') refl
¬ω⊆-impl¬ω τ≠ω (~>∩ x) ()
¬ω⊆-impl¬ω τ≠ω (⊆ₗ-trans τ⊆ₗτ' τ⊆ₗτ'') τ'≡ω = ¬ω⊆-impl¬ω (¬ω⊆-impl¬ω τ≠ω τ⊆ₗτ') τ⊆ₗτ'' τ'≡ω


-- ~>∩ₗ : ∀ {A B Γ} {m : Λ (A ⟶ B)} {τ τ' τ''} -> Γ ⊩ₗ m ∶ ((τ ~> τ') ∷ ∩' (τ ~> τ'')) -> Γ ⊩ₗ m ∶ ∩' (τ ~> (τ' ++ τ''))
-- ~>∩ₗ (cons Γ⊩ₗm∶τ~>τ' (cons Γ⊩ₗm∶τ~>τ'' (nil wf-Γ))) = cons (~>∩ Γ⊩ₗm∶τ~>τ' Γ⊩ₗm∶τ~>τ'' (⊆ₗ-refl {!   !})) (nil wf-Γ)


Γ⊩ₗYm-max : ∀ {A Γ} {m : Λ (A ⟶ A)} {τ} -> ¬(τ ≡ ω) -> Γ ⊩ₗ app (Y A) m ∶ τ -> ∃(λ τ' -> Γ ⊩ₗ m ∶ ∩' (τ' ~> τ') × τ ⊆ₗ[ A ] τ')
Γ⊩ₗYm-max τ≠ω (nil wf-Γ) = ⊥-elim (τ≠ω refl)
Γ⊩ₗYm-max {A} {Γ} {m} {τ ∷ τᵢ} τ≠ω (cons x Γ⊩ₗYm∶τ) with τᵢ ≟TIₗ ω
Γ⊩ₗYm-max {A} {Γ} {m} {τ ∷ .[]} τ≠ω (cons x Γ⊩ₗYm∶τ) | yes refl = Γ⊩Ym-max x
Γ⊩ₗYm-max {A} {Γ} {m} {τ ∷ τᵢ} τ≠ω (cons x Γ⊩ₗYm∶τ) | no τᵢ≠ω =
  τ' ++ τᵢ' ,
  subₗ Γ⊩ₗm∶ττᵢ'~>τ'ττᵢ'~>τᵢ' (~>∩ (cons (arr (∷'ₗ-++ τ'∷'A τᵢ'∷'A) (∷'ₗ-++ τ'∷'A τᵢ'∷'A)) nil)) (⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗYm∶τ) (λ {x} z → z)) ,
  mon τ⊆τ' τᵢ⊆τᵢ'
  where
  ih : ∃(λ τᵢ' -> Γ ⊩ₗ m ∶ ∩' (τᵢ' ~> τᵢ') × τᵢ ⊆ₗ[ A ] τᵢ')
  ih = Γ⊩ₗYm-max τᵢ≠ω Γ⊩ₗYm∶τ

  τᵢ' = proj₁ ih
  Γ⊩ₗm∶τᵢ'~>τᵢ' : Γ ⊩ₗ m ∶ ∩' (τᵢ' ~> τᵢ')
  Γ⊩ₗm∶τᵢ'~>τᵢ' = proj₁ (proj₂ ih)

  τᵢ⊆τᵢ' = proj₂ (proj₂ ih)

  body : ∃(λ τ' -> Γ ⊩ₗ m ∶ ∩' (τ' ~> τ') × ∩' τ ⊆ₗ[ A ] τ')
  body = Γ⊩Ym-max x

  τ' = proj₁ body
  Γ⊩ₗm∶τ'~>τ' : Γ ⊩ₗ m ∶ ∩' (τ' ~> τ')
  Γ⊩ₗm∶τ'~>τ' = proj₁ (proj₂ body)

  τ⊆τ' = proj₂ (proj₂ body)

  τ'∷'A = ⊆ₗ-∷'ₗ-r τ⊆τ'
  τᵢ'∷'A = ⊆ₗ-∷'ₗ-r τᵢ⊆τᵢ'

  Γ⊩ₗm∶ττᵢ'~>τ'ττᵢ'~>τᵢ' : Γ ⊩ₗ m ∶ (∩' ((τ' ++ τᵢ') ~> τ') ++ ∩' ((τ' ++ τᵢ') ~> τᵢ'))
  Γ⊩ₗm∶ττᵢ'~>τ'ττᵢ'~>τᵢ' = ⊩++ {τᵢ = ∩' ((τ' ++ τᵢ') ~> τ')} {∩' ((τ' ++ τᵢ') ~> τᵢ')}
    (subₗ Γ⊩ₗm∶τ'~>τ'
      (cons
        ( (τ' ~> τ') ,
          ((here refl) ,
          (arr (⊆ₗ-⊆ (λ x₂ → ∈-cons-l _ x₂) (∷'ₗ-++ τ'∷'A τᵢ'∷'A)) (⊆ₗ-refl τ'∷'A) (arr (∷'ₗ-++ τ'∷'A τᵢ'∷'A) τ'∷'A) (arr τ'∷'A τ'∷'A))))
        (nil (cons (arr τ'∷'A τ'∷'A) nil)))
      (⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗYm∶τ) (λ {x} z → z)))
    (subₗ Γ⊩ₗm∶τᵢ'~>τᵢ'
      (cons
        ( (τᵢ' ~> τᵢ') ,
          (here refl ,
          arr (⊆ₗ-⊆ (λ x₂ → ∈-cons-r τ' x₂) (∷'ₗ-++ τ'∷'A τᵢ'∷'A)) (⊆ₗ-refl τᵢ'∷'A) (arr (∷'ₗ-++ τ'∷'A τᵢ'∷'A) τᵢ'∷'A) (arr τᵢ'∷'A τᵢ'∷'A)))
        (nil (cons (arr τᵢ'∷'A τᵢ'∷'A) nil)))
      (⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗYm∶τ) (λ {x} z → z)))


Γ⊩mYm∶τ->Γ⊩Ym∶τ : ∀ {A Γ m τ} -> Γ ⊩ app m (app (Y A) m) ∶ τ -> Γ ⊩ app (Y A) m ∶ τ
Γ⊩mYm∶τ->Γ⊩Ym∶τ {A} {Γ} {τ = τ} (app {s = m} {τ₁ = []} {τᵢ} Γ⊩m∶τᵢ'~>τᵢ (nil wf-Γ) τ⊆τᵢ τᵢ'∷A) = app
  (Y {τ = ∩' τ} {(ω ~> ∩' τ) ∷ []} {∩' τ}
    wf-Γ
    (cons (([] ~> ∩' τ) , ((here refl) , (arr (nil τ∷A) (⊆ₗ-refl τ∷A) (arr τ∷A τ∷A) (arr τᵢ'∷A τ∷A)))) (nil (cons (arr τᵢ'∷A τ∷A) nil)))
    (⊆ₗ-refl τ∷A))
  (cons (sub Γ⊩m∶τᵢ'~>τᵢ (arr (nil τᵢ'∷A) τ⊆τᵢ (arr τᵢ'∷A τ∷A) (arr τᵢ'∷A (⊆ₗ-∷'ₗ-r τ⊆τᵢ))) (⊆Γ-⊆ wf-Γ (λ {x} z → z))) (nil wf-Γ))
  (⊆ₗ-refl τ∷A)
  (cons (arr τᵢ'∷A τ∷A) nil)

  where
  τ∷A = ⊆ₗ-∷'ₗ-l τ⊆τᵢ

Γ⊩mYm∶τ->Γ⊩Ym∶τ {A} {Γ} {τ = τ} (app {s = m} {τ₁ = τ' ∷ τᵢ'} {τᵢ} Γ⊩m∶τᵢ'~>τᵢ (cons x₁ Γ⊩ₗYm∶τ'ᵢ₁) τ⊆τᵢ τᵢ'∷A) = app
  (Y {τ = [ τ ] ++ τ''} {∩' (τ'' ~> ([ τ ] ++ τ''))} {∩' τ}
    (⊩ₗ-wf-Γ Γ⊩ₗYm∶τ'ᵢ₁)
    (cons
      (
        (τ'' ~> ([ τ ] ++ τ'')) ,
        here refl ,
        arr
          (⊆ₗ-⊆ (λ x₂ → ∈-cons-r [ τ ] x₂) (cons τ∷'A τ''∷'A))
          (⊆ₗ-refl (cons τ∷'A τ''∷'A))
          (arr (cons τ∷'A τ''∷'A) (cons τ∷'A τ''∷'A))
          (arr τ''∷'A (cons τ∷'A τ''∷'A)))
      (nil (cons (arr τ''∷'A (cons τ∷'A τ''∷'A)) nil)))
    (cons (τ , (here refl , ⊆-refl τ∷'A)) (nil (cons τ∷'A τ''∷'A))))
  Γ⊩ₗm∶τ''~>τ++τ''
  (⊆ₗ-refl (cons τ∷'A nil))
  (cons (arr τ''∷'A (cons τ∷'A τ''∷'A)) nil)

  where
  τᵢ'' = τ' ∷ τᵢ'
  body₁ : ∃(λ τ'' -> Γ ⊩ₗ m ∶ ∩' (τ'' ~> τ'') × τᵢ'' ⊆ₗ[ A ] τ'')
  body₁ = Γ⊩ₗYm-max (λ ()) (cons x₁ Γ⊩ₗYm∶τ'ᵢ₁)

  τ'' = proj₁ body₁

  Γ⊩ₗm∶τ''~>τ'' : Γ ⊩ₗ m ∶ ∩' (τ'' ~> τ'')
  Γ⊩ₗm∶τ''~>τ'' = proj₁ (proj₂ body₁)

  τᵢ''⊆τ'' = proj₂ (proj₂ body₁)
  τ''∷'A = ⊆ₗ-∷'ₗ-r τᵢ''⊆τ''
  τᵢ''∷'A = ⊆ₗ-∷'ₗ-l τᵢ''⊆τ''

  τ∷'A : τ ∷' A
  τ∷'A = ∷'ₗ-∈ (here refl) (⊆ₗ-∷'ₗ-l τ⊆τᵢ)

  Γ⊩m∶τ''~>τ : Γ ⊩ m ∶ (τ'' ~> ∩' τ)
  Γ⊩m∶τ''~>τ = sub Γ⊩m∶τᵢ'~>τᵢ (arr τᵢ''⊆τ'' τ⊆τᵢ (arr τ''∷'A (⊆ₗ-∷'ₗ-l τ⊆τᵢ)) (arr τᵢ''∷'A (⊆ₗ-∷'ₗ-r τ⊆τᵢ))) (⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗYm∶τ'ᵢ₁) (λ {x} z → z))

  Γ⊩ₗm∶τ''~>τ++τ'' : Γ ⊩ₗ m ∶ ∩' (τ'' ~> ([ τ ] ++ τ''))
  Γ⊩ₗm∶τ''~>τ++τ'' = subₗ (cons Γ⊩m∶τ''~>τ Γ⊩ₗm∶τ''~>τ'') (~>∩ (cons (arr τ''∷'A (cons τ∷'A τ''∷'A)) nil)) (⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗYm∶τ'ᵢ₁) (λ {x} z → z))

Γ⊩mYm∶τ->Γ⊩Ym∶τ (~>∩ Γ⊩mYm∶τ Γ⊩mYm∶τ₁ z) = ~>∩ (Γ⊩mYm∶τ->Γ⊩Ym∶τ Γ⊩mYm∶τ) (Γ⊩mYm∶τ->Γ⊩Ym∶τ Γ⊩mYm∶τ₁) z


⊩->β : ∀ {A Γ} {m m' : Λ A} {τ} -> Γ ⊩ m' ∶ τ -> m ->Λβ m' -> Γ ⊩ m ∶ τ
⊩->βₗ : ∀ {A Γ} {m m' : Λ A} {τ} -> Γ ⊩ₗ m' ∶ τ -> m ->Λβ m' -> Γ ⊩ₗ m ∶ τ

⊩->β Γ⊩m'∶τ (redL x m->βm') = ⊩->β-redL Γ⊩m'∶τ m->βm'
  where
  ⊩->β-redL : ∀ {A B Γ} {m m' : Λ (A ⟶ B)} {n : Λ A} {τ} -> Γ ⊩ app m' n ∶ τ -> m ->Λβ m' -> Γ ⊩ app m n ∶ τ
  ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂ x₃) (redL x₄ m->Λβm') = app (⊩->β-redL Γ⊩m'n∶τ m->Λβm') x₁ x₂ x₃
  ⊩->β-redL (~>∩ Γ⊩m'n∶τ Γ⊩m'n∶τ₁ x₁) (redL x₂ m->Λβm') = ~>∩ (⊩->β-redL Γ⊩m'n∶τ (redL x₂ m->Λβm')) (⊩->β-redL Γ⊩m'n∶τ₁ (redL x₂ m->Λβm')) x₁
  ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂ x₃) (redR x₄ m->Λβm') = app (⊩->β Γ⊩m'n∶τ (redR x₄ m->Λβm')) x₁ x₂ x₃
  ⊩->β-redL (~>∩ Γ⊩m'n∶τ Γ⊩m'n∶τ₁ x₁) (redR x₂ m->Λβm') = ~>∩ (⊩->β-redL Γ⊩m'n∶τ (redR x₂ m->Λβm')) (⊩->β-redL Γ⊩m'n∶τ₁ (redR x₂ m->Λβm')) x₁
  ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂ x₃) (abs L x₄) = app (⊩->β Γ⊩m'n∶τ (abs L x₄)) x₁ x₂ x₃
  ⊩->β-redL (~>∩ Γ⊩m'n∶τ Γ⊩m'n∶τ₁ x₁) (abs L x₂) = ~>∩ (⊩->β-redL Γ⊩m'n∶τ (abs L x₂)) (⊩->β-redL Γ⊩m'n∶τ₁ (abs L x₂)) x₁
  ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂ x₃) (beta x₄ x₅) = app (⊩->β Γ⊩m'n∶τ (beta x₄ x₅)) x₁ x₂ x₃
  ⊩->β-redL (~>∩ Γ⊩m'n∶τ Γ⊩m'n∶τ₁ x₁) (beta x₂ x₃) = ~>∩ (⊩->β-redL Γ⊩m'n∶τ (beta x₂ x₃)) (⊩->β-redL Γ⊩m'n∶τ₁ (beta x₂ x₃)) x₁
  ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂ x₃) (Y x₄) = app (⊩->β Γ⊩m'n∶τ (Y x₄)) x₁ x₂ x₃
  ⊩->β-redL (~>∩ Γ⊩m'n∶τ Γ⊩m'n∶τ₁ x₁) (Y x₂) = ~>∩ (⊩->β-redL Γ⊩m'n∶τ (Y x₂)) (⊩->β-redL Γ⊩m'n∶τ₁ (Y x₂)) x₁

⊩->β (app Γ⊩m'∶τ x x₁ x₂) (redR x₃ m->βm') = app Γ⊩m'∶τ (⊩->βₗ x m->βm') x₁ x₂
⊩->β (~>∩ Γ⊩m'∶τ Γ⊩m'∶τ₁ x) (redR x₁ m->βm') = ~>∩ (⊩->β Γ⊩m'∶τ (redR x₁ m->βm')) (⊩->β Γ⊩m'∶τ₁ (redR x₁ m->βm')) x
⊩->β (abs L cf x) (abs L₁ x₁) = abs (L ++ L₁) (λ x∉L → ⊩->βₗ (cf (∉-cons-l _ _ x∉L)) (x₁ (∉-cons-r L _ x∉L))) x
⊩->β (~>∩ Γ⊩m'∶τ Γ⊩m'∶τ₁ x) (abs L x₁) = ~>∩ (⊩->β Γ⊩m'∶τ (abs L x₁)) (⊩->β Γ⊩m'∶τ₁ (abs L x₁)) x
⊩->β Γ⊩m'∶τ (beta {m = m} {n} x x₁) = app Γ⊩lam-m∶τ Γ⊩ₗn∶τᵢ {!   !} (⊩ₗ-∷'ₗ Γ⊩ₗn∶τᵢ)
  where
  helper = ^-⊩-2 x x₁ Γ⊩m'∶τ
  τᵢ = proj₁ helper
  Γ⊩lam-m∶τ = proj₁ (proj₂ helper)
  Γ⊩ₗn∶τᵢ = proj₂ (proj₂ helper)
⊩->β Γ⊩mYm∶τ (Y _) = Γ⊩mYm∶τ->Γ⊩Ym∶τ Γ⊩mYm∶τ

⊩->βₗ (nil wf-Γ) m->βm' = nil wf-Γ
⊩->βₗ (cons x Γ⊩ₗm'∶τ) m->βm' = cons (⊩->β x m->βm') (⊩->βₗ Γ⊩ₗm'∶τ m->βm')
-- ⊩->βₗ (subₗ Γ⊩ₗm'∶τ x) m->βm' = subₗ (⊩->βₗ Γ⊩ₗm'∶τ m->βm') x



















----------------------------------------------------

-- ⊩->β {Γ = Γ} {τ = τ} Γ⊩m'∶τ (beta {A} {B} {m} {n} x x₁) = {!   !} -- app {τ₂ = τᵢ} (abs L cf {!   !}) Γ⊩ₗn∶τᵢ {!   !} {!   !}
  -- where
  -- body : ∃(λ τᵢ -> (∃ (λ L -> ∀ {x} -> (x∉L : x ∉ L) -> ((x , (τᵢ , A)) ∷ Γ) ⊩ Λ[ 0 >> fv {A} x ] m ∶ τ) ) × (Γ ⊩ₗ n ∶ τᵢ))
  -- body = ^-⊩ {m = m} {n} Γ⊩m'∶τ
  --
  -- τᵢ = proj₁ body
  --
  -- cf_def : ∃(λ L -> ∀ {x} -> (x∉L : x ∉ L) -> ((x , (τᵢ , A)) ∷ Γ) ⊩ Λ[ 0 >> fv {A} x ] m ∶ τ)
  -- cf_def = proj₁ (proj₂ body)
  --
  -- L = proj₁ cf_def
  -- cf = proj₂ cf_def
  --
  -- Γ⊩ₗn∶τᵢ : Γ ⊩ₗ n ∶ τᵢ
  -- Γ⊩ₗn∶τᵢ = proj₂ (proj₂ body)
