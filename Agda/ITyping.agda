module ITyping where

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
open import Typing
open import Typed-Core
open import ITyping-Core
open import ITyping-Subst

open import Reduction using (_↝_)


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
subst-⊩ {B = B} {Γ} {τᵢ = τᵢ} {x} {n = n} (lam L cf) trm-n (abs {A} {τ = τ} {τ'} L' {m} cf') Γ⊩ₗn∶τᵢ = abs (x ∷ L ++ L' ++ dom Γ) body
  where
  cons' : ∀ {x τ A Γ} -> Wf-ICtxt ((x , τ , A) ∷ Γ) -> τ ∷'ₗ A
  cons' (cons _ x _) = x

  τ∷ : ∀ {x} -> x ∉ L' -> τ ∷'ₗ A
  τ∷ x∉ = cons' (⊩ₗ-wf-Γ (cf' x∉))

  body : ∀ {x'} -> x' ∉ x ∷ L ++ L' ++ dom Γ -> ((x' , τ , A) ∷ Γ) ⊩ₗ Λ[ 0 >> (fv {A} x') ] (m Λ[ x ::= n ]) ∶ τ'
  body {x'} x'∉ rewrite
    Λsubst-open-var {τ'' = A} x' x n m (fv-x≠y _ _ x'∉) trm-n = subst-⊩ₗ {τᵢ = τᵢ}
    (cf (∉-∷-elim _ (∉-cons-l _ _ x'∉)))
    trm-n
    (exchange-⊩ₗ (cf' (∉-cons-l _ _ (∉-cons-r L _ (∉-∷-elim _ x'∉)))))
    (subₗ
      Γ⊩ₗn∶τᵢ
      (⊆ₗ-refl (⊩ₗ-∷'ₗ Γ⊩ₗn∶τᵢ))
      (⊆Γ-⊆ (cons (∉-cons-r L' _ (∉-cons-r L _ (∉-∷-elim _ x'∉))) (τ∷ (∉-cons-l L' _ (∉-cons-r L _ (∉-∷-elim _ x'∉)))) (⊩ₗ-wf-Γ Γ⊩ₗn∶τᵢ)) (λ {x₂} → there)))

subst-⊩ (lam L cf) trm-n (~>∩ x∷Γ⊩m∶τ x∷Γ⊩m∶τ₁ x₁) Γ⊩ₗn∶τᵢ = ~>∩ (subst-⊩ (lam L cf) trm-n x∷Γ⊩m∶τ Γ⊩ₗn∶τᵢ) (subst-⊩ (lam L cf) trm-n x∷Γ⊩m∶τ₁ Γ⊩ₗn∶τᵢ) x₁
subst-⊩ (app trm-m trm-m₁) trm-n (app x∷Γ⊩m∶τ x₁ x₂) Γ⊩ₗn∶τᵢ = app (subst-⊩ trm-m trm-n x∷Γ⊩m∶τ Γ⊩ₗn∶τᵢ) (subst-⊩ₗ trm-m₁ trm-n x₁ Γ⊩ₗn∶τᵢ) x₂
subst-⊩ (app trm-m trm-m₁) trm-n (~>∩ x∷Γ⊩m∶τ x∷Γ⊩m∶τ₁ x₁) Γ⊩ₗn∶τᵢ = ~>∩ (subst-⊩ (app trm-m trm-m₁) trm-n x∷Γ⊩m∶τ Γ⊩ₗn∶τᵢ) (subst-⊩ (app trm-m trm-m₁) trm-n x∷Γ⊩m∶τ₁ Γ⊩ₗn∶τᵢ) x₁
subst-⊩ Y trm-n (Y (cons x∉ x₁ wf-Γ) x₂ x₃) Γ⊩ₗn∶τᵢ = Y wf-Γ x₂ x₃
subst-⊩ Y trm-n (~>∩ x∷Γ⊩m∶τ x∷Γ⊩m∶τ₁ x₁) Γ⊩ₗn∶τᵢ = ~>∩ (subst-⊩ Y trm-n x∷Γ⊩m∶τ Γ⊩ₗn∶τᵢ) (subst-⊩ Y trm-n x∷Γ⊩m∶τ₁ Γ⊩ₗn∶τᵢ) x₁

subst-⊩ₗ trm-m trm-n (nil (cons x∉ x₁ wf-Γ)) Γ⊩ₗn∶τᵢ = nil wf-Γ
subst-⊩ₗ trm-m trm-n (cons x₁ x∷Γ⊩ₗm∶τ) Γ⊩ₗn∶τᵢ = cons (subst-⊩ trm-m trm-n x₁ Γ⊩ₗn∶τᵢ) (subst-⊩ₗ trm-m trm-n x∷Γ⊩ₗm∶τ Γ⊩ₗn∶τᵢ)


^-⊩ : ∀ {A B Γ τ τᵢ} {m : Λ B} {n : Λ A} -> ΛTerm (lam A m) -> ΛTerm n -> Γ ⊩ lam A m ∶ (τᵢ ~> ∩' τ) -> Γ ⊩ₗ n ∶ τᵢ ->
   Γ ⊩ (Λ[ 0 >> n ] m) ∶ τ
^-⊩ {A} {Γ = Γ} {τ} {τᵢ} {m} {n} (lam L cf) trm-n Γ⊩lam-m Γ⊩n = body
  where
  helper : ∃(λ L -> ( ∀ {x} -> (x∉L : x ∉ L) -> ((x , (τᵢ , A)) ∷ Γ) ⊩ₗ Λ[ 0 >> fv {A} x ] m ∶ ∩' τ ))
  helper = abs-inv Γ⊩lam-m

  L' = proj₁ helper
  cf' = proj₂ helper

  x = ∃fresh (L ++ L' ++ ΛFV m)

  x∉ : x ∉ (L ++ L' ++ ΛFV m)
  x∉ = ∃fresh-spec (L ++ L' ++ ΛFV m)

  body : Γ ⊩ (Λ[ 0 >> n ] m) ∶ τ
  body rewrite
    Λsubst-intro x n m (∉-cons-r L' _ (∉-cons-r L _ x∉)) trm-n =
    subst-⊩ (cf (∉-cons-l L _ x∉)) trm-n (⊩ₗ-∈-⊩ (cf' (∉-cons-l L' _ (∉-cons-r L _ x∉))) (here refl)) Γ⊩n


Γ⊩Ym∶τ->Γ⊩mYm∶τ : ∀ {A Γ m τ} -> Γ ⊩ app (Y A) m ∶ τ -> Γ ⊩ app m (app (Y A) m) ∶ τ
Γ⊩Ym∶τ->Γ⊩mYm∶τ {A} {Γ} {m} {τ} (app {τ₁ = τ₁} {τ₂} Γ⊩Y Γ⊩m τ⊆ₗτ₂) = app (⊩ₗ-∈-⊩ Γ⊩m' (here refl)) (helper₂ _ (λ {x} z → z)) τ⊆ₗτ' -- (cons (app {τ₁ = τ₁} {τ₂} Γ⊩Y Γ⊩m τ⊆ₗτ₂ x₂) (nil {!   !})) (⊆ₗ-trans τ⊆ₗτ₂ τ₂⊆ₗτ') {!   !}
  where
  helper : ∃ (λ τ → (∩' (τ ~> τ) ⊆ₗ[ A ⟶ A ] τ₁) × (τ₂ ⊆ₗ[ A ] τ))
  helper = Y-inv Γ⊩Y

  τ' = proj₁ helper
  τ'~>τ'⊆ₗτ₁ = proj₁ (proj₂ helper)
  τ₂⊆ₗτ' = proj₂ (proj₂ helper)

  τ⊆ₗτ' : (∩' τ) ⊆ₗ[ A ] τ'
  τ⊆ₗτ' = (⊆ₗ-trans τ⊆ₗτ₂ τ₂⊆ₗτ')

  Γ⊩m' : Γ ⊩ₗ m ∶ ∩' (τ' ~> τ')
  Γ⊩m' = subₗ Γ⊩m τ'~>τ'⊆ₗτ₁ (⊆Γ-⊆ (⊩-wf-Γ Γ⊩Y) (λ {x} z → z))

  helper₂ : ∀ τ -> τ ⊆ τ' -> Γ ⊩ₗ app (Y A) m ∶ τ
  helper₂ [] _ = nil (⊩-wf-Γ Γ⊩Y)
  helper₂ (τ ∷ τ'ᵢ) τ⊆τ' = cons
    (app
      (Y (⊩-wf-Γ Γ⊩Y) (⊆ₗ-refl (⊆ₗ-∷'ₗ-l τ'~>τ'⊆ₗτ₁)) (⊆ₗ-refl (⊆ₗ-∷'ₗ-r τ₂⊆ₗτ')))
      Γ⊩m'
      (⊆ₗ-⊆ (λ x₁ → τ⊆τ' (∈-∨-++ (inj₁ x₁))) (⊆ₗ-∷'ₗ-r τ₂⊆ₗτ')))
    (helper₂ τ'ᵢ (λ x₁ → τ⊆τ' (there x₁)))

Γ⊩Ym∶τ->Γ⊩mYm∶τ (~>∩ Γ⊩Ym∶τ Γ⊩Ym∶τ₁ x) = ~>∩ (Γ⊩Ym∶τ->Γ⊩mYm∶τ Γ⊩Ym∶τ) (Γ⊩Ym∶τ->Γ⊩mYm∶τ Γ⊩Ym∶τ₁) x


->β⊩ : ∀ {A Γ} {m m' : Λ A} {τ} -> Γ ⊩ m ∶ τ -> m ->Λβ m' -> Γ ⊩ m' ∶ τ
->β⊩ₗ : ∀ {A Γ} {m m' : Λ A} {τ} -> Γ ⊩ₗ m ∶ τ -> m ->Λβ m' -> Γ ⊩ₗ m' ∶ τ

->β⊩ (app Γ⊩m∶τ x x₁) (redL x₃ m->βm') = app (->β⊩ Γ⊩m∶τ m->βm') x x₁
->β⊩ (~>∩ Γ⊩m∶τ Γ⊩m∶τ₁ x) (redL x₁ m->βm') = ~>∩ (->β⊩ Γ⊩m∶τ (redL x₁ m->βm')) (->β⊩ Γ⊩m∶τ₁ (redL x₁ m->βm')) x
->β⊩ (app Γ⊩m∶τ x x₁) (redR x₃ m->βm') = app Γ⊩m∶τ (->β⊩ₗ x m->βm') x₁
->β⊩ (~>∩ Γ⊩m∶τ Γ⊩m∶τ₁ x) (redR x₁ m->βm') = ~>∩ (->β⊩ Γ⊩m∶τ (redR x₁ m->βm')) (->β⊩ Γ⊩m∶τ₁ (redR x₁ m->βm')) x
->β⊩ (abs L cf) (abs L₁ x₁) = abs (L ++ L₁) (λ x∉L → ->β⊩ₗ (cf (∉-cons-l L _ x∉L)) (x₁ (∉-cons-r L _ x∉L)))
->β⊩ (~>∩ Γ⊩m∶τ Γ⊩m∶τ₁ x) (abs L x₁) = ~>∩ (->β⊩ Γ⊩m∶τ (abs L x₁)) (->β⊩ Γ⊩m∶τ₁ (abs L x₁)) x
->β⊩ (app Γ⊩m∶τ Γ⊩ₗn x₁) (beta x₃ x₄) =
  ^-⊩ x₃ x₄ (sub Γ⊩m∶τ (arr (⊆ₗ-refl (⊩ₗ-∷'ₗ Γ⊩ₗn)) x₁) (⊆Γ-⊆ (⊩-wf-Γ Γ⊩m∶τ) (λ {x} z → z))) Γ⊩ₗn
->β⊩ (~>∩ Γ⊩m∶τ Γ⊩m∶τ₁ x) (beta x₁ x₂) = ~>∩ (->β⊩ Γ⊩m∶τ (beta x₁ x₂)) (->β⊩ Γ⊩m∶τ₁ (beta x₁ x₂)) x
->β⊩ {_} {Γ} {τ = τ} Γ⊩m∶τ (Y {A} {m} x) = Γ⊩Ym∶τ->Γ⊩mYm∶τ Γ⊩m∶τ

->β⊩ₗ (nil wf-Γ) m->βm' = nil wf-Γ
->β⊩ₗ (cons x Γ⊩ₗm∶τ) m->βm' = cons (->β⊩ x m->βm') (->β⊩ₗ Γ⊩ₗm∶τ m->βm')



^-⊩-2 : ∀ {A B Γ τ} {m : Λ B} {n : Λ A} -> ΛTerm (lam A m) -> ΛTerm n -> Γ ⊩ (Λ[ 0 >> n ] m) ∶ τ ->
  ∃(λ τᵢ -> (Γ ⊩ lam A m ∶ (τᵢ ~> ∩' τ) × ( Γ ⊩ₗ n ∶ τᵢ )))
^-⊩-2 {A} {B} {Γ} {τ} {m} {n} (lam L cf) trm-n Γ⊩m^n∶τ =
  τᵢ ,
  ((abs
    (x ∷ dom Γ ++ ΛFV m)
    (λ {x'} x'∉ → auxₗ
      m
      (proj₂ (∃~T m))
      (∉-cons-l (dom Γ) _ (∉-∷-elim _ x'∉))
      (∉-cons-l (ΛFV m) _ (∉-cons-r L _ x∉))
      ((∉-cons-r (dom Γ) _ (∉-∷-elim _ x'∉)))
      (λ x₁ → fv-x≠y _ _ x'∉ (sym x₁))
      (cons x∷Γ⊩m^'x∶τ (nil (cons (∉-cons-r (ΛFV m) _ (∉-cons-r L _ x∉)) (⊩ₗ-∷'ₗ Γ⊩ₗn∶τᵢ) (⊩ₗ-wf-Γ Γ⊩ₗn∶τᵢ)))))) ,
  Γ⊩ₗn∶τᵢ)
  where
  x = ∃fresh (L ++ ΛFV m ++ dom Γ)

  x∉ : x ∉ (L ++ ΛFV m ++ dom Γ)
  x∉ = ∃fresh-spec (L ++ ΛFV m ++ dom Γ)

  Γ⊩m^n∶τ' : Γ ⊩ ((Λ[ 0 >> fv {A} x ] m) Λ[ x ::= n ]) ∶ τ
  Γ⊩m^n∶τ' rewrite Λsubst-intro2 x n m (∉-cons-l (ΛFV m) _ (∉-cons-r L _ x∉)) trm-n = Γ⊩m^n∶τ

  ih : ∃(λ τᵢ -> ( ((x , τᵢ , A) ∷ Γ) ⊩ (Λ[ 0 >> fv {A} x ] m) ∶ τ ) × ( Γ ⊩ₗ n ∶ τᵢ ))
  ih = subst-⊩-2 (cf (∉-cons-l L _ x∉)) trm-n (∉-cons-r (ΛFV m) _ (∉-cons-r L _ x∉)) Γ⊩m^n∶τ'

  τᵢ = proj₁ ih
  x∷Γ⊩m^'x∶τ = proj₁ (proj₂ ih)
  Γ⊩ₗn∶τᵢ = proj₂ (proj₂ ih)


Γ⊩Ym-max : ∀ {A Γ} {m : Λ (A ⟶ A)} {τ} -> Γ ⊩ app (Y A) m ∶ τ -> ∃(λ τ' -> Γ ⊩ₗ m ∶ ∩' (τ' ~> τ') × (∩' τ) ⊆ₗ[ A ] τ')
Γ⊩Ym-max {A} {Γ} {m} {τ} (app Γ⊩Y∶τ₁~>τ₂ Γ⊩ₗm∶τ₁ τ⊆ₗτ₂) = τ' , (subₗ Γ⊩ₗm∶τ₁ τ'~>τ'⊆ₗτ₁ (⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗm∶τ₁) (λ {x} z → z)) , ⊆ₗ-trans τ⊆ₗτ₂ τ₂⊆ₗτ)
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
      (cons ((τ ~> (τ₁ ++ τ₂)) , ((here refl) , (arr (⊆ₗ-refl τ∷') τ₁τ₂⊆ₗτ₁++τ₂))) (nil τ+∷))
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
          (arr (⊆ₗ-⊆ (λ x₂ → ∈-cons-l _ x₂) (∷'ₗ-++ τ'∷'A τᵢ'∷'A)) (⊆ₗ-refl τ'∷'A))))
        (nil (cons (arr τ'∷'A τ'∷'A) nil)))
      (⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗYm∶τ) (λ {x} z → z)))
    (subₗ Γ⊩ₗm∶τᵢ'~>τᵢ'
      (cons
        ( (τᵢ' ~> τᵢ') ,
          (here refl ,
          arr (⊆ₗ-⊆ (λ x₂ → ∈-cons-r τ' x₂) (∷'ₗ-++ τ'∷'A τᵢ'∷'A)) (⊆ₗ-refl τᵢ'∷'A)))
        (nil (cons (arr τᵢ'∷'A τᵢ'∷'A) nil)))
      (⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗYm∶τ) (λ {x} z → z)))


Γ⊩mYm∶τ->Γ⊩Ym∶τ : ∀ {A Γ m τ} -> Γ ⊩ app m (app (Y A) m) ∶ τ -> Γ ⊩ app (Y A) m ∶ τ
Γ⊩mYm∶τ->Γ⊩Ym∶τ {A} {Γ} {τ = τ} (app {s = m} {τ₁ = []} {τᵢ} Γ⊩m∶τᵢ'~>τᵢ (nil wf-Γ) τ⊆τᵢ) = app
  (Y {τ = ∩' τ} {(ω ~> ∩' τ) ∷ []} {∩' τ}
    wf-Γ
    (cons (([] ~> ∩' τ) , ((here refl) , (arr (nil τ∷A) (⊆ₗ-refl τ∷A)))) (nil (cons (arr nil τ∷A) nil)))
    (⊆ₗ-refl τ∷A))
  (cons (sub Γ⊩m∶τᵢ'~>τᵢ (arr (nil nil) τ⊆τᵢ) (⊆Γ-⊆ wf-Γ (λ {x} z → z))) (nil wf-Γ))
  (⊆ₗ-refl τ∷A)

  where
  τ∷A = ⊆ₗ-∷'ₗ-l τ⊆τᵢ

Γ⊩mYm∶τ->Γ⊩Ym∶τ {A} {Γ} {τ = τ} (app {s = m} {τ₁ = τ' ∷ τᵢ'} {τᵢ} Γ⊩m∶τᵢ'~>τᵢ (cons x₁ Γ⊩ₗYm∶τ'ᵢ₁) τ⊆τᵢ) = app
  (Y {τ = [ τ ] ++ τ''} {∩' (τ'' ~> ([ τ ] ++ τ''))} {∩' τ}
    (⊩ₗ-wf-Γ Γ⊩ₗYm∶τ'ᵢ₁)
    (cons
      (
        (τ'' ~> ([ τ ] ++ τ'')) ,
        here refl ,
        arr
          (⊆ₗ-⊆ (λ x₂ → ∈-cons-r [ τ ] x₂) (cons τ∷'A τ''∷'A))
          (⊆ₗ-refl (cons τ∷'A τ''∷'A)))
      (nil (cons (arr τ''∷'A (cons τ∷'A τ''∷'A)) nil)))
    (cons (τ , (here refl , ⊆-refl τ∷'A)) (nil (cons τ∷'A τ''∷'A))))
  Γ⊩ₗm∶τ''~>τ++τ''
  (⊆ₗ-refl (cons τ∷'A nil))

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
  Γ⊩m∶τ''~>τ = sub Γ⊩m∶τᵢ'~>τᵢ (arr τᵢ''⊆τ'' τ⊆τᵢ) (⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗYm∶τ'ᵢ₁) (λ {x} z → z))

  Γ⊩ₗm∶τ''~>τ++τ'' : Γ ⊩ₗ m ∶ ∩' (τ'' ~> ([ τ ] ++ τ''))
  Γ⊩ₗm∶τ''~>τ++τ'' = subₗ (cons Γ⊩m∶τ''~>τ Γ⊩ₗm∶τ''~>τ'') (~>∩ (cons (arr τ''∷'A (cons τ∷'A τ''∷'A)) nil)) (⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗYm∶τ'ᵢ₁) (λ {x} z → z))

Γ⊩mYm∶τ->Γ⊩Ym∶τ (~>∩ Γ⊩mYm∶τ Γ⊩mYm∶τ₁ z) = ~>∩ (Γ⊩mYm∶τ->Γ⊩Ym∶τ Γ⊩mYm∶τ) (Γ⊩mYm∶τ->Γ⊩Ym∶τ Γ⊩mYm∶τ₁) z


⊩->β : ∀ {A Γ} {m m' : Λ A} {τ} -> Γ ⊩ m' ∶ τ -> m ->Λβ m' -> Γ ⊩ m ∶ τ
⊩->βₗ : ∀ {A Γ} {m m' : Λ A} {τ} -> Γ ⊩ₗ m' ∶ τ -> m ->Λβ m' -> Γ ⊩ₗ m ∶ τ

⊩->β Γ⊩m'∶τ (redL x m->βm') = ⊩->β-redL Γ⊩m'∶τ m->βm'
  where
  ⊩->β-redL : ∀ {A B Γ} {m m' : Λ (A ⟶ B)} {n : Λ A} {τ} -> Γ ⊩ app m' n ∶ τ -> m ->Λβ m' -> Γ ⊩ app m n ∶ τ
  ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂) (redL x₄ m->Λβm') = app (⊩->β-redL Γ⊩m'n∶τ m->Λβm') x₁ x₂
  ⊩->β-redL (~>∩ Γ⊩m'n∶τ Γ⊩m'n∶τ₁ x₁) (redL x₂ m->Λβm') = ~>∩ (⊩->β-redL Γ⊩m'n∶τ (redL x₂ m->Λβm')) (⊩->β-redL Γ⊩m'n∶τ₁ (redL x₂ m->Λβm')) x₁
  ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂) (redR x₄ m->Λβm') = app (⊩->β Γ⊩m'n∶τ (redR x₄ m->Λβm')) x₁ x₂
  ⊩->β-redL (~>∩ Γ⊩m'n∶τ Γ⊩m'n∶τ₁ x₁) (redR x₂ m->Λβm') = ~>∩ (⊩->β-redL Γ⊩m'n∶τ (redR x₂ m->Λβm')) (⊩->β-redL Γ⊩m'n∶τ₁ (redR x₂ m->Λβm')) x₁
  ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂) (abs L x₄) = app (⊩->β Γ⊩m'n∶τ (abs L x₄)) x₁ x₂
  ⊩->β-redL (~>∩ Γ⊩m'n∶τ Γ⊩m'n∶τ₁ x₁) (abs L x₂) = ~>∩ (⊩->β-redL Γ⊩m'n∶τ (abs L x₂)) (⊩->β-redL Γ⊩m'n∶τ₁ (abs L x₂)) x₁
  ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂) (beta x₄ x₅) = app (⊩->β Γ⊩m'n∶τ (beta x₄ x₅)) x₁ x₂
  ⊩->β-redL (~>∩ Γ⊩m'n∶τ Γ⊩m'n∶τ₁ x₁) (beta x₂ x₃) = ~>∩ (⊩->β-redL Γ⊩m'n∶τ (beta x₂ x₃)) (⊩->β-redL Γ⊩m'n∶τ₁ (beta x₂ x₃)) x₁
  ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂) (Y x₄) = app (⊩->β Γ⊩m'n∶τ (Y x₄)) x₁ x₂
  ⊩->β-redL (~>∩ Γ⊩m'n∶τ Γ⊩m'n∶τ₁ x₁) (Y x₂) = ~>∩ (⊩->β-redL Γ⊩m'n∶τ (Y x₂)) (⊩->β-redL Γ⊩m'n∶τ₁ (Y x₂)) x₁

⊩->β (app Γ⊩m'∶τ x x₁) (redR x₃ m->βm') = app Γ⊩m'∶τ (⊩->βₗ x m->βm') x₁
⊩->β (~>∩ Γ⊩m'∶τ Γ⊩m'∶τ₁ x) (redR x₁ m->βm') = ~>∩ (⊩->β Γ⊩m'∶τ (redR x₁ m->βm')) (⊩->β Γ⊩m'∶τ₁ (redR x₁ m->βm')) x
⊩->β (abs L cf) (abs L₁ x₁) = abs (L ++ L₁) (λ x∉L → ⊩->βₗ (cf (∉-cons-l _ _ x∉L)) (x₁ (∉-cons-r L _ x∉L)))
⊩->β (~>∩ Γ⊩m'∶τ Γ⊩m'∶τ₁ x) (abs L x₁) = ~>∩ (⊩->β Γ⊩m'∶τ (abs L x₁)) (⊩->β Γ⊩m'∶τ₁ (abs L x₁)) x
⊩->β Γ⊩m'∶τ (beta {m = m} {n} x x₁) = app Γ⊩lam-m∶τ Γ⊩ₗn∶τᵢ (⊆ₗ-refl (cons (⊩-∷' Γ⊩m'∶τ) nil))
  where
  helper = ^-⊩-2 x x₁ Γ⊩m'∶τ
  τᵢ = proj₁ helper
  Γ⊩lam-m∶τ = proj₁ (proj₂ helper)
  Γ⊩ₗn∶τᵢ = proj₂ (proj₂ helper)
⊩->β Γ⊩mYm∶τ (Y _) = Γ⊩mYm∶τ->Γ⊩Ym∶τ Γ⊩mYm∶τ

⊩->βₗ (nil wf-Γ) m->βm' = nil wf-Γ
⊩->βₗ (cons x Γ⊩ₗm'∶τ) m->βm' = cons (⊩->β x m->βm') (⊩->βₗ Γ⊩ₗm'∶τ m->βm')
