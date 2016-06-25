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

open import Core
open import Core-Lemmas
open import Typing using (_≟T_)
open import Typed-Core
open import ITyping-Core
open import Reduction using (_↝_)



Γ⊩Ym-max : ∀ {A Γ} {m : Λ (A ⟶ A)} {τ} -> Γ ⊩ app (Y A) m ∶ τ -> ∃(λ τ' -> Γ ⊩ₗ m ∶ ∩' (τ' ~> τ') × (∩' τ) ⊆ₗ[ A ] τ')
Γ⊩Ym-max {A} {Γ} {m} {τ} (app {τ₁ = τ₁ᵢ~>τ₂ᵢ} {τ'}
  (Y {τ = τ''} wf-Γ τ''~>τ''⊆τ₁ᵢ~>τ₂ᵢ τ'⊆τ'')
  Γ⊩ₗm∶τ₁ᵢ~>τ₂ᵢ
  τ⊆τ' τ₁ᵢ~>τ₂ᵢ∷A⟶A) = τ'' , ((subₗ Γ⊩ₗm∶τ₁ᵢ~>τ₂ᵢ τ''~>τ''⊆τ₁ᵢ~>τ₂ᵢ) , (⊆ₗ-trans τ⊆τ' τ'⊆τ''))

¬ω⊆-impl¬ω : ∀ {A τ τ'} -> ¬(τ ≡ ω) -> τ ⊆ₗ[ A ] τ' -> ¬(τ' ≡ ω)
¬ω⊆-impl¬ω τ≠ω (nil x) τ'≡ω = τ≠ω refl
¬ω⊆-impl¬ω τ≠ω (cons (_ , () , _) τ⊆ₗτ') refl
¬ω⊆-impl¬ω τ≠ω (~>∩ x) ()
¬ω⊆-impl¬ω τ≠ω (⊆ₗ-trans τ⊆ₗτ' τ⊆ₗτ'') τ'≡ω = ¬ω⊆-impl¬ω (¬ω⊆-impl¬ω τ≠ω τ⊆ₗτ') τ⊆ₗτ'' τ'≡ω

Γ⊩ₗYm-max : ∀ {A Γ} {m : Λ (A ⟶ A)} {τ} -> ¬(τ ≡ ω) -> Γ ⊩ₗ app (Y A) m ∶ τ -> ∃(λ τ' -> Γ ⊩ₗ m ∶ ∩' (τ' ~> τ') × τ ⊆ₗ[ A ] τ')
Γ⊩ₗYm-max τ≠ω (nil wf-Γ) = ⊥-elim (τ≠ω refl)
Γ⊩ₗYm-max {A} {Γ} {m} {τ ∷ τᵢ} τ≠ω (cons x Γ⊩ₗYm∶τ) with τᵢ ≟TIₗ ω
Γ⊩ₗYm-max {A} {Γ} {m} {τ ∷ .[]} τ≠ω (cons x Γ⊩ₗYm∶τ) | yes refl = Γ⊩Ym-max x
Γ⊩ₗYm-max {A} {Γ} {m} {τ ∷ τᵢ} τ≠ω (cons x Γ⊩ₗYm∶τ) | no τᵢ≠ω =
  τ' ++ τᵢ' ,
  subₗ Γ⊩ₗm∶ττᵢ'~>τ'ττᵢ'~>τᵢ' (~>∩ (cons (arr (∷'ₗ-++ τ'∷'A τᵢ'∷'A) (∷'ₗ-++ τ'∷'A τᵢ'∷'A)) nil)) ,
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
        (nil (cons (arr τ'∷'A τ'∷'A) nil))))
    (subₗ Γ⊩ₗm∶τᵢ'~>τᵢ'
      (cons
        ( (τᵢ' ~> τᵢ') ,
          (here refl ,
          arr (⊆ₗ-⊆ (λ x₂ → ∈-cons-r τ' x₂) (∷'ₗ-++ τ'∷'A τᵢ'∷'A)) (⊆ₗ-refl τᵢ'∷'A) (arr (∷'ₗ-++ τ'∷'A τᵢ'∷'A) τᵢ'∷'A) (arr τᵢ'∷'A τᵢ'∷'A)))
        (nil (cons (arr τᵢ'∷'A τᵢ'∷'A) nil))))

Γ⊩ₗYm-max {A} {Γ} {m} {τᵢ} τ≠ω (subₗ {τ = τᵢ'} Γ⊩ₗYm∶τᵢ' x) = τᵢ'' , Γ⊩ₗm∶τᵢ''~>τᵢ'' , (⊆ₗ-trans x τᵢ'⊆τᵢ'')
  where
  ih : ∃(λ τᵢ'' -> Γ ⊩ₗ m ∶ ∩' (τᵢ'' ~> τᵢ'') × τᵢ' ⊆ₗ[ A ] τᵢ'')
  ih = Γ⊩ₗYm-max (¬ω⊆-impl¬ω τ≠ω x) Γ⊩ₗYm∶τᵢ'

  τᵢ'' = proj₁ ih
  Γ⊩ₗm∶τᵢ''~>τᵢ'' = proj₁ (proj₂ ih)
  τᵢ'⊆τᵢ'' = proj₂ (proj₂ ih)




subst-⊩ : ∀ {A B Γ τ τᵢ x} {m : Λ A} {n : Λ B} -> ΛTerm m -> ΛTerm n -> ((x , (τᵢ , A)) ∷ Γ) ⊩ m ∶ τ -> Γ ⊩ₗ n ∶ τᵢ ->
  Γ ⊩ (m Λ[ x ::= n ]) ∶ τ
subst-⊩ {A} {B} {x = x} var trm-n (var {x = y} wf-Γ τᵢ∈Γ τ⊆τᵢ) Γ⊩ₗn∶τᵢ with x ≟ y | A ≟T B
subst-⊩ var trm-n (var wf-Γ τᵢ∈Γ τ⊆τᵢ) Γ⊩ₗn∶τᵢ | yes refl | yes refl = ?
subst-⊩ var trm-n (var wf-Γ τᵢ∈Γ τ⊆τᵢ) Γ⊩ₗn∶τᵢ | yes refl | no ¬p = {!   !}
subst-⊩ var trm-n (var wf-Γ τᵢ∈Γ τ⊆τᵢ) Γ⊩ₗn∶τᵢ | no ¬p | q = {!   !}
subst-⊩ (lam L cf) trm-n x∷Γ⊩m∶τ Γ⊩ₗn∶τᵢ = {!   !}
subst-⊩ (app trm-m trm-m₁) trm-n x∷Γ⊩m∶τ Γ⊩ₗn∶τᵢ = {!   !}
subst-⊩ Y trm-n x∷Γ⊩m∶τ Γ⊩ₗn∶τᵢ = {!   !}


-- ^-⊩ : ∀ {A B Γ τ} {m : Λ B} {n : Λ A}-> Γ ⊩ Λ[ 0 >> n ] m ∶ τ ->
--   ∃(λ τᵢ -> (∃ (λ L -> ∀ {x} -> (x∉L : x ∉ L) -> ((x , (τᵢ , A)) ∷ Γ) ⊩ Λ[ 0 >> fv {A} x ] m ∶ τ) ) × (Γ ⊩ₗ n ∶ τᵢ))
-- ^-⊩ = {!   !}

-- Term n -> ( cf : ∀ {x} -> (x∉L : x ∉ L) -> ((x , ∩ τᵢ) ∷ Γ) ⊩ m ^' x ∶ τ₂ ) ->
--   (∀ {τ} -> τ ∈ τᵢ -> Γ ⊩ n ∶ τ) -> Γ ⊩ m ^ n ∶ τ₂




⊩->β : ∀ {A Γ} {m m' : Λ A} {τ} -> Γ ⊩ m' ∶ τ -> m ->Λβ m' -> Γ ⊩ m ∶ τ
⊩->βₗ : ∀ {A Γ} {m m' : Λ A} {τ} -> Γ ⊩ₗ m' ∶ τ -> m ->Λβ m' -> Γ ⊩ₗ m ∶ τ

⊩->β Γ⊩m'∶τ (redL x m->βm') = ⊩->β-redL Γ⊩m'∶τ m->βm'
  where
    ⊩->β-redL : ∀ {A B Γ} {m m' : Λ (A ⟶ B)} {n : Λ A} {τ} -> Γ ⊩ app m' n ∶ τ -> m ->Λβ m' -> Γ ⊩ app m n ∶ τ
    ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂ x₃) (redL x₄ m->Λβm') = app (⊩->β-redL Γ⊩m'n∶τ m->Λβm') x₁ x₂ x₃
    ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂ x₃) (redR x₄ m->Λβm') = app (⊩->β Γ⊩m'n∶τ (redR x₄ m->Λβm')) x₁ x₂ x₃
    ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂ x₃) (abs L x₄) = app (⊩->β Γ⊩m'n∶τ (abs L x₄)) x₁ x₂ x₃
    ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂ x₃) (beta x₄ x₅) = app (⊩->β Γ⊩m'n∶τ (beta x₄ x₅)) x₁ x₂ x₃
    ⊩->β-redL (app Γ⊩m'n∶τ x₁ x₂ x₃) (Y x₄) = app (⊩->β Γ⊩m'n∶τ (Y x₄)) x₁ x₂ x₃

⊩->β (app Γ⊩m'∶τ x x₁ x₂) (redR x₃ m->βm') = app Γ⊩m'∶τ (⊩->βₗ x m->βm') x₁ x₂
⊩->β (abs L cf x) (abs L₁ x₁) = abs (L ++ L₁) (λ x∉L → ⊩->βₗ (cf (∉-cons-l _ _ x∉L)) (x₁ (∉-cons-r L _ x∉L))) x

⊩->β {Γ = Γ} {τ = τ} Γ⊩m'∶τ (beta {A} {B} {m} {n} x x₁) = {!   !} -- app {τ₂ = τᵢ} (abs L cf {!   !}) Γ⊩ₗn∶τᵢ {!   !} {!   !}
  where
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

⊩->β {A} {Γ} {τ = τ} (app {s = m} {τ₁ = τᵢ'} {τᵢ} Γ⊩m∶τᵢ'~>τᵢ Γ⊩ₗYm∶τᵢ' τ⊆τᵢ τᵢ'∷A) (Y _) = body Γ⊩m∶τᵢ'~>τᵢ τ⊆τᵢ τᵢ'∷A Γ⊩ₗYm∶τᵢ'
  where
  body : ∀ {τᵢ τᵢ'} -> Γ ⊩ m ∶ (τᵢ' ~> τᵢ) -> ∩' τ ⊆ₗ[ A ] τᵢ -> τᵢ' ∷'ₗ A -> Γ ⊩ₗ app (Y A) m ∶ τᵢ' -> Γ ⊩ app (Y A) m ∶ τ
  body Γ⊩m∶τᵢ'~>τᵢ τ⊆τᵢ τᵢ'∷A (nil wf-Γ) = app
    (Y {τ = ∩' τ} {(ω ~> ∩' τ) ∷ []} {∩' τ}
      wf-Γ
      (cons (([] ~> ∩' τ) , ((here refl) , (arr (nil τ∷A) (⊆ₗ-refl τ∷A) (arr τ∷A τ∷A) (arr τᵢ'∷A τ∷A)))) (nil (cons (arr τᵢ'∷A τ∷A) nil)))
      (⊆ₗ-refl τ∷A))
    (cons (sub Γ⊩m∶τᵢ'~>τᵢ (arr (nil τᵢ'∷A) τ⊆τᵢ (arr τᵢ'∷A τ∷A) (arr τᵢ'∷A (⊆ₗ-∷'ₗ-r τ⊆τᵢ))) (⊆Γ-⊆ wf-Γ (λ {x} z → z))) (nil wf-Γ))
    (⊆ₗ-refl τ∷A)
    (cons (arr τᵢ'∷A τ∷A) nil)

    where
    τ∷A = ⊆ₗ-∷'ₗ-l τ⊆τᵢ
  body {τᵢ' = τ' ∷ τᵢ'} Γ⊩m∶τᵢ'~>τᵢ τ⊆τᵢ τᵢ'∷A (cons x₁ Γ⊩ₗYm∶τ'ᵢ₁) = app
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
    Γ⊩ₗm∶τ''~>τ++τ'' = subₗ (cons Γ⊩m∶τ''~>τ Γ⊩ₗm∶τ''~>τ'') (~>∩ (cons (arr τ''∷'A (cons τ∷'A τ''∷'A)) nil))

  body Γ⊩m∶τᵢ'~>τᵢ τ⊆τᵢ τᵢ'∷A (subₗ Γ⊩ₗYm∶τᵢ'' τᵢ'⊆τᵢ'') = body
    (sub Γ⊩m∶τᵢ'~>τᵢ
      (arr τᵢ'⊆τᵢ''
        (⊆ₗ-refl (⊆ₗ-∷'ₗ-r τ⊆τᵢ))
        (arr (⊆ₗ-∷'ₗ-r τᵢ'⊆τᵢ'') (⊆ₗ-∷'ₗ-r τ⊆τᵢ))
        (arr (⊆ₗ-∷'ₗ-l τᵢ'⊆τᵢ'') (⊆ₗ-∷'ₗ-r τ⊆τᵢ)))
      (⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗYm∶τᵢ'') (λ {x} z → z)))
    τ⊆τᵢ
    (⊆ₗ-∷'ₗ-r τᵢ'⊆τᵢ'')
    Γ⊩ₗYm∶τᵢ''

⊩->βₗ (nil wf-Γ) m->βm' = nil wf-Γ
⊩->βₗ (cons x Γ⊩ₗm'∶τ) m->βm' = cons (⊩->β x m->βm') (⊩->βₗ Γ⊩ₗm'∶τ m->βm')
⊩->βₗ (subₗ Γ⊩ₗm'∶τ x) m->βm' = subₗ (⊩->βₗ Γ⊩ₗm'∶τ m->βm') x
