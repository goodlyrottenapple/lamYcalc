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
open import Typing using (dom)
open import Typed-Core
open import ITyping-Core
open import Reduction using (_↝_)



Γ⊩Ym-max : ∀ {A Γ} {m : Λ (A ⟶ A)} {τ} -> Γ ⊩ app (Y A) m ∶ τ -> ∃(λ τ' -> Γ ⊩ₗ m ∶ ∩' (τ' ~> τ') × (∩' τ) ⊆ₗ[ A ] τ')
Γ⊩Ym-max {A} {Γ} {m} {τ} (app {τ₁ = τ₁ᵢ~>τ₂ᵢ} {τ'}
  (Y {τ = τ''} wf-Γ τ''~>τ''⊆τ₁ᵢ~>τ₂ᵢ τ'⊆τ'')
  Γ⊩ₗm∶τ₁ᵢ~>τ₂ᵢ
  τ⊆τ' τ₁ᵢ~>τ₂ᵢ∷A⟶A) = τ'' , ((subₗ Γ⊩ₗm∶τ₁ᵢ~>τ₂ᵢ τ''~>τ''⊆τ₁ᵢ~>τ₂ᵢ) , (⊆ₗ-trans τ⊆τ' τ'⊆τ''))

∩-⊆-imp-⊆-∩ : ∀ {A τ τ' τᵢ τᵢ'} -> τ ⊆ₗ[ A ] τ' -> τᵢ ⊆ₗ[ A ] τᵢ' -> (τ ++ τᵢ) ⊆ₗ[ A ] (τ' ++ τᵢ')
∩-⊆-imp-⊆-∩ {τ' = τ'} τ⊆τ' τᵢ⊆τᵢ' = glb
  (⊆ₗ-trans τ⊆τ' (⊆ₗ-⊆ (λ x₁ → ∈-cons-l _ x₁) (∷'ₗ-++ (⊆ₗ-∷'ₗ-r τ⊆τ') (⊆ₗ-∷'ₗ-r τᵢ⊆τᵢ'))))
  (⊆ₗ-trans τᵢ⊆τᵢ' (⊆ₗ-⊆ (λ x₁ → ∈-cons-r τ' x₁) (∷'ₗ-++ (⊆ₗ-∷'ₗ-r τ⊆τ') (⊆ₗ-∷'ₗ-r τᵢ⊆τᵢ'))))


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
  ∩-⊆-imp-⊆-∩ τ⊆τ' τᵢ⊆τᵢ'
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


⊩->β : ∀ {A Γ} {m m' : Λ A} {τ} -> Γ ⊩ m' ∶ τ -> m ->Λβ m' -> Γ ⊩ m ∶ τ
⊩->β Γ⊩m'∶τ (redL x m->βm') = {!   !}
⊩->β Γ⊩m'∶τ (redR x m->βm') = {!   !}
⊩->β Γ⊩m'∶τ (abs L x) = {!   !}
⊩->β Γ⊩m'∶τ (beta x x₁) = {!   !}
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



-- ⊩->β {τ = τ} (app Γ⊩m∶[]~>τᵢ (nil wf-Γ) τ⊆τᵢ []∷A) (Y _) = app
--   (Y {τ = ∩' τ} {(ω ~> ∩' τ) ∷ []} {∩' τ}
--     wf-Γ
--     (cons (([] ~> ∩' τ) , ((here refl) , (arr (nil τ∷A) (⊆ₗ-refl τ∷A) (arr τ∷A τ∷A) (arr []∷A τ∷A)))) (nil (cons (arr []∷A τ∷A) nil)))
--     (⊆ₗ-refl τ∷A))
--   (cons (sub Γ⊩m∶[]~>τᵢ (arr (nil []∷A) τ⊆τᵢ (arr []∷A τ∷A) (arr []∷A (⊆ₗ-∷'ₗ-r τ⊆τᵢ))) (⊆Γ-⊆ wf-Γ (λ {x} z → z))) (nil wf-Γ))
--   (⊆ₗ-refl τ∷A)
--   (cons (arr []∷A τ∷A) nil)
--
--   where
--   τ∷A = ⊆ₗ-∷'ₗ-l τ⊆τᵢ
--
-- ⊩->β {A} {Γ} {τ = τ} (app {s = m} {τ₁ = τ' ∷ τ'ᵢ} {τᵢ} Γ⊩m∶τ'~>τᵢ Γ⊩ₗYm∶τ' τ⊆τᵢ τ'∷A) (Y _) = {!   !}
--   where
--   Γ⊆Γ-refl = ⊆Γ-⊆ (⊩ₗ-wf-Γ Γ⊩ₗYm∶τ') (λ {x} z → z)
--
--   τ'' = proj₁ (Γ⊩ₗYm-max (λ x → {!   !}) Γ⊩ₗYm∶τ')
--
--   Γ⊩m∶τ''~>τ'' : Γ ⊩ m ∶ (τ'' ~> τ'')
--   Γ⊩m∶τ''~>τ'' = proj₁ (proj₂ (Γ⊩ₗYm-max {!   !} Γ⊩ₗYm∶τ'))
--
--   τ'τ'ᵢ⊆τ'' : (τ' ∷ τ'ᵢ) ⊆ₗ[ A ] τ''
--   τ'τ'ᵢ⊆τ'' = proj₂ (proj₂ (Γ⊩ₗYm-max {!   !} Γ⊩ₗYm∶τ'))
--
--   Γ⊩m∶τ''~>τᵢ : Γ ⊩ m ∶ (τ'' ~> ∩' τ)
--   Γ⊩m∶τ''~>τᵢ = sub Γ⊩m∶τ'~>τᵢ (arr τ'τ'ᵢ⊆τ'' τ⊆τᵢ (arr (⊆ₗ-∷'ₗ-r τ'τ'ᵢ⊆τ'') (⊆ₗ-∷'ₗ-l τ⊆τᵢ)) (arr τ'∷A (⊆ₗ-∷'ₗ-r τ⊆τᵢ))) Γ⊆Γ-refl
--
-- ⊩->β {τ = τ} (app Γ⊩m∶[]~>τᵢ (subₗ x y) τ⊆τᵢ []∷A) (Y z) = {!   !}
--
--
--







-------------------------------------------




-- ⊩->β {τ = τ} (app Γ⊩m∶[]~>τᵢ (nil wf-Γ) τ⊆τᵢ []∷A) (Y _) = app
--   (Y {τ = ∩' τ} {(ω ~> ∩' τ) ∷ []} {∩' τ}
--     wf-Γ
--     ((ω ~> ∩' τ) , here refl , arr (nil τ∷A) (⊆ₗ-refl τ∷A) (arr τ∷A τ∷A) (arr nil τ∷A))
--     (cons (arr []∷A τ∷A) nil)
--     (⊆ₗ-refl τ∷A))
--   (cons (sub Γ⊩m∶[]~>τᵢ (arr (nil []∷A) τ⊆τᵢ (arr []∷A τ∷A) (arr []∷A (⊆ₗ-∷'ₗ-r τ⊆τᵢ))) (⊆Γ-⊆ wf-Γ (λ {x} z → z))) (nil wf-Γ))
--   (⊆ₗ-refl τ∷A)
--   (cons (arr []∷A τ∷A) nil)
--
--
-- -- ⊩->β (app {τ₁ = ∩ (τ₁ ∷ τ₁ᵢ)} Γ⊩m∶τ₁ᵢ~>τ₂ (cons (app (Y wf-Γ (proj₁ , () , proj₃) x₁ x₂) (nil wf-Γ₁) τ₁⊆τ₁₂ x₅) Γ⊩Ym∶τ₁ᵢ) τ⊆τ₂ τ₁∷A) (Y x)
-- -- ⊩->β {τ = τ} (app {τ₁ = ∩ (τ₁ ∷ τ₁ᵢ)} {τ₂} Γ⊩m∶τ₁ᵢ~>τ₂ (cons (app {τ₁ = ∩ (τ₁₁ ∷ τ₁₁ᵢ)} {τ₁₂} (Y {τ = τ'} wf-Γ (τ'' , τ''∈ τ₁₁, proj₃) x₁ x₂) (cons Γ⊩m∶τ₁₁ Γ⊩ₗm∶τ₁₁ᵢ) τ₁⊆τ₁₂ x₅) Γ⊩Ym∶τ₁ᵢ) τ⊆τ₂ τ₁∷A) (Y _) =
-- ⊩->β {A} {Γ} {τ = τ} (app {s = m} {τ₁ = ∩ (τ₁ ∷ τ₁ᵢ)} {τ₂}
--   Γ⊩m∶τ₁ᵢτ₁ᵢ~>τ₂
--   (cons
--     (app {τ₁ = ∩ (τ₁₁)} {τ₁₂}
--       (Y {τ = τ'} wf-Γ (_ , τ''∈τ₁₁ , arr {τ₂₁ = τ''₁} {τ''₂} τ''₁⊆τ' τ'⊆τ''₂ τ'~>τ'∷A⟶A (arr τ''₁∷A τ''₂∷A)) τ₁₁∷A⟶A τ₁₂⊆τ')
--       Γ⊩ₗm∶τ₁₁ τ₁⊆τ₁₂ τ₁₁∷A⟶A₂)
--     Γ⊩Ym∶τ₁ᵢ)
--   τ⊆τ₂
--   τ₁∷A) (Y _) =
--   {!   !}
--
--   where
--   Γ⊆Γ-refl = ⊆Γ-⊆ wf-Γ (λ {x} z → z)
--
--   Γ⊩m∶τ''₁~>τ''₂ : Γ ⊩ m ∶ (τ''₁ ~> τ''₂)
--   Γ⊩m∶τ''₁~>τ''₂ = ⊩ₗ-∈-⊩ Γ⊩ₗm∶τ₁₁ τ''∈τ₁₁
--
--   Γ⊩m∶τ''₂~>τ''₂ : Γ ⊩ m ∶ (τ''₂ ~> τ''₂)
--   Γ⊩m∶τ''₂~>τ''₂ = sub Γ⊩m∶τ''₁~>τ''₂ (arr (⊆ₗ-trans τ''₁⊆τ' τ'⊆τ''₂) (⊆ₗ-refl τ''₂∷A) (arr τ''₂∷A τ''₂∷A) (arr τ''₁∷A τ''₂∷A)) Γ⊆Γ-refl
--
--   Γ⊩m∶τ₁~>τ₂ : Γ ⊩ m ∶ (∩' τ₁ ~> τ₂)
--   Γ⊩m∶τ₁~>τ₂ = sub Γ⊩m∶τ₁ᵢτ₁ᵢ~>τ₂ (arr {!   !} {!   !} {!   !} {!   !}) Γ⊆Γ-refl












-- ⊩->β Γ⊩m'∶τ (redL x m->βm') = {!   !}
-- ⊩->β Γ⊩m'∶τ (redR x m->βm') = {!   !}
-- ⊩->β Γ⊩m'∶τ (abs L x) = {!   !}
-- ⊩->β Γ⊩m'∶τ (beta x x₁) = {!   !}
-- ⊩->β (app Γ⊩m'∶ω~>τ₂ (nil wf-Γ) τ⊆τ₂ nil) (Y trm-m) = {!   !}
-- ⊩->β (app Γ⊩m∶τ₃τᵢ~>τ₅ (cons _ (app (Y _ τ₂⊆τ₁ τ₁⊆τ) (cons _ Γ⊩m∶τ~>τ₁ (nil wf-Γ)) τ₃⊆τ₂ (cons τ~>τ₁∷A⟶A _)) Γ⊩ₗYm∶∩τᵢ) τ₄⊆τ₅ τ₃τᵢ∷A) (Y trm-m) = {!   !}













-- ⊩->β Γ⊩m'∶τ (redL x m->βm') = {!   !}
-- ⊩->β Γ⊩m'∶τ (redR x m->βm') = {!   !}
-- ⊩->β Γ⊩m'∶τ (abs L x) = {!   !}
-- ⊩->β Γ⊩m'∶τ (beta x x₁) = {!   !}
-- -- ⊩->β (app Γ⊩m∶τ₁~>τ (app (Y wf-Γ (arr (arr ::' ::'') ::''') τ≤τ₁ τ₂≤τ₁) Γ⊩m'∶τ₂ x₄) x₅) (Y x₆) = {!   !}
-- ⊩->β (app {s = m} {τ₂ = τ} Γ⊩m∶τ₁~>τ (app {τ₂ = τ₁} (Y {τ = τ₂} {τ₃} wf-Γ (arr (arr τ₂∷A τ₃∷A) _) τ≤τ₁ τ₂≤τ₁) Γ⊩m∶τ₂~>τ₃ _) (arr {A = A} τ₁∷A τ∷A)) (Y x₆) =
--   app {A = A ⟶ A}
--     (Y {_} {A} {∩ (τ₂ ∷ τ₁ ∷ [])} {∩ (τ₃ ∷ τ ∷ [])} {τ}
--       wf-Γ
--       (arr (arr (∩-cons τ₂∷A (∩-cons τ₁∷A ∩-nil)) (∩-cons τ₃∷A (∩-cons τ∷A ∩-nil))) τ∷A)
--       {!   !}
--       (∩-∈ (there (here refl))))
--     {!   !}
--     (arr (arr (∩-cons τ₂∷A (∩-cons τ₁∷A ∩-nil)) (∩-cons τ₃∷A (∩-cons τ∷A ∩-nil))) τ∷A)
--
-- ⊩->β (app Γ⊩m'∶τ (∩-nil ¬Y-shape wf-Γ) x) (Y x₁) = ⊥-elim (¬Y-shape intro₁)
-- ⊩->β (app Γ⊩m'∶τ (∩-cons ¬Y-shape wf-Γ Γ⊩m'∶τ₁ Γ⊩m'∶τ₂) x) (Y x₁) = ⊥-elim (¬Y-shape intro₁)
-- ⊩->β (∩-nil ¬Y-shape wf-Γ) (Y x) = ⊥-elim (¬Y-shape intro₂)
-- ⊩->β (∩-cons ¬Y-shape wf-Γ Γ⊩m'∶τ Γ⊩m'∶τ₁) (Y x) = ⊥-elim (¬Y-shape intro₂)

-- ⊩->β Γ⊩m'∶τ (redL trm-n m->βm') = ⊩->β-redL Γ⊩m'∶τ m->βm'
--   where
--   ⊩->β-redL : ∀ {A B Γ} {m m' : Λ (A ⟶ B)} {n : Λ A} {τ} -> Γ ⊩ app m' n ∶ τ -> m ->Λβ m' -> Γ ⊩ app m n ∶ τ
--   ⊩->β-redL (app Γ⊩m'n∶τ Γ⊩m'n∶τ₁ x x₁) (redL x₂ m->Λβm') =
--     app (⊩->β-redL Γ⊩m'n∶τ m->Λβm') Γ⊩m'n∶τ₁ x x₁
--   ⊩->β-redL (∩-nil ¬Y-shape wf-Γ) (redL x m->Λβm') = {!   !}
--   ⊩->β-redL (∩-cons ¬Y-shape wf-Γ Γ⊩m'n∶τ Γ⊩m'n∶τ₁) (redL x m->Λβm') = {!   !}
--   ⊩->β-redL Γ⊩m'n∶τ (redR x m->Λβm') = {!   !}
--   ⊩->β-redL Γ⊩m'n∶τ (abs L x) = {!   !}
--   ⊩->β-redL Γ⊩m'n∶τ (beta x x₁) = {!   !}
--   ⊩->β-redL Γ⊩m'n∶τ (Y x) = {!   !}
-- ⊩->β Γ⊩m'∶τ (redR trm-m n->βn') = {!   !}
-- ⊩->β Γ⊩m'∶τ (abs L x) = {!   !}
-- ⊩->β Γ⊩m'∶τ (beta x x₁) = {!   !}
-- ⊩->β (app {s = m} {τ₂ = τ} Γ⊩m∶τ₁~>τ (app (Y {_} {_} {τ₂} {τ₃} {τ₁} wf-Γ τ₂∷A τ₃∷A τ₁∷A τ₂≤∩τ₃ τ₁≤∩τ₃) Γ⊩m∶τ₂~>τ₃ x τ₂~>τ₃∷A) (arr {A = A} _ τ∷A) _) (Y trm-m) =
--   -- app {A = A ⟶ A} (Y wf-Γ τ₁∷A τ∷A τ∷A {!   !} {!   !}) Γ⊩m∶τ₁~>τ (arr (arr τ₁∷A τ∷A) τ∷A) (arr τ₁∷A τ∷A)
--   app {A = A ⟶ A}
--     (Y {_} {A} {∩ (τ₁ ∷ τ₂ ∷ τ₃ ∷ [])} {∩ (τ ∷ τ₃ ∷ [])} {τ}
--       wf-Γ
--       {!   !}
--       (∩-cons τ∷A (∩-cons τ₃∷A ∩-nil))
--       τ∷A
--       {!   !}
--       {!   !})
--     {!   !}
--     (arr {!   !} {!   !})
--     {!   !}
--
-- ⊩->β (app Γ⊩m∶τ~>τ' (∩-nil ¬Y-shape wf-Γ) x τ∷A) (Y trm-m) = ⊥-elim (¬Y-shape intro₁)
-- ⊩->β (app Γ⊩m∶τ~>τ' (∩-cons ¬Y-shape wf-Γ Γ⊩Ym∶τ' Γ⊩Ym∶τ'') x τ∷A) (Y trm-m) = ⊥-elim (¬Y-shape intro₁)
-- ⊩->β (∩-nil ¬Y-shape wf-Γ) (Y x) = ⊥-elim (¬Y-shape intro₂)
-- ⊩->β (∩-cons ¬Y-shape wf-Γ Γ⊩m'∶τ Γ⊩m'∶τ₁) (Y x) = ⊥-elim (¬Y-shape intro₂)
