module ITyping-Subst where

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


data Tree : Set where
  * : Tree
  U : Tree -> Tree
  _&_ : Tree -> Tree -> Tree


data _~T_ : ∀ {τ} -> Λ τ -> Tree -> Set where
  l-bv : ∀ {A i} -> bv {A} i ~T *
  l-fv : ∀ {A x} -> fv {A} x ~T *
  l-Y : ∀ {A} -> Y A ~T *
  un : ∀ {A B v} {e : Λ B} -> e ~T v -> (lam A e) ~T (U v)
  bin : ∀ {A B v w} {s : Λ (A ⟶ B)} {t : Λ A} -> s ~T v -> t ~T w -> (app s t) ~T (v & w)


^'-~T-inv : ∀ {A B x t k} {m : Λ A} -> m ~T t -> Λ[ k >> fv {B} x ] m ~T t
^'-~T-inv {A} {B} {x} {_} {k} {bv i} l-bv with k ≟ i
^'-~T-inv {A} {B} {x} {.*} {k} {bv .k} l-bv | yes refl with A ≟T B
^'-~T-inv {A} {.A} {x} {.*} {k} {bv .k} l-bv | yes refl | yes refl = l-fv
^'-~T-inv {A} {B} {x} {.*} {k} {bv .k} l-bv | yes refl | no _ = l-bv
^'-~T-inv {A} {B} {x} {.*} {k} {bv i} l-bv | no _ = l-bv
^'-~T-inv l-fv = l-fv
^'-~T-inv l-Y = l-Y
^'-~T-inv (un m~Tt) = un (^'-~T-inv m~Tt)
^'-~T-inv (bin m~Tt m~Tt₁) = bin (^'-~T-inv m~Tt) (^'-~T-inv m~Tt₁)


∃~T : ∀ {A} (m : Λ A) -> ∃(λ t -> m ~T t)
∃~T (bv i) = * , l-bv
∃~T (fv x) = * , l-fv
∃~T (lam A m) = (U (proj₁ ih)) , (un (proj₂ ih))
  where
  ih = ∃~T m
∃~T (app m m₁) = ((proj₁ ihₗ) & (proj₁ ihᵣ)) , bin (proj₂ ihₗ) (proj₂ ihᵣ)
  where
  ihₗ = ∃~T m
  ihᵣ = ∃~T m₁
∃~T (Y t) = * , l-Y


strenghten-⊩-aux : ∀ {A B Γ x τ τᵢ} {m : Λ B} {t} -> m ~T t -> x ∉ ΛFV m -> ((x , τᵢ , A) ∷ Γ) ⊩ m ∶ τ -> Γ ⊩ m ∶ τ
strenghten-⊩ₗ-aux : ∀ {A B Γ x τ τᵢ} {m : Λ B} {t} -> m ~T t -> x ∉ ΛFV m -> ((x , τᵢ , A) ∷ Γ) ⊩ₗ m ∶ τ -> Γ ⊩ₗ m ∶ τ
strenghten-⊩-aux m~Tt x∉ (var (cons x∉₁ x₂ wf-Γ) (here refl) τ⊆τᵢ) = ⊥-elim (x∉ (here refl))
strenghten-⊩-aux m~Tt x∉ (var (cons x∉₁ x₂ wf-Γ) (there τᵢ∈Γ) τ⊆τᵢ) = var wf-Γ τᵢ∈Γ τ⊆τᵢ
strenghten-⊩-aux (bin u~Tt v~Tt) x∉ (app {s = s} x∷Γ⊩m∶τ x₁ x₂ x₃) = app (strenghten-⊩-aux u~Tt (∉-cons-l _ _ x∉) x∷Γ⊩m∶τ) (strenghten-⊩ₗ-aux v~Tt (∉-cons-r (ΛFV s) _ x∉) x₁) x₂ x₃
strenghten-⊩-aux {x = x} (un m~Tt) x∉ (abs L {m} cf x₁) =
  abs (x ∷ L) (λ x∉L → strenghten-⊩ₗ-aux (^'-~T-inv m~Tt) (ΛFV-^ m x∉ (λ x₂ → fv-x≠y _ _ x∉L (sym x₂))) (exchange-⊩ₗ (cf (∉-∷-elim _ x∉L)))) x₁
strenghten-⊩-aux l-Y x∉ (Y (cons x∉₁ x₁ wf-Γ) x₂ x₃) = Y wf-Γ x₂ x₃
strenghten-⊩-aux m~Tt x∉ (~>∩ x∷Γ⊩m∶τ x∷Γ⊩m∶τ₁ x₁) = ~>∩ (strenghten-⊩-aux m~Tt x∉ x∷Γ⊩m∶τ) (strenghten-⊩-aux m~Tt x∉ x∷Γ⊩m∶τ₁) x₁

strenghten-⊩ₗ-aux m~Tt x∉ (nil (cons x∉₁ x₁ wf-Γ)) = nil wf-Γ
strenghten-⊩ₗ-aux m~Tt x∉ (cons x₁ x∷Γ⊩ₗm∶τ) = cons (strenghten-⊩-aux m~Tt x∉ x₁) (strenghten-⊩ₗ-aux m~Tt x∉ x∷Γ⊩ₗm∶τ)


strenghten-⊩ : ∀ {A B Γ x τ τᵢ} {m : Λ B} -> x ∉ ΛFV m -> ((x , τᵢ , A) ∷ Γ) ⊩ m ∶ τ -> Γ ⊩ m ∶ τ
strenghten-⊩ {m = m} x∉ x∷Γ⊩m∶τ = strenghten-⊩-aux (proj₂ (∃~T m)) x∉ x∷Γ⊩m∶τ


strenghten-⊩ₗ : ∀ {A B Γ x τ τᵢ} {m : Λ B} -> x ∉ ΛFV m -> ((x , τᵢ , A) ∷ Γ) ⊩ₗ m ∶ τ -> Γ ⊩ₗ m ∶ τ
strenghten-⊩ₗ {m = m} x∉ x∷Γ⊩m∶τ = strenghten-⊩ₗ-aux (proj₂ (∃~T m)) x∉ x∷Γ⊩m∶τ


∈-imp-∈dom : ∀ {Γ} {A : Type} {x : Atom} {τ : List IType} -> (x , (τ , A)) ∈ Γ -> x ∈ dom Γ
∈-imp-∈dom (here refl) = here refl
∈-imp-∈dom (there x,τ,A∈Γ) = there (∈-imp-∈dom x,τ,A∈Γ)


⊩bv-contr : ∀ {A Γ τ k} -> Γ ⊩ bv {A} k ∶ τ -> ⊥
⊩bv-contr (~>∩ Γ⊩k Γ⊩k₁ x) = ⊩bv-contr Γ⊩k


aux : ∀ {A B Γ τ τ' x y k} {t} -> (m : Λ B) -> m ~T t -> y ∉ dom Γ -> x ∉ ΛFV m -> y ∉ ΛFV m -> ¬(x ≡ y) ->
  ((x , τ , A) ∷ Γ) ⊩ Λ[ k >> fv {A} x ] m ∶ τ' -> ((y , τ , A) ∷ Γ) ⊩ Λ[ k >> fv {A} y ] m ∶ τ'
auxₗ : ∀ {A B Γ τ τ' x y k} {t} -> (m : Λ B) -> m ~T t -> y ∉ dom Γ -> x ∉ ΛFV m -> y ∉ ΛFV m -> ¬(x ≡ y) ->
  ((x , τ , A) ∷ Γ) ⊩ₗ Λ[ k >> fv {A} x ] m ∶ τ' -> ((y , τ , A) ∷ Γ) ⊩ₗ Λ[ k >> fv {A} y ] m ∶ τ'
aux {k = k} (bv i) l-bv y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ' with k ≟ i
aux {A} {B} (bv k) l-bv y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ' | yes refl with B ≟T A
aux (bv k) l-bv y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ' | yes refl | yes refl = body y∉Γ x∷Γ⊩m^'x∶τ'
  where
  body : ∀ {B Γ τ τ' x y} -> y ∉ dom Γ -> ((x , τ , B) ∷ Γ) ⊩ fv {B} x ∶ τ' -> ((y , τ , B) ∷ Γ) ⊩ fv {B} y ∶ τ'
  body y∉ (var (cons x∉ x₁ wf-Γ) (here refl) τ⊆τᵢ) = var (cons y∉ x₁ wf-Γ) (here refl) τ⊆τᵢ
  body y∉ (var (cons x∉ x₁ wf-Γ) (there τᵢ∈Γ) τ⊆τᵢ) = ⊥-elim (∉-dom x∉ τᵢ∈Γ)
  body y∉ (~>∩ x∷Γ⊩x∶τ' x∷Γ⊩x∶τ'' x₁) = ~>∩ (body y∉ x∷Γ⊩x∶τ') (body y∉ x∷Γ⊩x∶τ'') x₁

aux (bv k) l-bv y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ' | yes refl | no ¬p = ⊥-elim (⊩bv-contr x∷Γ⊩m^'x∶τ')
aux (bv i) l-bv y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ' | no ¬p = ⊥-elim (⊩bv-contr x∷Γ⊩m^'x∶τ')
aux {A} {B} {Γ} {k = k} (fv x₁) l-fv y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ' =
  sub (strenghten-⊩ (ΛFV-^ {k = k} {A = A} {B} (fv x₁) x∉FVm x≠y) x∷Γ⊩m^'x∶τ') (⊆-refl (⊩-∷' x∷Γ⊩m^'x∶τ')) (⊆Γ-⊆ (cons y∉Γ (∷'' (⊩-wf-Γ x∷Γ⊩m^'x∶τ')) wf-Γ) (λ {x} → there))
  where
  cons' : ∀ {x Γ} -> Wf-ICtxt (x ∷ Γ) -> Wf-ICtxt Γ
  cons' (cons x∉ x₂ wf-Γ) = wf-Γ

  ∷'' : ∀ {x τ B Γ} -> Wf-ICtxt ((x , τ , B) ∷ Γ) -> τ ∷'ₗ B
  ∷'' (cons x∉ x₂ wf-Γ) = x₂

  wf-Γ : Wf-ICtxt Γ
  wf-Γ = cons' (⊩-wf-Γ x∷Γ⊩m^'x∶τ')

aux {A} {_} {Γ} {τ} {τ' ~> τ''} {x} {y} {k} (lam {B} A' m) (un m~Tt) y∉Γ x∉FVm y∉FVm x≠y (abs L cf x₁) = abs (y ∷ x ∷ L) body x₁
  where
  cf' : ∀ {x'} -> x' ∉ (x ∷ L) -> ((x , τ , A) ∷ (x' , τ' , A') ∷ Γ) ⊩ₗ Λ[ suc k >> fv {A} x ](Λ[ 0 >> fv {A'} x' ] m) ∶ τ''
  cf' {x'} x'∉L rewrite Λ^-^-swap {B} {A} {A'} (suc k) 0 x x' m (λ ()) (λ x₂ → fv-x≠y _ _ x'∉L (sym x₂)) = exchange-⊩ₗ (cf (∉-∷-elim _ x'∉L))

  ih' : ∀ {x'} -> x' ∉ (y ∷ x ∷ L) -> ((y , τ , A) ∷ (x' , τ' , A') ∷ Γ) ⊩ₗ Λ[ suc k >> fv {A} y ](Λ[ 0 >> fv {A'} x' ] m) ∶ τ''
  ih' {x'} x'∉L = auxₗ
    (Λ[ 0 >> fv {A'} x' ] m)
    (^'-~T-inv m~Tt)
    (∉-∷ _ _ (λ x₂ → fv-x≠y _ _ x'∉L (sym x₂)) y∉Γ)
    (ΛFV-^ m x∉FVm (λ x₂ → fv-x≠y _ _ (∉-∷-elim _ x'∉L) (sym x₂)))
    (ΛFV-^ m y∉FVm (λ x₂ → fv-x≠y _ _ x'∉L (sym x₂)))
    x≠y
    (cf' (∉-∷-elim _ x'∉L))

  body : ∀ {x'} -> x' ∉ (y ∷ x ∷ L) -> ((x' , τ' , A') ∷ (y , τ , A) ∷ Γ) ⊩ₗ Λ[ 0 >> fv {A'} x' ](Λ[ suc k >> fv {A} y ] m) ∶ τ''
  body {x'} x'∉L rewrite Λ^-^-swap {B} {A'} {A} 0 (suc k) x' y m (λ ()) (λ x₂ → fv-x≠y _ _ x'∉L x₂) = exchange-⊩ₗ (ih' x'∉L)

aux (lam A m) m~Tt y∉Γ x∉FVm y∉FVm x≠y (~>∩ x∷Γ⊩m^'x∶τ' x∷Γ⊩m^'x∶τ'' x₁) =
  ~>∩ (aux (lam A m) m~Tt y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ') (aux (lam A m) m~Tt y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ'') x₁
aux (app m m₁) (bin m~Tt m₁~Tt) y∉Γ x∉FVm y∉FVm x≠y (app x∷Γ⊩m^'x∶τ' x₁ x₂ x₃) =
  app (aux m m~Tt y∉Γ (∉-cons-l _ _ x∉FVm) (∉-cons-l _ _ y∉FVm) x≠y x∷Γ⊩m^'x∶τ') (auxₗ m₁ m₁~Tt y∉Γ (∉-cons-r (ΛFV m) _ x∉FVm) (∉-cons-r (ΛFV m) _ y∉FVm) x≠y x₁) x₂ x₃
aux (app m m₁) m~Tt y∉Γ x∉FVm y∉FVm x≠y (~>∩ x∷Γ⊩m^'x∶τ' x∷Γ⊩m^'x∶τ'' x₁) =
  ~>∩ (aux (app m m₁) m~Tt y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ') (aux (app m m₁) m~Tt y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ'') x₁
aux (Y _) l-Y y∉Γ x∉FVm y∉FVm x≠y(Y (cons x∉ x₁ wf-Γ) x₂ x₃) = Y (cons y∉Γ x₁ wf-Γ) x₂ x₃
aux {k = k} (Y B) m~Tt y∉Γ x∉FVm y∉FVm x≠y (~>∩ x∷Γ⊩m^'x∶τ' x∷Γ⊩m^'x∶τ'' x₁) =
  ~>∩ (aux {k = k} (Y B) m~Tt y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ') (aux {k = k} (Y B) m~Tt y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩m^'x∶τ'') x₁

auxₗ m m~Tt y∉Γ _ _ _ (nil (cons x∉ x₁ wf-Γ)) = nil (cons y∉Γ x₁ wf-Γ)
auxₗ m m~Tt y∉Γ x∉FVm y∉FVm x≠y (cons x₁ x∷Γ⊩ₗm^'x∶τ') = cons (aux m m~Tt y∉Γ x∉FVm y∉FVm x≠y x₁) (auxₗ m m~Tt y∉Γ x∉FVm y∉FVm x≠y x∷Γ⊩ₗm^'x∶τ')



subst-⊩-2-aux : ∀ {A B Γ τ x} {m : Λ A} {n : Λ B} {t} -> m ~T t -> ΛTerm m -> ΛTerm n -> x ∉ dom Γ -> Γ ⊩ (m Λ[ x ::= n ]) ∶ τ ->
  ∃(λ τᵢ -> ( ((x , τᵢ , B) ∷ Γ) ⊩ m ∶ τ ) × ( Γ ⊩ₗ n ∶ τᵢ ))
subst-⊩ₗ-2-aux : ∀ {A B Γ τ x} {m : Λ A} {n : Λ B} {t} -> m ~T t -> ΛTerm m -> ΛTerm n -> x ∉ dom Γ -> Γ ⊩ₗ (m Λ[ x ::= n ]) ∶ τ ->
  ∃(λ τᵢ -> ( ((x , τᵢ , B) ∷ Γ) ⊩ₗ m ∶ τ ) × ( Γ ⊩ₗ n ∶ τᵢ ))

subst-⊩-2-aux {x = x} l-fv (var {x = y}) trm-n x∉Γ Γ⊩m[x::=n] with x ≟ y
subst-⊩-2-aux {A} {B} l-fv var trm-n x∉Γ Γ⊩m[x::=n] | yes refl with A ≟T B
subst-⊩-2-aux {τ = τ} l-fv var trm-n x∉Γ Γ⊩m[x::=n] | yes refl | yes refl = (∩' τ) ,
  (var (cons x∉Γ (cons (⊩-∷' Γ⊩m[x::=n]) nil) (⊩-wf-Γ Γ⊩m[x::=n])) (here refl) (⊆ₗ-refl (cons (⊩-∷' Γ⊩m[x::=n]) nil)) ,
  (cons Γ⊩m[x::=n] (nil (⊩-wf-Γ Γ⊩m[x::=n]))))

subst-⊩-2-aux l-fv var trm-n x∉Γ Γ⊩m[x::=n] | yes refl | no _ = ⊥-elim (x∉Γ (contr Γ⊩m[x::=n]))
  where
  contr : ∀ {Γ A x τ} -> Γ ⊩ (fv {A} x) ∶ τ -> x ∈ dom Γ
  contr (var wf-Γ τᵢ∈Γ τ⊆τᵢ) = ∈-imp-∈dom τᵢ∈Γ
  contr (~>∩ Γ⊩x∶τ Γ⊩x∶τ₁ x₁) = contr Γ⊩x∶τ₁

subst-⊩-2-aux {A} {B} l-fv var trm-n x∉Γ Γ⊩m[x::=n] | no _ = ω , ((sub Γ⊩m[x::=n] (⊆-refl (⊩-∷' Γ⊩m[x::=n])) (⊆Γ-⊆ (cons x∉Γ nil (⊩-wf-Γ Γ⊩m[x::=n])) (λ {x₁} → there))) , (nil (⊩-wf-Γ Γ⊩m[x::=n])))
subst-⊩-2-aux {A ⟶ B} {C} {Γ} {τ ~> τ'} {x} {_} {n} (un m~Tt) (lam L {m} cf) trm-n x∉Γ (abs L' cf' x₁) = τᵢ ,
  (abs (x' ∷ x ∷ dom Γ ++ ΛFV m)
    (λ x∉ -> auxₗ
      m
      m~Tt
      (∉-∷ _ (dom Γ) (λ x₂ → fv-x≠y _ _ (∉-∷-elim _ x∉) x₂) (∉-cons-l (dom Γ) _ (∉-∷-elim _ (∉-∷-elim _ x∉))))
      (∉-cons-l (ΛFV m) _ (∉-cons-r (dom Γ) _ (∉-cons-r L' _ (∉-cons-r L _ (∉-∷-elim _ x'∉)))))
      (∉-cons-r (dom Γ) _ (∉-∷-elim _ (∉-∷-elim _ x∉)))
      (λ x₂ → fv-x≠y _ _ x∉ (sym x₂))
      x∷x'∷Γ⊩ₗm^x∶τ')
    x₁) ,
  Γ⊩ₗn∶τᵢ
  where
  x' = ∃fresh-impl (x ∷ L ++ L' ++ dom Γ ++ ΛFV m ++ ΛFV n)

  x'∉ : x' ∉ (x ∷ L ++ L' ++ dom Γ ++ ΛFV m ++ ΛFV n)
  x'∉ = ∃fresh-impl-spec (x ∷ L ++ L' ++ dom Γ ++ ΛFV m ++ ΛFV n)

  ih' : ((x' , τ , A) ∷ Γ) ⊩ₗ (Λ[ 0 >> fv {A} x' ] m) Λ[ x ::= n ] ∶ τ'
  ih' rewrite Λsubst-open-var2 {τ'' = A} x' x n m (fv-x≠y _ _ x'∉) trm-n = cf' (∉-cons-l L' _ (∉-cons-r L _ (∉-∷-elim _ x'∉)))

  ih : ∃(λ τᵢ₁ ->
    (((x , τᵢ₁ , C) ∷ (x' , τ , A) ∷ Γ) ⊩ₗ Λ[ 0 >> fv x' ] m ∶ τ') × (((x' , τ , A) ∷ Γ) ⊩ₗ n ∶ τᵢ₁))
  ih = subst-⊩ₗ-2-aux (^'-~T-inv m~Tt) (cf (∉-cons-l L _ (∉-∷-elim _ x'∉))) trm-n (∉-∷ _ (dom Γ) (λ x₂ -> fv-x≠y _ _ x'∉ (sym x₂)) x∉Γ) ih'

  τᵢ = proj₁ ih

  x∷x'∷Γ⊩ₗm^x∶τ' : ((x' , τ , A) ∷ (x , τᵢ , C) ∷ Γ) ⊩ₗ Λ[ 0 >> fv x' ] m ∶ τ'
  x∷x'∷Γ⊩ₗm^x∶τ' = exchange-⊩ₗ (proj₁ (proj₂ ih))

  Γ⊩ₗn∶τᵢ : Γ ⊩ₗ n ∶ τᵢ
  Γ⊩ₗn∶τᵢ = strenghten-⊩ₗ (∉-cons-r (ΛFV m) _ (∉-cons-r (dom Γ) _ (∉-cons-r L' _ (∉-cons-r L _ (∉-∷-elim _ x'∉))))) (proj₂ (proj₂ ih))

subst-⊩-2-aux {B = B} {Γ} {x = x} m~Tt (lam L {e = m} cf) trm-n x∉Γ (~>∩ Γ⊩m[x::=n] Γ⊩m[x::=n]₁ x₁) = τₗ ++ τᵣ ,
  sub
    (~>∩
      (sub {Γ' = ((x , τₗ ++ τᵣ , B) ∷ Γ)} x∷Γ⊩m∶τₗ (⊆-refl (⊩-∷' Γ⊩m[x::=n])) ⊆Γₗ)
      (sub x∷Γ⊩m∶τᵣ (⊆-refl (⊩-∷' Γ⊩m[x::=n]₁)) ⊆Γᵣ)
      (⊆ₗ-refl (++-∷'ₗ (proj₂ (arr' (⊩-∷' Γ⊩m[x::=n]))) (proj₂ (arr' (⊩-∷' Γ⊩m[x::=n]₁))))))
    (arr (⊆ₗ-refl τ∷) x₁ (arr τ∷ (⊆ₗ-∷'ₗ-l x₁)) (arr τ∷ (⊆ₗ-∷'ₗ-r x₁)))
    (⊆Γ-⊆ wf-x∷Γ (λ x₃ → x₃)) ,
  ⊩ₗ-++ Γ⊩n∶τₗ Γ⊩n∶τᵣ
  where
  ihₗ = subst-⊩-2-aux m~Tt (lam L {e = m} cf) trm-n x∉Γ Γ⊩m[x::=n]
  ihᵣ = subst-⊩-2-aux m~Tt (lam L {e = m} cf) trm-n x∉Γ Γ⊩m[x::=n]₁
  τₗ = proj₁ ihₗ
  τᵣ = proj₁ ihᵣ
  x∷Γ⊩m∶τₗ = proj₁ (proj₂ ihₗ)
  x∷Γ⊩m∶τᵣ = proj₁ (proj₂ ihᵣ)
  Γ⊩n∶τₗ = proj₂ (proj₂ ihₗ)
  Γ⊩n∶τᵣ = proj₂ (proj₂ ihᵣ)

  τₗ++τᵣ∷' : (τₗ ++ τᵣ) ∷'ₗ B
  τₗ++τᵣ∷' = ++-∷'ₗ (⊩ₗ-∷'ₗ Γ⊩n∶τₗ) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ)

  wf-x∷Γ : Wf-ICtxt ((x , τₗ ++ τᵣ , B) ∷ Γ)
  wf-x∷Γ = cons x∉Γ τₗ++τᵣ∷' (⊩-wf-Γ Γ⊩m[x::=n]₁)

  ⊆Γₗ : ((x , τₗ , B) ∷ Γ) ⊆Γ ((x , τₗ ++ τᵣ , B) ∷ Γ)
  ⊆Γₗ = cons ((τₗ ++ τᵣ) , ((here refl) , ⊆ₗ++-l' (⊩ₗ-∷'ₗ Γ⊩n∶τₗ) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))

  ⊆Γᵣ : ((x , τᵣ , B) ∷ Γ) ⊆Γ ((x , τₗ ++ τᵣ , B) ∷ Γ)
  ⊆Γᵣ = cons ((τₗ ++ τᵣ) , ((here refl) , ⊆ₗ++-r (nil (⊩ₗ-∷'ₗ Γ⊩n∶τₗ)) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))

  τ∷ = proj₁ (arr' (⊩-∷' Γ⊩m[x::=n]₁))

subst-⊩-2-aux {B = B} {Γ} {x = x} (bin m~Tt m₁~Tt) (app trm-m trm-m₁) trm-n x∉Γ (app Γ⊩e₁[x::=n] Γ⊩ₗe₂[x::=n] x₂ x₃) = τₗ ++ τᵣ ,
  (app (sub x∷Γ⊩m∶τₗ (⊆-refl (⊩-∷' Γ⊩e₁[x::=n])) ⊆Γₗ) (subₗ x∷Γ⊩m∶τᵣ (⊆ₗ-refl (⊩ₗ-∷'ₗ Γ⊩ₗe₂[x::=n])) ⊆Γᵣ) x₂ x₃) ,
  (⊩ₗ-++ Γ⊩n∶τₗ Γ⊩n∶τᵣ)
  where
  ihₗ = subst-⊩-2-aux m~Tt trm-m trm-n x∉Γ Γ⊩e₁[x::=n]
  ihᵣ = subst-⊩ₗ-2-aux m₁~Tt trm-m₁ trm-n x∉Γ Γ⊩ₗe₂[x::=n]
  τₗ = proj₁ ihₗ
  τᵣ = proj₁ ihᵣ
  x∷Γ⊩m∶τₗ = proj₁ (proj₂ ihₗ)
  x∷Γ⊩m∶τᵣ = proj₁ (proj₂ ihᵣ)
  Γ⊩n∶τₗ = proj₂ (proj₂ ihₗ)
  Γ⊩n∶τᵣ = proj₂ (proj₂ ihᵣ)

  τₗ++τᵣ∷' : (τₗ ++ τᵣ) ∷'ₗ B
  τₗ++τᵣ∷' = ++-∷'ₗ (⊩ₗ-∷'ₗ Γ⊩n∶τₗ) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ)

  wf-x∷Γ : Wf-ICtxt ((x , τₗ ++ τᵣ , B) ∷ Γ)
  wf-x∷Γ = cons x∉Γ τₗ++τᵣ∷' (⊩-wf-Γ Γ⊩e₁[x::=n])

  ⊆Γₗ : ((x , τₗ , B) ∷ Γ) ⊆Γ ((x , τₗ ++ τᵣ , B) ∷ Γ)
  ⊆Γₗ = cons ((τₗ ++ τᵣ) , ((here refl) , ⊆ₗ++-l' (⊩ₗ-∷'ₗ Γ⊩n∶τₗ) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))

  ⊆Γᵣ : ((x , τᵣ , B) ∷ Γ) ⊆Γ ((x , τₗ ++ τᵣ , B) ∷ Γ)
  ⊆Γᵣ = cons ((τₗ ++ τᵣ) , ((here refl) , ⊆ₗ++-r (nil (⊩ₗ-∷'ₗ Γ⊩n∶τₗ)) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))

subst-⊩-2-aux {B = B} {Γ} {x = x} m~Tt (app trm-m trm-m₁) trm-n x∉Γ (~>∩ Γ⊩m[x::=n] Γ⊩m[x::=n]₁ x₁) = τₗ ++ τᵣ ,
  sub
    (~>∩
      (sub {Γ' = ((x , τₗ ++ τᵣ , B) ∷ Γ)} x∷Γ⊩m∶τₗ (⊆-refl (⊩-∷' Γ⊩m[x::=n])) ⊆Γₗ)
      (sub x∷Γ⊩m∶τᵣ (⊆-refl (⊩-∷' Γ⊩m[x::=n]₁)) ⊆Γᵣ)
      (⊆ₗ-refl (++-∷'ₗ (proj₂ (arr' (⊩-∷' Γ⊩m[x::=n]))) (proj₂ (arr' (⊩-∷' Γ⊩m[x::=n]₁))))))
    (arr (⊆ₗ-refl τ∷) x₁ (arr τ∷ (⊆ₗ-∷'ₗ-l x₁)) (arr τ∷ (⊆ₗ-∷'ₗ-r x₁)))
    (⊆Γ-⊆ wf-x∷Γ (λ x₃ → x₃)) ,
  ⊩ₗ-++ Γ⊩n∶τₗ Γ⊩n∶τᵣ
  where
  ihₗ = subst-⊩-2-aux m~Tt (app trm-m trm-m₁) trm-n x∉Γ Γ⊩m[x::=n]
  ihᵣ = subst-⊩-2-aux m~Tt (app trm-m trm-m₁) trm-n x∉Γ Γ⊩m[x::=n]₁
  τₗ = proj₁ ihₗ
  τᵣ = proj₁ ihᵣ
  x∷Γ⊩m∶τₗ = proj₁ (proj₂ ihₗ)
  x∷Γ⊩m∶τᵣ = proj₁ (proj₂ ihᵣ)
  Γ⊩n∶τₗ = proj₂ (proj₂ ihₗ)
  Γ⊩n∶τᵣ = proj₂ (proj₂ ihᵣ)

  τₗ++τᵣ∷' : (τₗ ++ τᵣ) ∷'ₗ B
  τₗ++τᵣ∷' = ++-∷'ₗ (⊩ₗ-∷'ₗ Γ⊩n∶τₗ) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ)

  wf-x∷Γ : Wf-ICtxt ((x , τₗ ++ τᵣ , B) ∷ Γ)
  wf-x∷Γ = cons x∉Γ τₗ++τᵣ∷' (⊩-wf-Γ Γ⊩m[x::=n]₁)

  ⊆Γₗ : ((x , τₗ , B) ∷ Γ) ⊆Γ ((x , τₗ ++ τᵣ , B) ∷ Γ)
  ⊆Γₗ = cons ((τₗ ++ τᵣ) , ((here refl) , ⊆ₗ++-l' (⊩ₗ-∷'ₗ Γ⊩n∶τₗ) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))

  ⊆Γᵣ : ((x , τᵣ , B) ∷ Γ) ⊆Γ ((x , τₗ ++ τᵣ , B) ∷ Γ)
  ⊆Γᵣ = cons ((τₗ ++ τᵣ) , ((here refl) , ⊆ₗ++-r (nil (⊩ₗ-∷'ₗ Γ⊩n∶τₗ)) (⊩ₗ-∷'ₗ Γ⊩n∶τᵣ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))

  τ∷ = proj₁ (arr' (⊩-∷' Γ⊩m[x::=n]₁))

subst-⊩-2-aux l-Y Y trm-n x∉Γ Γ⊩m[x::=n] = ω , (sub Γ⊩m[x::=n] (⊆-refl (⊩-∷' Γ⊩m[x::=n])) (⊆Γ-⊆ (cons x∉Γ nil (⊩-wf-Γ Γ⊩m[x::=n])) (λ {x} → there))) , (nil (⊩-wf-Γ Γ⊩m[x::=n]))

subst-⊩ₗ-2-aux m~Tt trm-m trm-n x∉Γ (nil wf-Γ) = ω , ((nil (cons x∉Γ nil wf-Γ)) , (nil wf-Γ))
subst-⊩ₗ-2-aux {B = B} {Γ} {x = x} m~Tt trm-m trm-n x∉Γ (cons x' Γ⊩ₗm∶τ) =
  τ ++ τₗ , (cons (sub x∷Γ⊩m∶τ (⊆-refl (⊩-∷' x')) ⊆Γ') (subₗ x∷Γ⊩m∶τₗ (⊆ₗ-refl (⊩ₗ-∷'ₗ Γ⊩ₗm∶τ)) ⊆Γₗ)) , ⊩ₗ-++ Γ⊩n∶τ Γ⊩n∶τₗ
  where
  ih = subst-⊩-2-aux m~Tt trm-m trm-n x∉Γ x'
  ihₗ = subst-⊩ₗ-2-aux m~Tt trm-m trm-n x∉Γ Γ⊩ₗm∶τ
  τ = proj₁ ih
  τₗ = proj₁ ihₗ
  x∷Γ⊩m∶τ = proj₁ (proj₂ ih)
  x∷Γ⊩m∶τₗ = proj₁ (proj₂ ihₗ)
  Γ⊩n∶τ = proj₂ (proj₂ ih)
  Γ⊩n∶τₗ = proj₂ (proj₂ ihₗ)

  τ++τₗ∷' : (τ ++ τₗ) ∷'ₗ B
  τ++τₗ∷' = ++-∷'ₗ (⊩ₗ-∷'ₗ Γ⊩n∶τ) (⊩ₗ-∷'ₗ Γ⊩n∶τₗ)

  wf-x∷Γ : Wf-ICtxt ((x , τ ++ τₗ , B) ∷ Γ)
  wf-x∷Γ = cons x∉Γ τ++τₗ∷' (⊩-wf-Γ x')

  ⊆Γ' : ((x , τ , B) ∷ Γ) ⊆Γ ((x , τ ++ τₗ , B) ∷ Γ)
  ⊆Γ' = cons ((τ ++ τₗ) , ((here refl) , ⊆ₗ++-l' (⊩ₗ-∷'ₗ Γ⊩n∶τ) (⊩ₗ-∷'ₗ Γ⊩n∶τₗ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))

  ⊆Γₗ : ((x , τₗ , B) ∷ Γ) ⊆Γ ((x , τ ++ τₗ , B) ∷ Γ)
  ⊆Γₗ = cons ((τ ++ τₗ) , ((here refl) , ⊆ₗ++-r (nil (⊩ₗ-∷'ₗ Γ⊩n∶τ)) (⊩ₗ-∷'ₗ Γ⊩n∶τₗ))) (⊆Γ-⊆ wf-x∷Γ (λ x₃ → there x₃))


subst-⊩-2 : ∀ {A B Γ τ x} {m : Λ A} {n : Λ B} -> ΛTerm m -> ΛTerm n -> x ∉ dom Γ -> Γ ⊩ (m Λ[ x ::= n ]) ∶ τ ->
  ∃(λ τᵢ -> ( ((x , τᵢ , B) ∷ Γ) ⊩ m ∶ τ ) × ( Γ ⊩ₗ n ∶ τᵢ ))
subst-⊩-2 {m = m} trm-m trm-n x∉Γ Γ⊩m[x::=n] = subst-⊩-2-aux (proj₂ (∃~T m)) trm-m trm-n x∉Γ Γ⊩m[x::=n]


subst-⊩ₗ-2 : ∀ {A B Γ τ x} {m : Λ A} {n : Λ B} -> ΛTerm m -> ΛTerm n -> x ∉ dom Γ -> Γ ⊩ₗ (m Λ[ x ::= n ]) ∶ τ ->
  ∃(λ τᵢ -> ( ((x , τᵢ , B) ∷ Γ) ⊩ₗ m ∶ τ ) × ( Γ ⊩ₗ n ∶ τᵢ ))
subst-⊩ₗ-2 {m = m} trm-m trm-n x∉Γ Γ⊩ₗm[x::=n] = subst-⊩ₗ-2-aux (proj₂ (∃~T m)) trm-m trm-n x∉Γ Γ⊩ₗm[x::=n]
