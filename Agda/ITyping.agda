module ITyping where

open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Product
-- open import Data.Maybe
open import Data.List.Any as LAny
open LAny.Membership-≡
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core


open import Core
open import Core-Lemmas
open import Typing
open import Reduction


data IType : Set where
  o : IType
  _~>_ : IType -> IType -> IType
  ∩ : List IType -> IType

ω = ∩ []

∩' : IType -> IType
∩' x = ∩ (x ∷ [])

~>-inj-l : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂} -> (τ₁₁ ~> τ₁₂) ≡ (τ₂₁ ~> τ₂₂) -> τ₁₁ ≡ τ₂₁
~>-inj-l refl = refl

~>-inj-r : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂} -> (τ₁₁ ~> τ₁₂) ≡ (τ₂₁ ~> τ₂₂) -> τ₁₂ ≡ τ₂₂
~>-inj-r refl = refl

∩-inj-cons : ∀ {x y τᵢ τⱼ} -> ∩ (x ∷ τᵢ) ≡ ∩ (y ∷ τⱼ) -> ∩ τᵢ ≡ ∩ τⱼ
∩-inj-cons refl = refl

∩-inj : ∀ {x y τᵢ τⱼ} -> ∩ (x ∷ τᵢ) ≡ ∩ (y ∷ τⱼ) -> x ≡ y
∩-inj refl = refl


_≟TI_ : Decidable {A = IType} _≡_
o ≟TI o = yes refl
o ≟TI (_ ~> _) = no (λ ())
o ≟TI (∩ _) = no (λ ())

(_ ~> _) ≟TI o = no (λ ())
(_ ~> _) ≟TI (∩ _) = no (λ ())
(τ₁₁ ~> τ₁₂) ≟TI (τ₂₁ ~> τ₂₂) with τ₁₁ ≟TI τ₂₁ | τ₁₂ ≟TI τ₂₂
(τ₁₁ ~> τ₁₂) ≟TI (.τ₁₁ ~> .τ₁₂) | yes refl | yes refl = yes refl
(τ₁₁ ~> τ₁₂) ≟TI (.τ₁₁ ~> τ₂₂) | yes refl | no τ₁₂≠τ₂₂ = no (λ eq → τ₁₂≠τ₂₂ (~>-inj-r eq))
(τ₁₁ ~> τ₁₂) ≟TI (τ₂₁ ~> τ₂₂) | no τ₁₁≠τ₂₁ | _ = no (λ eq → τ₁₁≠τ₂₁ (~>-inj-l eq))

(∩ _) ≟TI o = no (λ ())
(∩ _) ≟TI (_ ~> _) = no (λ ())
∩ [] ≟TI ∩ [] = yes refl
∩ [] ≟TI ∩ (x ∷ τⱼ) = no (λ ())
∩ (x ∷ τᵢ) ≟TI ∩ [] = no (λ ())
∩ (x ∷ τᵢ) ≟TI ∩ (y ∷ τⱼ) with x ≟TI y | (∩ τᵢ) ≟TI (∩ τⱼ)
∩ (x ∷ τᵢ) ≟TI ∩ (.x ∷ .τᵢ) | yes refl | yes refl = yes refl
∩ (x ∷ τᵢ) ≟TI ∩ (.x ∷ τⱼ) | yes refl | no τᵢ≠τⱼ = no (λ ∩x∷τᵢ≡∩x∷τⱼ → τᵢ≠τⱼ (∩-inj-cons ∩x∷τᵢ≡∩x∷τⱼ))
∩ (x ∷ τᵢ) ≟TI ∩ (y ∷ τⱼ) | no x≠y | _ = no (λ ∩x∷τᵢ≡∩y∷τⱼ → x≠y (∩-inj ∩x∷τᵢ≡∩y∷τⱼ))



ICtxt = List (Atom × IType)


data Wf-ICtxt : ICtxt -> Set where
  nil : Wf-ICtxt []
  cons : ∀ {Γ x τ} -> (x∉ : x ∉ dom Γ) -> Wf-ICtxt Γ ->
    Wf-ICtxt ((x , τ) ∷ Γ)


data _∷'_ : IType -> Type -> Set where
  base : o ∷' σ
  arr : ∀ {δ τ A B} -> δ ∷' A -> τ ∷' B -> (δ ~> τ) ∷' (A ⟶ B)
  ∩-nil : ∀ {A} ->  ω ∷' A
  ∩-cons : ∀ {τᵢ τ A} ->  τ ∷' A -> ∩ τᵢ ∷' A -> ∩ (τ ∷ τᵢ) ∷' A


data _≤∩_ : IType -> IType -> Set where
  base : o ≤∩ o
  arr : ∀ {τ₁₁ τ₁₂ τ₂₁ τ₂₂} -> τ₁₂ ≤∩ τ₂₂ -> τ₂₁ ≤∩ τ₁₁ -> (τ₁₁ ~> τ₁₂) ≤∩ (τ₂₁ ~> τ₂₂)
  ∩-∈ : ∀ {τ τᵢ} -> τ ∈ τᵢ -> ∩ τᵢ ≤∩ τ
  ∩-nil : ∀ {τ} -> τ ≤∩ ω
  ∩-cons : ∀ {τ τ' τᵢ} -> τ ≤∩ τ' -> τ ≤∩ ∩ τᵢ -> τ ≤∩ ∩ (τ' ∷ τᵢ)
  -- ∩-trans : ∀ {τ₁ τ₂ τ₃} -> τ₁ ≤∩ τ₂ -> τ₂ ≤∩ τ₃ -> τ₁ ≤∩ τ₃


∩τⱼ≤∩τᵢ : ∀ {τᵢ τⱼ} -> τᵢ ⊆ τⱼ -> ∩ τⱼ ≤∩ ∩ τᵢ
∩τⱼ≤∩τᵢ {[]} τᵢ⊆τⱼ = ∩-nil
∩τⱼ≤∩τᵢ {x ∷ τᵢ} τᵢ⊆τⱼ = ∩-cons (∩-∈ (τᵢ⊆τⱼ (here refl))) (∩τⱼ≤∩τᵢ (λ {x₁} z → τᵢ⊆τⱼ (there z)))

≤∩-refl : ∀ {τ} -> τ ≤∩ τ
≤∩-refl {o} = base
≤∩-refl {τ ~> τ₁} = arr ≤∩-refl ≤∩-refl
≤∩-refl {∩ []} = ∩-nil
≤∩-refl {∩ (x ∷ x₁)} = ∩τⱼ≤∩τᵢ (λ {x₂} z → z)


data Λ : Type -> Set where
  bv : ∀ {A} -> (i : ℕ) -> Λ A
  fv : ∀ {A} -> (x : Atom) -> Λ A
  lam : ∀ {B} -> (A : Type) -> (e : Λ B) -> Λ (A ⟶ B)
  app : ∀ {A B} -> (e₁ : Λ (A ⟶ B)) -> (e₂ : Λ A) -> Λ B
  Y : (t : Type) -> Λ ((t ⟶ t) ⟶ t)


-- _∈?_ : ∀ {a} {A : Set a} -> Atom -> List (Atom × A) -> Maybe A
-- a ∈? [] = nothing
-- a ∈? (l ∷ ist) with a ≟ proj₁ l
-- ... | yes _ = just (proj₂ l)
-- a ∈? (l ∷ ist) | no _ = a ∈? ist

-- PTerm->Λ : ∀ {Γ m t} -> (List (Atom × ℕ)) -> Γ ⊢ m ∶ t -> Λ t
-- PTerm->Λ {m = bv i} _ ()
-- PTerm->Λ {m = fv x} bound Γ⊢m∶t with x ∈? bound
-- PTerm->Λ {m = fv x} {t} bound Γ⊢m∶t | just i = bv {t} i
-- PTerm->Λ {m = fv x} bound Γ⊢m∶t | nothing = fv x
-- PTerm->Λ {m = lam m} bound (abs {_} {τ₁} {τ₂} L cf) = lam τ₁ (PTerm->Λ ((x , 0) ∷ bound') (cf (∉-cons-l _ _ x∉)))
--   where
--   x = ∃fresh (L ++ FV m)
--   x∉ : x ∉ (L ++ FV m)
--   x∉ = ∃fresh-spec (L ++ FV m)
--
--   bound' : List (Atom × ℕ)
--   bound' = Data.List.map (λ a,i → (proj₁ a,i) , suc (proj₂ a,i)) bound
--
-- PTerm->Λ {m = app t1 t} bound (app Γ⊢s Γ⊢t) = app (PTerm->Λ bound Γ⊢s) (PTerm->Λ bound Γ⊢t)
-- PTerm->Λ {m = Y τ} bound (Y x) = Y τ
--
-- PTerm->Λ : ∀ {Γ m t} -> Γ ⊢ m ∶ t -> Λ t
-- PTerm->Λ = PTerm->Λ []

data _~_ : ∀{t} -> Λ t -> PTerm -> Set where
  bv : ∀ {t i} -> (bv {t} i) ~ (bv i)
  fv : ∀ {t x} -> (fv {t} x) ~ (fv x)
  lam : ∀ {t s m m'} -> m ~ m' -> (lam {s} t m) ~ (lam m')
  app : ∀ {t s m n m' n'} -> m ~ m' -> n ~ n' -> (app {t} {s} m n) ~ (app m' n')
  Y : ∀ {t} -> (Y t) ~ (Y t)

Λ[_<<_] : ∀ {t} -> ℕ -> Atom -> Λ t -> Λ t
Λ[ k << x ] (bv i) = bv i
Λ[ k << x ] (fv y) with x ≟ y
... | yes _ = bv k
... | no _ = fv y
Λ[ k << x ] (lam t m) = lam t (Λ[ (suc k) << x ] m)
Λ[ k << x ] (app t1 t2) = app (Λ[ k << x ] t1) (Λ[ k << x ] t2)
Λ[ k << x ] (Y t) = Y t



PTerm->Λ : ∀ {Γ m t} -> Γ ⊢ m ∶ t -> Λ t
PTerm->Λ {m = bv i} ()
PTerm->Λ {m = fv x} {t} Γ⊢m∶t = fv {t} x
PTerm->Λ {m = lam m} (abs {_} {τ₁} {τ₂} L cf) =
  lam τ₁ ( Λ[ 0 << ∃fresh (L ++ FV m) ]
    (PTerm->Λ (cf (∉-cons-l _ _ (∃fresh-spec (L ++ FV m)) ))) )
PTerm->Λ {m = app t1 t} (app Γ⊢s Γ⊢t) = app (PTerm->Λ Γ⊢s) (PTerm->Λ Γ⊢t)
PTerm->Λ {m = Y τ} (Y x) = Y τ


Λ*^-*^~ : ∀ {τ x k} t t' -> _~_ {τ} t t' -> Λ[ k << x ] t ~ ([ k << x ] t')
Λ*^-*^~ _ _ bv = bv
Λ*^-*^~ {x = x} (fv y) _ fv with x ≟ y
Λ*^-*^~ (fv x) .(fv x) fv | yes _ = bv
Λ*^-*^~ (fv y) .(fv y) fv | no _ = fv
Λ*^-*^~ _ _ (lam {m = m} {m'} t~t') = lam (Λ*^-*^~ m m' t~t')
Λ*^-*^~ _ _ (app {m = m} {n} {m'} {n'} t~t' t~t'') = app (Λ*^-*^~ m m' t~t') (Λ*^-*^~ n n' t~t'')
Λ*^-*^~ _ _ Y = Y



Λ*^-*^-swap : ∀ {t : Type} k n x y m -> ¬(k ≡ n) -> ¬(x ≡ y) -> Λ[_<<_] {t} k x (Λ[ n << y ] m) ≡ Λ[ n << y ] (Λ[ k << x ] m)
Λ*^-*^-swap k n x y (bv i) k≠n x≠y = refl
Λ*^-*^-swap k n x y (fv z) k≠n x≠y = {!   !}
Λ*^-*^-swap k n x y (lam A m) k≠n x≠y =
  cong (lam A) (Λ*^-*^-swap (suc k) (suc n) x y m (λ x₁ → k≠n (≡-suc x₁)) x≠y)
Λ*^-*^-swap k n x y (app m m') k≠n x≠y rewrite
  Λ*^-*^-swap k n x y m k≠n x≠y | Λ*^-*^-swap k n x y m' k≠n x≠y = refl
Λ*^-*^-swap k n x y (Y t) k≠n x≠y = refl


fv-^-Λ*^-refl : ∀ x t {k Γ τ} -> x ∉ FV t -> (Γ⊢t^x : Γ ⊢ [ k >> fv x ] t ∶ τ) -> (Λ[ k << x ] (PTerm->Λ Γ⊢t^x) ) ~ t
fv-^-Λ*^-refl x (bv n) x∉FVt ()
fv-^-Λ*^-refl x (fv y) x∉FVt Γ⊢t^x with x ≟ y
fv-^-Λ*^-refl x (fv .x) x∉FVt Γ⊢t^x | yes refl = ⊥-elim (x∉FVt (here refl))
fv-^-Λ*^-refl x (fv y) x∉FVt Γ⊢t^x | no x≠y = fv
fv-^-Λ*^-refl x (lam t) {k} {Γ} x∉FVt (abs {τ₁ = τ₁} {τ₂} L cf) = lam {!   !}
  --
  -- where
  -- x' = ∃fresh ( L ++ FV ([ suc k >> fv x ] t) )
  -- x'∉ = ∃fresh-spec ( L ++ FV ([ suc k >> fv x ] t) )
  --
  -- x'Γ⊢[suc-k>>x]t^'x' : ((x' , τ₁) ∷ Γ) ⊢ ([ suc k >> fv x ] t) ^' x' ∶ τ₂
  -- x'Γ⊢[suc-k>>x]t^'x' = cf (∉-cons-l L (FV ([ suc k >> fv x ] t)) (∃fresh-spec (L ++ FV ([ suc k >> fv x ] t))))
  --
  --
  -- x'Γ⊢[suc-k>>x]t^'x'≡ : ((x' , τ₁) ∷ Γ) ⊢ [ suc k >> fv x ] (t ^' x') ∶ τ₂ ≡
  --   ((x' , τ₁) ∷ Γ) ⊢ ([ suc k >> fv x ] t) ^' x' ∶ τ₂
  -- x'Γ⊢[suc-k>>x]t^'x'≡ rewrite ^-^-swap (suc k) 0 x x' t (λ ()) (λ x≡x' → {!   !}) = refl
  --
  -- x'Γ⊢[suc-k>>x]t^'x'' : ((x' , τ₁) ∷ Γ) ⊢ [ suc k >> fv x ] (t ^' x') ∶ τ₂
  -- x'Γ⊢[suc-k>>x]t^'x'' rewrite x'Γ⊢[suc-k>>x]t^'x'≡ = x'Γ⊢[suc-k>>x]t^'x'
  --
  -- ih'' : Λ[ (suc k) << x ] (PTerm->Λ x'Γ⊢[suc-k>>x]t^'x'') ~ (t ^' x')
  -- ih'' = fv-^-Λ*^-refl x ([ 0 >> fv x' ] t) {!   !} x'Γ⊢[suc-k>>x]t^'x''
  --
  -- -- ih' : Λ[ 0 << x' ] ( Λ[ (suc k) << x ] (PTerm->Λ x'Γ⊢[suc-k>>x]t^'x') ) ~ t
  -- -- ih' rewrite x'Γ⊢[suc-k>>x]t^'x'≡ = {!   !}
  --
  -- ih : Λ[ (suc k) << x ] ( Λ[ 0 << x' ] (PTerm->Λ x'Γ⊢[suc-k>>x]t^'x') ) ~ t
  -- ih rewrite
  --   Λ*^-*^-swap {τ₂} (suc k) 0 x x' (PTerm->Λ x'Γ⊢[suc-k>>x]t^'x') {!   !} {!   !} |
  --   x'Γ⊢[suc-k>>x]t^'x'≡ = {!   !}

fv-^-Λ*^-refl x (app s t) x∉FVt (app Γ⊢s^x Γ⊢t^x) = app
  (fv-^-Λ*^-refl x s (∉-cons-l _ _ x∉FVt) Γ⊢s^x)
  (fv-^-Λ*^-refl x t (∉-cons-r (FV s) _ x∉FVt) Γ⊢t^x)
fv-^-Λ*^-refl x (Y τ) x∉FVt (Y x₁) = Y



PTerm->Λ~ : ∀ {Γ t τ} -> {Γ⊢t : Γ ⊢ t ∶ τ} -> (PTerm->Λ Γ⊢t) ~ t
PTerm->Λ~ {t = bv i} = λ {τ} → λ {}
PTerm->Λ~ {t = fv x} = λ {τ} {Γ⊢t} → fv
PTerm->Λ~ {t = lam t} {Γ⊢t = abs {τ₁ = τ₁} {τ₂} L cf} =
  lam (fv-^-Λ*^-refl (∃fresh (L ++ FV t)) t (∉-cons-r L _ (∃fresh-spec (L ++ FV t))) (cf (∉-cons-l L (FV t) (∃fresh-spec (L ++ FV t)))))
  -- where
  -- x' = ∃fresh (L ++ FV t)
  -- x'∷Γ⊢t^'x' = cf (∉-cons-l L (FV t) (∃fresh-spec (L ++ FV t)))
  --
  -- ih' : Λ[ 0 << x' ] (PTerm->Λ x'∷Γ⊢t^'x') ~ (* x' ^ (t ^' x'))
  -- ih' = {!   !}
  --
  -- sub : ∀ {τ x m} -> x ∉ FV t -> _~_ {τ} m t ≡ m ~ (* x ^ (t ^' x))
  -- sub {_} {x} x∉ rewrite fv-^-*^-refl x t {0} x∉ = refl
  --
  -- ih : Λ[ 0 << x' ] (PTerm->Λ x'∷Γ⊢t^'x') ~ t
  -- ih rewrite sub {_} {x'} {Λ[ 0 << x' ] (PTerm->Λ x'∷Γ⊢t^'x')} {!   !} = ih'
PTerm->Λ~ {t = app t t₁} {Γ⊢t = app Γ⊢t Γ⊢t₁} = app PTerm->Λ~ PTerm->Λ~
PTerm->Λ~ {t = Y t₁} {Γ⊢t = Y x} = Y


Λ->PTerm : ∀ {t} -> Λ t -> PTerm
Λ->PTerm (bv i) = bv i
Λ->PTerm (fv x) = fv x
Λ->PTerm (lam A Λt) = lam (Λ->PTerm Λt)
Λ->PTerm (app Λs Λt) = app (Λ->PTerm Λs) (Λ->PTerm Λt)
Λ->PTerm (Y t) = Y t





-- data ITypeₛ : IType -> Set where
--   o : ITypeₛ o
--   arr : ∀ {τ τ'} -> ITypeₛ τ -> ITypeₛ τ' -> ITypeₛ (τ ~> τ')
--
-- data ITypeₛₛ : IType -> Set where
--   o : ITypeₛₛ o
--   arr :  ∀ {τ τ'} -> ITypeₛₛ τ -> ITypeₛₛ τ' -> ITypeₛₛ (τ ~> τ')
--   ∩-nil : ITypeₛₛ ω
--   ∩-cons : ∀ {τ τᵢ} -> ITypeₛ τ ->  ITypeₛₛ (∩ τᵢ) -> ITypeₛₛ (∩ (τ ∷ τᵢ))
--
-- τₛ->τₛₛ : ∀ {τ} -> ITypeₛ τ -> ITypeₛₛ τ
-- τₛ->τₛₛ o = o
-- τₛ->τₛₛ (arr τₛ τₛ₁) = arr (τₛ->τₛₛ τₛ) (τₛ->τₛₛ τₛ₁)

Λ[_>>_] : ∀ {τ τ'} -> ℕ -> Λ τ' -> Λ τ -> Λ τ
Λ[_>>_] {τ} {τ'} k u (bv i) with k ≟ i | τ ≟T τ'
Λ[ k >> u ] (bv i) | yes _ | yes refl = u
... | yes _ | no _ = bv i
... | no _ | _ = bv i
Λ[ k >> u ] (fv x) = fv x
Λ[ k >> u ] (lam A t) = lam A (Λ[ (suc k) >> u ] t)
Λ[ k >> u ] (app t1 t2) = app (Λ[ k >> u ] t1) (Λ[ k >> u ] t2) -- app (Λ[ k >> u ] t1) (Λ[ k >> u ] t2)
Λ[ k >> u ] (Y t) = Y t


data Y-shape : ∀ {τ} -> Λ τ -> Set where
  intro₁ : ∀ {A m} -> Y-shape (app (Y A) m)
  intro₂ : ∀ {A m} -> Y-shape (app m (app (Y A) m))

data _⊩_∶_ : ∀ {A} -> ICtxt -> Λ A -> IType -> Set where
  var : ∀ {A Γ x τ} {τᵢ : List IType} -> (wf-Γ : Wf-ICtxt Γ) -> (τᵢ∈Γ : (x , (∩ τᵢ)) ∈ Γ) -> (τᵢ≤∩τ : ∩ τᵢ ≤∩ τ) -> τ ∷' A ->
    Γ ⊩ fv {A} x ∶ τ
  app : ∀ {A B Γ s t τ₁ τ₂} -> Γ ⊩ s ∶ (τ₁ ~> τ₂) -> Γ ⊩ t ∶ τ₁ -> (τ₁ ~> τ₂) ∷' (A ⟶ B) -> τ₁ ∷' B ->
    Γ ⊩ (app {A} {B} s t) ∶ τ₂
  ∩-nil : ∀ {A Γ} {m : Λ A} -> (¬Y-shape : ¬ Y-shape m) -> (wf-Γ : Wf-ICtxt Γ) -> Γ ⊩ m  ∶ ω
  ∩-cons : ∀ {A Γ τ τᵢ} {m : Λ A} -> (¬Y-shape : ¬ Y-shape m) -> (wf-Γ : Wf-ICtxt Γ) ->
    Γ ⊩ m  ∶ τ -> Γ ⊩ m  ∶ (∩ τᵢ) -> Γ ⊩ m  ∶ (∩ (τ ∷ τᵢ))
  abs : ∀ {A B Γ τᵢ τ} (L : FVars) -> ∀ {t : Λ B} ->
    ( cf : ∀ {x} -> (x∉L : x ∉ L) -> ((x , ∩ τᵢ) ∷ Γ) ⊩ Λ[ 0 >> fv {A} x ] t ∶ τ ) -> ∩ τᵢ ∷' A -> τ ∷' B -> Γ ⊩ lam A t ∶ (∩ τᵢ ~> τ)
  Y : ∀ {Γ A τ τ₁ τ₂} -> Wf-ICtxt Γ -> τ ∷' A -> τ₁ ∷' A -> τ₂ ∷' A ->
    Γ ⊩ Y A ∶ ((τ ~> τ₁) ~> τ₂)


-- ⊩->β : ∀ {Γ m m' τ} -> Γ ⊩ m' ∶ τ -> m ->β m' -> Γ ⊩ m ∶ τ
-- ⊩->β Γ⊩m'∶τ (redL x m->βm') = ⊩->β-redL Γ⊩m'∶τ m->βm'
--   where
--   ⊩->β-redL : ∀ {Γ m m' n τ} -> Γ ⊩ app m' n ∶ τ -> m ->β m' -> Γ ⊩ app m n ∶ τ
--   ⊩->β-redL = {!   !}
-- ⊩->β Γ⊩m'∶τ (redR x m->βm') = {!   !}
-- ⊩->β Γ⊩m'∶τ (abs L x) = {!   !}
-- ⊩->β Γ⊩m'∶τ (beta x x₁) = {!   !}
-- ⊩->β {τ = τ} (app Γ⊩m∶τ'~>τ (app (Y {τ = τ'} wf-Γ τ∷ τ₁∷ τ₂∷) Γ⊩m∶τ'~>τ')) (Y trm-m) =
--     app (Y wf-Γ τ∷ τ₁∷ {!   !}) Γ⊩m∶τ'~>τ'
--
-- ⊩->β (app Γ⊩m'∶τ (∩-nil ¬Y-shape wf-Γ trm-m)) (Y x) = ⊥-elim (¬Y-shape intro₁)
-- ⊩->β (app Γ⊩m'∶τ (∩-cons ¬Y-shape wf-Γ trm-m Γ⊩m'∶τ₁ Γ⊩m'∶τ₂)) (Y x₁) = ⊥-elim (¬Y-shape intro₁)
-- ⊩->β (∩-nil ¬Y-shape wf-Γ trm-m) (Y x) = ⊥-elim (¬Y-shape intro₂)
-- ⊩->β (∩-cons ¬Y-shape wf-Γ trm-m Γ⊩m'∶τ Γ⊩m'∶τ₁) (Y x₁) = ⊥-elim (¬Y-shape intro₂)
--
--

-- ⊩->β Γ⊩m'∶τ (redL x m->βm') = ⊩->β-redL Γ⊩m'∶τ m->βm'
--   where
--   ⊩->β-redL : ∀ {Γ m m' n τ} -> Γ ⊩ app m' n ∶ τ -> m ->β m' -> Γ ⊩ app m n ∶ τ
--   ⊩->β-redL (app Γ⊩m'n∶τ Γ⊩m'n∶τ₁) (redL x₁ m->βm'') = app (⊩->β-redL Γ⊩m'n∶τ m->βm'') Γ⊩m'n∶τ₁
--   ⊩->β-redL (∩-intro Γ⊩m''n₁n₂∶τᵢ wf-Γ (app _ trm-n₂)) (redL trm-n₁ m->βm'') =
--     ∩-intro (λ τ∈τᵢ → ⊩->β-redL (Γ⊩m''n₁n₂∶τᵢ τ∈τᵢ) (redL trm-n₁ m->βm'')) wf-Γ (app (app (->β-Term-l m->βm'') trm-n₁) trm-n₂)
--   ⊩->β-redL (app Γ⊩m'n∶τ Γ⊩m'n∶τ₁) (redR x₁ m->βm'') = app (⊩->β Γ⊩m'n∶τ (redR x₁ m->βm'')) Γ⊩m'n∶τ₁
--   ⊩->β-redL (∩-intro Γ⊩m₁e₂n₂∶τᵢ wf-Γ (app (app _ trm-e₂) trm-n₂)) (redR trm-m₁ n₁->e₂) =
--     ∩-intro (λ τ∈τᵢ → ⊩->β (Γ⊩m₁e₂n₂∶τᵢ τ∈τᵢ) (redL trm-n₂ (redR trm-m₁ n₁->e₂))) wf-Γ (app (app trm-m₁ (->β-Term-l n₁->e₂)) trm-n₂)
--   ⊩->β-redL (app Γ⊩m'n∶τ Γ⊩m'n∶τ₁) (abs L cf) = app (⊩->β Γ⊩m'n∶τ (abs L cf)) Γ⊩m'n∶τ₁
--   ⊩->β-redL (∩-intro Γ⊩lam-m''n₁∶τᵢ wf-Γ (app trm-lam-m'' trm-n₁)) (abs L cf) =
--     ∩-intro (λ τ∈τᵢ → ⊩->β (Γ⊩lam-m''n₁∶τᵢ τ∈τᵢ) (redL trm-n₁ (abs L cf))) wf-Γ (app (lam L (λ x∉L → ->β-Term-l (cf x∉L))) trm-n₁)
--   ⊩->β-redL (app Γ⊩m'n∶τ Γ⊩m'n∶τ₁) (beta trm-lam-m₁ trm-n₁) = app (⊩->β Γ⊩m'n∶τ (beta trm-lam-m₁ trm-n₁)) Γ⊩m'n∶τ₁
--   ⊩->β-redL (∩-intro Γ⊩m₁^n₁n₂∶τ₁ wf-Γ (app trm-m₁^n₁ trm-n₂)) (beta trm-lam-m₁ trm-n₁) =
--     ∩-intro (λ τ∈τᵢ → ⊩->β (Γ⊩m₁^n₁n₂∶τ₁ τ∈τᵢ) (redL trm-n₂ (beta trm-lam-m₁ trm-n₁))) wf-Γ (app (app trm-lam-m₁ trm-n₁) trm-n₂)
--   ⊩->β-redL (app Γ⊩m'n∶τ Γ⊩m'n∶τ₁) (Y trm-m₁) = app (⊩->β Γ⊩m'n∶τ (Y trm-m₁)) Γ⊩m'n∶τ₁
--   ⊩->β-redL (∩-intro Γ⊩m₁Ym₁n₁∶τᵢ wf-Γ (app (app _ trm-Ym₁) trm-n₁)) (Y trm-m₁) =
--     ∩-intro (λ τ∈τᵢ → ⊩->β (Γ⊩m₁Ym₁n₁∶τᵢ τ∈τᵢ) (redL trm-n₁ (Y trm-m₁))) wf-Γ (app trm-Ym₁ trm-n₁)
--
-- ⊩->β (app Γ⊩m'∶τ Γ⊩m'∶τ₁) (redR trm-n m->βm') = app Γ⊩m'∶τ (⊩->β Γ⊩m'∶τ₁ m->βm')
-- ⊩->β (∩-intro Γ⊩mn'∶τᵢ wf-Γ trm-mn') (redR trm-m n->βn') =
--   ∩-intro (λ τ∈τᵢ → ⊩->β (Γ⊩mn'∶τᵢ τ∈τᵢ) (redR trm-m n->βn')) wf-Γ (app trm-m (->β-Term-l n->βn'))
-- ⊩->β (∩-intro Γ⊩lam-m'∶τᵢ wf-Γ trm-lam-x) (abs L x₂) =
--   ∩-intro (λ τ∈τᵢ → ⊩->β (Γ⊩lam-m'∶τᵢ τ∈τᵢ) (abs L x₂)) wf-Γ (lam L (λ x∉L → ->β-Term-l (x₂ x∉L)))
-- ⊩->β (abs L cf) (abs L₁ x) = abs (L ++ L₁) (λ x∉L → ⊩->β (cf (∉-cons-l _ _ x∉L)) (x (∉-cons-r L _ x∉L)))
-- ⊩->β Γ⊩m'∶τ (beta x x₁) = {!   !}
-- ⊩->β (app Γ⊩m'∶τ'~>τ (app Γ⊩Ym∶τ' Γ⊩Ym∶τ'')) (Y trm-m) = {!   !}
-- ⊩->β (app Γ⊩m'∶τ'~>τ (∩-intro {τᵢ = []} Γ⊩Ym∶τᵢ wf-Γ trm-Ym)) (Y trm-m) = {!   !}
-- ⊩->β {Γ} (app {s = m} Γ⊩m'∶τ'~>τ (∩-intro {τᵢ = x ∷ τᵢ} Γ⊩Ym∶τᵢ wf-Γ trm-Ym)) (Y trm-m) = {!   !}
--   where
--   Γ⊩m∶x~>x : Γ ⊩ m ∶ (x ~> x)
--   Γ⊩m∶x~>x = {!   !}
-- ⊩->β (∩-intro Γ⊩mYm∶τᵢ wf-Γ (app _ trm-Ym)) (Y trm-m) =
--   ∩-intro (λ τ∈τᵢ → ⊩->β (Γ⊩mYm∶τᵢ τ∈τᵢ) (Y trm-m)) wf-Γ trm-Ym
