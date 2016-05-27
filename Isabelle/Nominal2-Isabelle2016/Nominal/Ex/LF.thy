theory LF
imports "../Nominal2"
begin

atom_decl name
atom_decl ident

nominal_datatype lf:
    kind =
      Type
    | KPi "ty" n::"name" k::"kind" binds n in k
and ty =
      TConst "ident"
    | TApp "ty" "trm"
    | TPi "ty" n::"name" ty::"ty"   binds n in ty
and trm =
      Const "ident"
    | Var "name"
    | App "trm" "trm"
    | Lam' "ty" n::"name" t::"trm"  binds n in t

abbreviation
  KPi_syn::"name \<Rightarrow> ty \<Rightarrow> kind \<Rightarrow> kind" ("\<Pi>[_:_]._" [100,100,100] 100)
where 
  "\<Pi>[x:A].K \<equiv> KPi A x K"

abbreviation
  TPi_syn::"name \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty" ("\<Pi>[_:_]._" [100,100,100] 100)
where 
  "\<Pi>[x:A1].A2 \<equiv> TPi A1 x A2"

abbreviation
  Lam_syn::"name \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm" ("Lam [_:_]._" [100,100,100] 100)
where 
  "Lam [x:A].M \<equiv> Lam' A x M"

thm lf.distinct
thm lf.induct
thm lf.inducts
thm lf.exhaust
thm lf.strong_exhaust
thm lf.fv_defs
thm lf.bn_defs
thm lf.perm_simps
thm lf.eq_iff
thm lf.fv_bn_eqvt
thm lf.size_eqvt
thm lf.supports
thm lf.fsupp
thm lf.supp
thm lf.fresh
thm lf.fresh[simplified]

nominal_datatype sig_ass =
    TC_ass "ident" "kind"
  | C_ass "ident" "ty"

type_synonym Sig = "sig_ass list"
type_synonym Ctx = "(name \<times> ty) list"
type_synonym Subst = "(name \<times> trm) list"

inductive
    sig_valid  :: "Sig \<Rightarrow> bool" ("\<turnstile> _ sig" [60] 60)
and ctx_valid  :: "Sig \<Rightarrow> Ctx \<Rightarrow> bool" ("_ \<turnstile> _ ctx" [60,60] 60)
and trm_valid  :: "Sig \<Rightarrow> Ctx \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> bool" ("_,_ \<turnstile> _ : _" [60,60,60,60] 60)
and ty_valid   :: "Sig \<Rightarrow> Ctx \<Rightarrow> ty \<Rightarrow> kind \<Rightarrow> bool" ("_,_ \<turnstile> _ : _" [60,60,60,60] 60)
and kind_valid :: "Sig \<Rightarrow> Ctx \<Rightarrow> kind \<Rightarrow> bool" ("_,_ \<turnstile> _ : Kind" [60,60,60] 60)
and trm_equiv  :: "Sig \<Rightarrow> Ctx \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> bool" ("_,_ \<turnstile> _ = _ : _" [60,60,60,60,60] 60)
and ty_equiv   :: "Sig \<Rightarrow> Ctx \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> kind \<Rightarrow> bool" ("_,_ \<turnstile> _ = _ : _" [60,60,60,60,60] 60)
and kind_equiv :: "Sig \<Rightarrow> Ctx \<Rightarrow> kind \<Rightarrow> kind \<Rightarrow> bool" ("_,_ \<turnstile> _ = _ : Kind" [60,60,60,60] 60)
where
(* Signatures *)
  s1: "\<turnstile> [] sig"
| s2: "\<lbrakk>\<turnstile> \<Sigma> sig; \<Sigma>,[] \<turnstile> K : Kind; atom a\<sharp>\<Sigma>\<rbrakk> \<Longrightarrow> \<turnstile> (TC_ass a K)#\<Sigma> sig"
| s3: "\<lbrakk>\<turnstile> \<Sigma> sig; \<Sigma>,[] \<turnstile> A : Type; atom c\<sharp>\<Sigma>\<rbrakk> \<Longrightarrow> \<turnstile> (C_ass c A)#\<Sigma> sig"

(* Contexts *)
| c1: "\<turnstile> \<Sigma> sig \<Longrightarrow> \<Sigma> \<turnstile> [] ctx"
| c2: "\<lbrakk>\<Sigma> \<turnstile> \<Gamma>  ctx; \<Sigma>,\<Gamma> \<turnstile> A : Type; atom x\<sharp>\<Gamma>\<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> (x,A)#\<Gamma> ctx"

(* Typing Terms *)
| t1: "\<lbrakk>\<Sigma> \<turnstile> \<Gamma>  ctx; (x,A) \<in> set \<Gamma>\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> (Var x) : A"
| t2: "\<lbrakk>\<Sigma> \<turnstile> \<Gamma>  ctx; C_ass c A \<in> set \<Sigma>\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> (Const c) : A"
| t3: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> M1 : \<Pi>[x:A2].A1; \<Sigma>,\<Gamma> \<turnstile> M2 : A2; atom x\<sharp>\<Gamma>\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> (App M1 M2) : A1"
| t4: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> A1 : Type; \<Sigma>,(x,A1)#\<Gamma> \<turnstile> M2 : A2; atom x\<sharp>(\<Gamma>,A1)\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> (Lam [x:A1].M2) : \<Pi>[x:A1].A2"
| t5: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> M : A; \<Sigma>,\<Gamma> \<turnstile> A = B : Type\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> M : B "

(* Typing Types *)
| f1: "\<lbrakk>\<Sigma> \<turnstile> \<Gamma>  ctx; TC_ass a K \<in> set \<Sigma>\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> (TConst a) : K"
| f2: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> A : \<Pi>[x:B].K; \<Sigma>,\<Gamma> \<turnstile> M : B; atom x\<sharp>\<Gamma>\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> (TApp A M) : K"
| f3: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> A1 : Type; \<Sigma>,(x,A1)#\<Gamma> \<turnstile> A2 : Type; atom x\<sharp>(\<Gamma>,A1)\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> (\<Pi>[x:A1].A2) : Type"
| f4: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> A : K; \<Sigma>,\<Gamma> \<turnstile> K = L : Kind\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> A : L"

(* Typing Kinds *)
| k1: "\<Sigma> \<turnstile> \<Gamma> ctx \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> Type : Kind"
| k2: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> A : Type; \<Sigma>,(x,A)#\<Gamma> \<turnstile> K : Kind; atom x\<sharp>(\<Gamma>,A)\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> (\<Pi>[x:A].K) : Kind"

(* Simultaneous Congruence for Terms *)
| q1: "\<lbrakk>\<Sigma> \<turnstile> \<Gamma>  ctx; (x,A) \<in> set \<Gamma>\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> (Var x) = (Var x) : A"
| q2: "\<lbrakk>\<Sigma> \<turnstile> \<Gamma>  ctx; C_ass c A \<in> set \<Sigma>\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> (Const c) = (Const c): A"
| q3: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> M1 = N1 : \<Pi>[x:A2].A1; \<Sigma>,\<Gamma> \<turnstile> M2 = N2 : A2; atom x\<sharp>\<Gamma>\<rbrakk> 
       \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> (App M1 M2) = (App N1 N2) : A1"
| q4: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> A1' = A1 : Type; \<Sigma>,\<Gamma> \<turnstile> A1'' = A1 : Type; \<Sigma>,\<Gamma> \<turnstile> A1 : Type;
        \<Sigma>,(x,A1)#\<Gamma> \<turnstile> M2 = N2 : A2; atom x\<sharp>\<Gamma>\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> (Lam [x:A1'].M2) = (Lam [x:A1''].N2) : \<Pi>[x:A1].A2"

(* Extensionality *)
| ex: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> M : \<Pi>[x:A1].A2; \<Sigma>,\<Gamma> \<turnstile> N : \<Pi>[x:A1].A2; \<Sigma>,\<Gamma> \<turnstile> A1 : Type;
        \<Sigma>,(x,A1)#\<Gamma> \<turnstile> App M (Var x) = App N (Var x) : A2; atom x\<sharp>\<Gamma>\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> M = N : \<Pi>[x:A1].A2"

(* Parallel Conversion *)
| pc: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> A1 : Type; \<Sigma>,(x,A1)#\<Gamma> \<turnstile> M2 = N2 : A2; \<Sigma>,\<Gamma> \<turnstile> M1 = N1 : A1; atom x\<sharp>\<Gamma>\<rbrakk> 
       \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> App (Lam [x:A1].M2) M1 = N2 : A2"

(* Equivalence *)
| e1: "\<Sigma>,\<Gamma> \<turnstile> M = N : A \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> N = M : (A::ty)"
| e2: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> M = N : A; \<Sigma>,\<Gamma> \<turnstile> N = P : A\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> M = P : (A::ty)"
(*| e3: "\<Sigma>,\<Gamma> \<turnstile> M : A \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> M = M : (A::ty)"*)

(* Type conversion *)
| tc: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> M = N : A; \<Sigma>,\<Gamma> \<turnstile> A = B : Type\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> M = N : B"

(* Types Conruence *)
| ft1: "\<lbrakk>\<Sigma> \<turnstile> \<Gamma>  ctx; TC_ass a K \<in> set \<Sigma>\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> (TConst a) = (TConst a) : K"
| ft2: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> A = B : \<Pi>[x:C].K; \<Sigma>,\<Gamma> \<turnstile> M = N : C; atom x\<sharp>\<Gamma>\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> (TApp A M) = (TApp B N) : K"
| ft3: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> A1 = B1 : Type; \<Sigma>,\<Gamma> \<turnstile> A1 : Type; \<Sigma>,(x,A1)#\<Gamma> \<turnstile> A2 = B2 : Type; atom x\<sharp>\<Gamma>\<rbrakk> 
       \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> \<Pi>[x:A1].A2 = \<Pi>[x:B1].B2 : Type"

(* Types Equivalence *)
| fe1: "\<Sigma>,\<Gamma> \<turnstile> A = (B::ty) : (K::kind) \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> B = A : K"
| fe2: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> A = B : K; \<Sigma>,\<Gamma> \<turnstile> B = C : K\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> A = C : (K::kind)"
(*| fe3: "\<Sigma>,\<Gamma> \<turnstile> A : K \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> A = A : (K::kind)"*)

(* Kind Conversion *)
| kc: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> A = B : K; \<Sigma>,\<Gamma> \<turnstile> K = L : Kind\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> A = B : (L::kind)"

(* Kind Congruence *)
| kc1: "\<Sigma> \<turnstile> \<Gamma> ctx \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> Type = Type : Kind"
| kc2: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> A = B : Type; \<Sigma>,\<Gamma> \<turnstile> A : Type; \<Sigma>,(x,A)#\<Gamma> \<turnstile> K = L : Kind; atom x\<sharp>\<Gamma>\<rbrakk> 
        \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> \<Pi>[x:A].K = \<Pi>[x:B].L : Kind"

(* Kind Equivalence *)
| ke1: "\<Sigma>,\<Gamma> \<turnstile> K = L : Kind \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> L = K : Kind"
| ke2: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> K = L : Kind; \<Sigma>,\<Gamma> \<turnstile> L = L' : Kind\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> K = L' : Kind"
(*| ke3: "\<Sigma>,\<Gamma> \<turnstile> K : Kind \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> K = K : Kind"*)

(* type extensionality - needed in order to get the soundness theorem through*)
| tex: "\<lbrakk>\<Sigma>,\<Gamma> \<turnstile> A : \<Pi>[x:C].K; \<Sigma>,\<Gamma> \<turnstile> B : \<Pi>[x:C].K; \<Sigma>,\<Gamma> \<turnstile> C : Type; 
         \<Sigma>,(x,C)#\<Gamma> \<turnstile> TApp A (Var x) = TApp B (Var x) : K; atom x\<sharp>\<Gamma>\<rbrakk> \<Longrightarrow> \<Sigma>,\<Gamma> \<turnstile> A = B : \<Pi>[x:C].K"


end




