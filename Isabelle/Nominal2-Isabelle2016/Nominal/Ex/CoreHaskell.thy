theory CoreHaskell
imports "../Nominal2"
begin

(* Core Haskell *)

atom_decl var
atom_decl cvar
atom_decl tvar

nominal_datatype core_haskell: 
 tkind =
  KStar
| KFun "tkind" "tkind"
and ckind =
  CKEq "ty" "ty"
and ty =
  TVar "tvar"
| TC "string"
| TApp "ty" "ty"
| TFun "string" "ty_lst"
| TAll tv::"tvar" "tkind" T::"ty"  binds (set) tv in T
| TEq "ckind" "ty"
and ty_lst =
  TsNil
| TsCons "ty" "ty_lst"
and co =
  CVar "cvar"
| CConst "string"
| CApp "co" "co"
| CFun "string" "co_lst"
| CAll cv::"cvar" "ckind" C::"co"  binds (set) cv in C
| CEq "ckind" "co"
| CRefl "ty"
| CSym "co"
| CCir "co" "co"
| CAt "co" "ty"
| CLeft "co"
| CRight "co"
| CSim "co" "co"
| CRightc "co"
| CLeftc "co"
| CCoe "co" "co"
and co_lst =
  CsNil
| CsCons "co" "co_lst"
and trm =
  Var "var"
| K "string"
| LAMT tv::"tvar" "tkind" t::"trm" binds (set) tv in t
| LAMC cv::"cvar" "ckind" t::"trm" binds (set) cv in t
| AppT "trm" "ty"
| AppC "trm" "co"
| Lam v::"var" "ty" t::"trm"       binds (set) v in t
| App "trm" "trm"
| Let x::"var" "ty" "trm" t::"trm" binds (set) x in t
| Case "trm" "assoc_lst"
| Cast "trm" "ty"                  --"ty is supposed to be a coercion type only"
and assoc_lst =
  ANil
| ACons p::"pat" t::"trm" "assoc_lst" binds "bv p" in t
and pat =
  Kpat "string" "tvars" "cvars" "vars"
and vars =
  VsNil
| VsCons "var" "ty" "vars"
and tvars =
  TvsNil
| TvsCons "tvar" "tkind" "tvars"
and cvars =
  CvsNil
| CvsCons "cvar" "ckind" "cvars"
binder
    bv :: "pat \<Rightarrow> atom list"
and bv_vs :: "vars \<Rightarrow> atom list"
and bv_tvs :: "tvars \<Rightarrow> atom list"
and bv_cvs :: "cvars \<Rightarrow> atom list"
where
  "bv (Kpat s tvts tvcs vs) = append (bv_tvs tvts) (append (bv_cvs tvcs) (bv_vs vs))"
| "bv_vs VsNil = []"
| "bv_vs (VsCons v k t) = (atom v) # bv_vs t"
| "bv_tvs TvsNil = []"
| "bv_tvs (TvsCons v k t) = (atom v) # bv_tvs t"
| "bv_cvs CvsNil = []"
| "bv_cvs (CvsCons v k t) = (atom v) # bv_cvs t"

(* generated theorems *)

thm core_haskell.permute_bn
thm core_haskell.perm_bn_alpha
thm core_haskell.perm_bn_simps
thm core_haskell.bn_finite

thm core_haskell.distinct
thm core_haskell.induct
thm core_haskell.inducts
thm core_haskell.strong_induct
thm core_haskell.exhaust
thm core_haskell.fv_defs
thm core_haskell.bn_defs
thm core_haskell.perm_simps
thm core_haskell.eq_iff
thm core_haskell.fv_bn_eqvt
thm core_haskell.size_eqvt
thm core_haskell.supp


end

