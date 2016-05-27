theory Modules
imports "../Nominal2"
begin

(* 
   example from Leroy'96 about modules

   see OTT example by Owens 
*)

atom_decl name

nominal_datatype modules: 
 mexp =
  Acc "path"
| Stru "body"
| Funct x::"name" "sexp" m::"mexp"    binds (set) x in m
| FApp "mexp" "path"
| Ascr "mexp" "sexp"
and body =
  Empty
| Seq c::"defn" d::"body"     binds (set) "cbinders c" in d
and defn =
  Type "name" "ty"
| Dty "name"
| DStru "name" "mexp"
| Val "name" "trm"
and sexp =
  Sig sbody
| SFunc "name" "sexp" "sexp"
and sbody =
  SEmpty
| SSeq C::"spec" D::"sbody"    binds (set) "Cbinders C" in D
and spec =
  Type1 "name"
| Type2 "name" "ty"
| SStru "name" "sexp"
| SVal "name" "ty"
and ty =
  Tyref1 "name"
| Tyref2 "path" "ty"
| Fun "ty" "ty"
and path =
  Sref1 "name"
| Sref2 "path" "name"
and trm =
  Tref1 "name"
| Tref2 "path" "name"
| Lam' v::"name" "ty" M::"trm"  binds (set) v in M
| App' "trm" "trm"
| Let' "body" "trm"
binder
    cbinders :: "defn \<Rightarrow> atom set"
and Cbinders :: "spec \<Rightarrow> atom set"
where
  "cbinders (Type t T) = {atom t}"
| "cbinders (Dty t) = {atom t}"
| "cbinders (DStru x s) = {atom x}"
| "cbinders (Val v M) = {atom v}"
| "Cbinders (Type1 t) = {atom t}"
| "Cbinders (Type2 t T) = {atom t}"
| "Cbinders (SStru x S) = {atom x}"
| "Cbinders (SVal v T) = {atom v}"


thm modules.perm_bn_alpha
thm modules.perm_bn_simps
thm modules.bn_finite

thm modules.distinct
thm modules.induct
thm modules.exhaust
thm modules.fv_defs
thm modules.bn_defs
thm modules.perm_simps
thm modules.eq_iff
thm modules.fv_bn_eqvt
thm modules.size_eqvt
thm modules.supp


end



