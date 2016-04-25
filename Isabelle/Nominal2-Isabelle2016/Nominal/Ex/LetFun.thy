theory LetFun
imports "../Nominal2"
begin

atom_decl name

(* x is bound in both e1 and e2;
   bp-names in p are bound only in e1 
*)


nominal_datatype exp =
  Var name
| Pair exp exp
| LetRec x::name p::pat e1::exp e2::exp  binds x in e2, binds x "bp p" in e1
and pat =
  PVar name
| PUnit
| PPair pat pat
binder
  bp :: "pat \<Rightarrow> atom list"
where
  "bp (PVar x) = [atom x]"
| "bp (PUnit) = []"
| "bp (PPair p1 p2) = bp p1 @ bp p2"

thm exp_pat.distinct
thm exp_pat.induct
thm exp_pat.inducts
thm exp_pat.exhaust
thm exp_pat.fv_defs
thm exp_pat.bn_defs
thm exp_pat.perm_simps
thm exp_pat.eq_iff
thm exp_pat.fv_bn_eqvt
thm exp_pat.size_eqvt
thm exp_pat.size
thm exp_pat.supports
thm exp_pat.fsupp
thm exp_pat.supp


end
