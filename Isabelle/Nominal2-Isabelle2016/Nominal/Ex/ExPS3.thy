theory ExPS3
imports "../Nominal2"
begin

(* example 3 from Peter Sewell's bestiary *)

atom_decl name

nominal_datatype exp =
  Var "name"
| App "exp" "exp"
| Lam x::"name" e::"exp" binds x in e
| Let x::"name" p::"pat" e1::"exp" e2::"exp" binds (set) x in e2, binds (set) "bp p" in e1
and pat =
  PVar "name"
| PUnit
| PPair "pat" "pat"
binder
  bp :: "pat \<Rightarrow> atom set"
where
  "bp (PVar x) = {atom x}"
| "bp (PUnit) = {}"
| "bp (PPair p1 p2) = bp p1 \<union> bp p2"


thm exp_pat.distinct
thm exp_pat.induct
thm exp_pat.exhaust
thm exp_pat.fv_defs
thm exp_pat.bn_defs
thm exp_pat.perm_simps
thm exp_pat.eq_iff
thm exp_pat.fv_bn_eqvt
thm exp_pat.size_eqvt


end



