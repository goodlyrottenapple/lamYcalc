theory Foo2
imports "../Nominal2" 
begin

(* 
  Contrived example that has more than one
  binding clause
*)

atom_decl name


nominal_datatype foo: trm =
  Var "name"
| App "trm" "trm"
| Lam x::"name" t::"trm"  binds x in t
| Let1 a1::"assg" t1::"trm" a2::"assg" t2::"trm" binds "bn a1" in t1, binds "bn a2" in t2
| Let2 x::"name" y::"name" t1::"trm" t2::"trm" binds x y in t1, binds y in t2
and assg =
  As_Nil
| As "name" x::"name" t::"trm" "assg" 
binder
  bn::"assg \<Rightarrow> atom list"
where
  "bn (As x y t a) = [atom x] @ bn a"
| "bn (As_Nil) = []"


thm foo.bn_defs
thm foo.permute_bn
thm foo.perm_bn_alpha
thm foo.perm_bn_simps
thm foo.bn_finite

thm foo.distinct
thm foo.induct
thm foo.inducts
thm foo.strong_induct
thm foo.exhaust
thm foo.strong_exhaust
thm foo.fv_defs
thm foo.bn_defs
thm foo.perm_simps
thm foo.eq_iff
thm foo.fv_bn_eqvt
thm foo.size_eqvt
thm foo.supports
thm foo.fsupp
thm foo.supp
thm foo.fresh
thm foo.size


end



