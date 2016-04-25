theory SingleLet
imports "../Nominal2" 
begin

atom_decl name

nominal_datatype single_let: trm =
  Var "name"
| App "trm" "trm"
| Lam x::"name" t::"trm"  binds x in t
| Let a::"assg" t::"trm"  binds "bn a" in t
| Foo x::"name" y::"name" t::"trm" t1::"trm" t2::"trm" binds (set) x in y t t1 t2
| Bar x::"name" y::"name" t::"trm" binds y x in t x y
| Baz x::"name" t1::"trm" t2::"trm" binds (set) x in t1, binds (set+) x in t2 
and assg =
  As "name" x::"name" t::"trm" binds x in t
binder
  bn::"assg \<Rightarrow> atom list"
where
  "bn (As x y t) = [atom x]"

thm single_let.distinct
thm single_let.induct
thm single_let.inducts
thm single_let.exhaust
thm single_let.strong_exhaust
thm single_let.fv_defs
thm single_let.bn_defs
thm single_let.perm_simps
thm single_let.eq_iff
thm single_let.fv_bn_eqvt
thm single_let.size_eqvt
thm single_let.supports
thm single_let.fsupp
thm single_let.supp
thm single_let.fresh


end



