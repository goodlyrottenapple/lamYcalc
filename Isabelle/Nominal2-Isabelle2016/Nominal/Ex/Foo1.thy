theory Foo1
imports "../Nominal2" 
begin

text {* 
  Contrived example that has more than one
  binding function
*}


atom_decl name

nominal_datatype foo: trm =
  Var "name"
| App "trm" "trm"
| Lam x::"name" t::"trm"    binds x in t
| Let1 a::"assg" t::"trm"   binds "bn1 a" in t
| Let2 a::"assg" t::"trm"   binds "bn2 a" in t
| Let3 a::"assg" t::"trm"   binds "bn3 a" in t
| Let4 a::"assg'" t::"trm"  binds (set) "bn4 a" in t
and assg =
  As "name" "name" "trm"
and assg' =
  BNil
| BAs "name" "assg'"
binder
  bn1::"assg \<Rightarrow> atom list" and
  bn2::"assg \<Rightarrow> atom list" and
  bn3::"assg \<Rightarrow> atom list" and
  bn4::"assg' \<Rightarrow> atom set"
where
  "bn1 (As x y t) = [atom x]"
| "bn2 (As x y t) = [atom y]"
| "bn3 (As x y t) = [atom x, atom y]"
| "bn4 (BNil) = {}"
| "bn4 (BAs a as) = {atom a} \<union> bn4 as"

thm foo.permute_bn
thm foo.perm_bn_alpha
thm foo.perm_bn_simps
thm foo.bn_finite

thm foo.distinct
thm foo.induct
thm foo.inducts
thm foo.exhaust
thm foo.strong_induct
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
thm foo.bn_finite


end



