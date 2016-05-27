theory Ex1
imports "../Nominal2"
begin

(* free names in bar are bound in foo *)

atom_decl name

thm finite_sets_supp

nominal_datatype foo =
  Foo0 "name"
| Foo1 b::"bar" f::"foo" binds (set) "bv b" in f
and bar =
  Bar0 "name"
| Bar1 "name" s::"name" b::"bar" binds (set) s in b
binder
  bv
where
  "bv (Bar0 x) = {}"
| "bv (Bar1 v x b) = {atom v}"

thm foo_bar.perm_bn_alpha
thm foo_bar.perm_bn_simps
thm foo_bar.bn_finite

thm foo_bar.eq_iff
thm foo_bar.distinct
thm foo_bar.induct
thm foo_bar.inducts
thm foo_bar.exhaust
thm foo_bar.fv_defs
thm foo_bar.bn_defs
thm foo_bar.perm_simps
thm foo_bar.eq_iff
thm foo_bar.fv_bn_eqvt
thm foo_bar.size_eqvt
thm foo_bar.supports
thm foo_bar.fsupp
thm foo_bar.supp

lemma
  "supp (Foo1 (Bar1 v x (Bar0 x)) (Foo0 v)) = {}"
apply(simp only: foo_bar.supp)
apply(simp only: foo_bar.bn_defs)
apply(simp only: supp_at_base)
apply(simp)
done

end


