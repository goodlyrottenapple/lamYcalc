theory LetPat
imports "../Nominal2"
begin

atom_decl name

nominal_datatype trm =
  Var "name"
| App "trm" "trm"
| Lam x::"name" t::"trm"       binds x in t
| Let p::"pat" "trm" t::"trm"  binds "bn p" in t
and pat =
  PNil
| PVar "name"
| PTup "pat" "pat"
binder
  bn::"pat \<Rightarrow> atom list"
where
  "bn PNil = []"
| "bn (PVar x) = [atom x]"
| "bn (PTup p1 p2) = bn p1 @ bn p2"

thm trm_pat.eq_iff
thm trm_pat.distinct
thm trm_pat.induct
thm trm_pat.strong_induct[no_vars]
thm trm_pat.exhaust
thm trm_pat.strong_exhaust[no_vars]
thm trm_pat.fv_defs
thm trm_pat.bn_defs
thm trm_pat.perm_simps
thm trm_pat.eq_iff
thm trm_pat.fv_bn_eqvt
thm trm_pat.size

(* Nominal_Abs test *)

lemma alpha_res_alpha_set:
  "(bs, x) \<approx>res op = supp p (cs, y) \<longleftrightarrow> 
  (bs \<inter> supp x, x) \<approx>set op = supp p (cs \<inter> supp y, y)"
  using alpha_abs_set_abs_res alpha_abs_res_abs_set by blast


lemma
  fixes x::"'a::fs"
  assumes "(supp x - as) \<sharp>* p"
      and "p \<bullet> x = y"
      and "p \<bullet> (as \<inter> supp x) = bs \<inter> supp y"
  shows "(as, x) \<approx>res (op =) supp p (bs, y)"
  using assms
  unfolding alpha_res_alpha_set
  unfolding alphas
  apply simp
  apply rule
  apply (rule trans)
  apply (rule supp_perm_eq[symmetric, of _ p])
  apply(subst supp_finite_atom_set)
  apply (metis finite_Diff finite_supp)
  apply (simp add: fresh_star_def)
  apply blast
  apply(perm_simp)
  apply(simp)
  done

lemma
  fixes x::"'a::fs"
  assumes "(supp x - as) \<sharp>* p"
      and "p \<bullet> x = y"
      and "p \<bullet> as = bs"
  shows "(as, x) \<approx>set (op =) supp p (bs, y)"
  using assms
  unfolding alphas
  apply simp
  apply (rule trans)
  apply (rule supp_perm_eq[symmetric, of _ p])
  apply(subst supp_finite_atom_set)
  apply (metis finite_Diff finite_supp)
  apply(simp)
  apply(perm_simp)
  apply(simp)
  done

lemma
  fixes x::"'a::fs"
  assumes "(supp x - set as) \<sharp>* p"
      and "p \<bullet> x = y"
      and "p \<bullet> as = bs"
  shows "(as, x) \<approx>lst (op =) supp p (bs, y)"
  using assms
  unfolding alphas
  apply simp
  apply (rule trans)
  apply (rule supp_perm_eq[symmetric, of _ p])
  apply(subst supp_finite_atom_set)
  apply (metis finite_Diff finite_supp)
  apply(simp)
  apply(perm_simp)
  apply(simp)
  done


end



