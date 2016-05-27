theory Local_Contexts 
imports "../Nominal2" 
begin

text {*
This theory, contributed by Tjark Weber, contains examples 
and test cases that illustrate the useof Nominal2 in local 
contexts (locales, type classes, etc.).

As a running example, we use a variant of the untyped lambda-calculus
whose lambda-binder binds lists of names, rather than single names.
*}

atom_decl name

nominal_datatype lam = Var name
                     | App lam lam ("_ \<cdot> _" [110,110] 110)
                     | Lam xs::"name list" t::lam binds xs in t ("Lam _. _" [100,100] 100)

locale name_subst =
  fixes name_subst :: "name \<Rightarrow> name list \<Rightarrow> lam \<Rightarrow> lam"
  assumes name_subst_eqvt [eqvt]:
    "p \<bullet> name_subst x xs t = name_subst (p \<bullet> x) (p \<bullet> xs) (p \<bullet> t)"
  and name_subst_fresh: "supp xs \<sharp>* t \<Longrightarrow> supp xs \<sharp>* name_subst x xs t"

lemma set_map_atom_eq_supp: "set (map atom xs) = supp xs"
by (metis List.finite_set image_set supp_finite_set_at_base supp_set)

lemma atom_image_set_eq_supp: "atom ` set xs = supp xs"
by (metis image_set set_map_atom_eq_supp)

nominal_function (in name_subst)
  subst :: "lam \<Rightarrow> name list \<Rightarrow> lam \<Rightarrow> lam" ("_[_::=_]" [120,120,120] 120)
where
  "(Var x)[xs::=t] = name_subst x xs t"
| "(s \<cdot> t)[xs::=u] = s[xs::=u] \<cdot> t[xs::=u]"
| "\<lbrakk>supp xs \<sharp>* ys; supp xs \<sharp>* u\<rbrakk> \<Longrightarrow> (Lam xs. t)[ys::=u] = Lam xs. t[ys::=u]"
        apply auto
-- {* 3 subgoals *}
  -- {* eqvt *}
  apply (unfold eqvt_def subst_graph_def subst_graph_aux_def)
  apply (rule, perm_simp, rule)
 -- {* exhaustion *}
 apply (rule_tac y=a and c="(aa, b)" in lam.strong_exhaust)
   apply auto
 apply (metis atom_image_set_eq_supp fresh_star_Pair)
-- {* well-defined (compatibility) *}
apply (rename_tac xs' ys u t')
apply (erule Abs_lst_fcb2)
    apply (metis Abs_fresh_star(3) subset_refl)
   apply (metis fresh_star_Pair set_map_atom_eq_supp)
  apply (metis fresh_star_Pair set_map_atom_eq_supp)
 apply (auto simp add: eqvt_at_def)
 apply (metis Pair_eqvt perm_supp_eq)
apply (metis Pair_eqvt perm_supp_eq)
done

nominal_termination (in name_subst) (eqvt) by lexicographic_order

inductive (in name_subst) beta :: "lam \<Rightarrow> lam \<Rightarrow> bool" (infix "\<longrightarrow>\<^sub>\<beta>" 90)
where
  redex: "supp xs \<sharp>* u \<Longrightarrow> (Lam xs. t) \<cdot> u \<longrightarrow>\<^sub>\<beta> t[xs::=u]"
| "s \<longrightarrow>\<^sub>\<beta> s' \<Longrightarrow> s \<cdot> t \<longrightarrow>\<^sub>\<beta> s' \<cdot> t"
| "t \<longrightarrow>\<^sub>\<beta> t' \<Longrightarrow> s \<cdot> t \<longrightarrow>\<^sub>\<beta> s \<cdot> t'"

equivariance (in name_subst) beta


lemma lam_bound_fresh: "supp xs \<sharp>* (Lam xs. t)"
by (simp add: atom_image_set_eq_supp fresh_star_def)


lemma (in name_subst) subst_fresh: "supp xs \<sharp>* u \<Longrightarrow> supp xs \<sharp>* t[xs::=u]"
apply (nominal_induct t avoiding: xs u rule: lam.strong_induct)
  apply (simp_all add: atom_image_set_eq_supp)
  apply (metis name_subst_fresh)
 apply (metis fresh_star_def lam.fresh(2))
apply (simp add: fresh_star_def)
done

nominal_inductive (in name_subst) beta
avoids
  redex: xs
apply (auto simp add: fresh_star_Pair)
 apply (metis atom_image_set_eq_supp fresh_star_def lam.fresh(2) lam_bound_fresh)
apply (simp add: atom_image_set_eq_supp subst_fresh)
done

end
