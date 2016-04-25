theory TypeSchemes2
imports "../Nominal2"
begin

section {*** Type Schemes defined as a single nominal datatype ***}

atom_decl name 

nominal_datatype ty =
  Var "name"
| Fun "ty" "ty"
and tys =
  All xs::"name fset" ty::"ty" binds (set+) xs in ty

thm ty_tys.distinct
thm ty_tys.induct
thm ty_tys.inducts
thm ty_tys.exhaust 
thm ty_tys.strong_exhaust
thm ty_tys.fv_defs
thm ty_tys.bn_defs
thm ty_tys.perm_simps
thm ty_tys.eq_iff
thm ty_tys.fv_bn_eqvt
thm ty_tys.size_eqvt
thm ty_tys.supports
thm ty_tys.supp
thm ty_tys.fresh

fun
  lookup :: "(name \<times> ty) list \<Rightarrow> name \<Rightarrow> ty"
where
  "lookup [] Y = Var Y"
| "lookup ((X, T) # Ts) Y = (if X = Y then T else lookup Ts Y)"

lemma lookup_eqvt[eqvt]:
  shows "(p \<bullet> lookup Ts T) = lookup (p \<bullet> Ts) (p \<bullet> T)"
apply(induct Ts T rule: lookup.induct)
apply(simp_all)
done

lemma TEST1:
  assumes "x = Inl y"
  shows "(p \<bullet> Sum_Type.projl x) = Sum_Type.projl (p \<bullet> x)"
using assms by simp

lemma TEST2:
  assumes "x = Inr y"
  shows "(p \<bullet> Sum_Type.projr x) = Sum_Type.projr (p \<bullet> x)"
using assms by simp

lemma test:
  assumes a: "\<exists>y. f x = Inl y"
  shows "(p \<bullet> (Sum_Type.projl (f x))) = Sum_Type.projl ((p \<bullet> f) (p \<bullet> x))"
using a TEST1
by (metis eqvt_bound eqvt_lambda permute_eq_iff)

lemma test2:
  assumes a: "\<exists>y. f x = Inl y"
  shows "(p \<bullet> (Sum_Type.projl (f x))) = Sum_Type.projl (p \<bullet> (f x))"
using a
by clarsimp

nominal_function (default "case_sum (\<lambda>x. Inl undefined) (\<lambda>x. Inr undefined)")
    subst  :: "(name \<times> ty) list \<Rightarrow> ty \<Rightarrow> ty"
and substs :: "(name \<times> ty) list \<Rightarrow> tys \<Rightarrow> tys"
where
  "subst \<theta> (Var X) = lookup \<theta> X"
| "subst \<theta> (Fun T1 T2) = Fun (subst \<theta> T1) (subst \<theta> T2)"
| "fset (map_fset atom xs) \<sharp>* \<theta> \<Longrightarrow> substs \<theta> (All xs T) = All xs (subst \<theta> T)"
thm subst_substs_graph_def subst_substs_graph_aux_def
apply(simp add: subst_substs_graph_aux_def eqvt_def)
apply(rule TrueI)
apply (case_tac x)
apply simp apply clarify 
apply (rule_tac y="b" in ty_tys.exhaust(1))
apply (auto)[1]
apply (auto)[1]
apply simp apply clarify 
apply (rule_tac ya="b" and c="a" in ty_tys.strong_exhaust(2))
apply (auto)[1]
apply (auto)[5]
--"LAST GOAL"
apply (simp add: meta_eq_to_obj_eq[OF subst_def, symmetric, unfolded fun_eq_iff])
apply (subgoal_tac "eqvt_at (\<lambda>(l, r). subst l r) (\<theta>', T)")
apply (thin_tac "eqvt_at subst_substs_sumC (Inl (\<theta>', T))")
apply (thin_tac "eqvt_at subst_substs_sumC (Inl (\<theta>', Ta))")
prefer 2
apply (simp add: eqvt_at_def subst_def)
apply rule
apply (subst test2)
apply (simp add: subst_substs_sumC_def)
apply (simp add: THE_default_def)
apply (case_tac "Ex1 (subst_substs_graph (Inl (\<theta>', T)))")
prefer 2
apply simp
apply (simp add: the1_equality)
apply auto[1]
apply (erule_tac x="x" in allE)
apply simp
apply(cases rule: subst_substs_graph.cases)
apply assumption
apply (rule_tac x="lookup \<theta> X" in exI)
apply clarify
apply (rule the1_equality)
apply blast apply assumption
apply (rule_tac x="(Fun (Sum_Type.projl (subst_substs_sum (Inl (\<theta>, T1))))
                  (Sum_Type.projl (subst_substs_sum (Inl (\<theta>, T2)))))" in exI)
apply clarify
apply (rule the1_equality)
apply blast apply assumption
apply clarify
apply simp
--"-"
apply clarify
  apply (frule supp_eqvt_at)
  apply (simp add: finite_supp)
  apply (erule Abs_res_fcb)
  apply (simp add: Abs_fresh_iff)
  apply (simp add: Abs_fresh_iff)
  apply auto[1]
  apply (simp add: fresh_def fresh_star_def)
  apply (erule contra_subsetD)
  apply (simp add: supp_Pair)
  apply blast
  apply clarify
  apply (simp)
  apply (simp add: eqvt_at_def)
  apply (subst Abs_eq_iff)
  apply (rule_tac x="0::perm" in exI)
  apply (subgoal_tac "p \<bullet> \<theta>' = \<theta>'")
  apply (simp add: alphas fresh_star_zero)
  apply (subgoal_tac "\<And>x. x \<in> supp (subst \<theta>' (p \<bullet> T)) \<Longrightarrow> x \<in> p \<bullet> atom ` fset xs \<longleftrightarrow> x \<in> atom ` fset xsa")
  apply(simp)
  apply blast
  apply (subgoal_tac "x \<in> supp(p \<bullet> \<theta>', p \<bullet> T)")
  apply (simp add: supp_Pair eqvts eqvts_raw)
  apply auto[1]
  apply (subgoal_tac "(atom ` fset (p \<bullet> xs)) \<sharp>* \<theta>'")
  apply (simp add: fresh_star_def fresh_def)
  apply(drule_tac p1="p" in iffD2[OF fresh_star_permute_iff])
  apply (simp add: eqvts eqvts_raw)
  apply (simp add: fresh_star_def fresh_def)
  apply (simp (no_asm) only: supp_eqvt[symmetric] Pair_eqvt[symmetric])
  apply (subgoal_tac "p \<bullet> supp (subst \<theta>' T) \<subseteq> p \<bullet> supp (\<theta>', T)")
  apply (erule_tac subsetD)
  apply(simp only: supp_eqvt)
  apply(perm_simp)
  apply(drule_tac x="p" in spec)
  apply(simp)
  apply (metis permute_pure subset_eqvt)
  apply (rule perm_supp_eq)
  apply (simp add: fresh_def fresh_star_def)
  apply blast
  done


nominal_termination (eqvt) by lexicographic_order

text {* Some Tests about Alpha-Equality *}

lemma
  shows "All {|a, b|} (Fun (Var a) (Var b)) = All {|b, a|} (Fun (Var a) (Var b))"
  apply(simp add: Abs_eq_iff)
  apply(rule_tac x="0::perm" in exI)
  apply(simp add: alphas fresh_star_def ty_tys.supp supp_at_base)
  done

lemma
  shows "All {|a, b|} (Fun (Var a) (Var b)) = All {|a, b|} (Fun (Var b) (Var a))"
  apply(simp add: Abs_eq_iff)
  apply(rule_tac x="(atom a \<rightleftharpoons> atom b)" in exI)
  apply(simp add: alphas fresh_star_def supp_at_base ty_tys.supp)
  done

lemma
  shows "All {|a, b, c|} (Fun (Var a) (Var b)) = All {|a, b|} (Fun (Var a) (Var b))"
  apply(simp add: Abs_eq_iff)
  apply(rule_tac x="0::perm" in exI)
  apply(simp add: alphas fresh_star_def ty_tys.supp supp_at_base)
done

lemma
  assumes a: "a \<noteq> b"
  shows "\<not>(All {|a, b|} (Fun (Var a) (Var b)) = All {|c|} (Fun (Var c) (Var c)))"
  using a
  apply(simp add: Abs_eq_iff)
  apply(clarify)
  apply(simp add: alphas fresh_star_def ty_tys.supp supp_at_base)
  apply auto
  done

end
