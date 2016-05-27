theory TypeSchemes1
imports "../Nominal2"
begin

section {* Type Schemes defined as two separate nominal datatypes *}

atom_decl name 

nominal_datatype ty =
  Var "name"
| Fun "ty" "ty" ("_ \<rightarrow> _")

nominal_datatype tys =
  All xs::"name fset" ty::"ty" binds (set+) xs in ty ("All [_]._")

thm tys.distinct
thm tys.induct tys.strong_induct
thm tys.exhaust tys.strong_exhaust
thm tys.fv_defs
thm tys.bn_defs
thm tys.perm_simps
thm tys.eq_iff
thm tys.fv_bn_eqvt
thm tys.size_eqvt
thm tys.supports
thm tys.supp
thm tys.fresh

subsection {* Some Tests about Alpha-Equality *}

lemma
  shows "All [{|a, b|}].((Var a) \<rightarrow> (Var b)) = All [{|b, a|}]. ((Var a) \<rightarrow> (Var b))"
  apply(simp add: Abs_eq_iff)
  apply(rule_tac x="0::perm" in exI)
  apply(simp add: alphas fresh_star_def ty.supp supp_at_base)
  done

lemma
  shows "All [{|a, b|}].((Var a) \<rightarrow> (Var b)) = All [{|a, b|}].((Var b) \<rightarrow> (Var a))"
  apply(simp add: Abs_eq_iff)
  apply(rule_tac x="(atom a \<rightleftharpoons> atom b)" in exI)
  apply(simp add: alphas fresh_star_def supp_at_base ty.supp)
  done

lemma
  shows "All [{|a, b, c|}].((Var a) \<rightarrow> (Var b)) = All [{|a, b|}].((Var a) \<rightarrow> (Var b))"
  apply(simp add: Abs_eq_iff)
  apply(rule_tac x="0::perm" in exI)
  apply(simp add: alphas fresh_star_def ty.supp supp_at_base)
done

lemma
  assumes a: "a \<noteq> b"
  shows "\<not>(All [{|a, b|}].((Var a) \<rightarrow> (Var b)) = All [{|c|}].((Var c) \<rightarrow> (Var c)))"
  using a
  apply(simp add: Abs_eq_iff)
  apply(clarify)
  apply(simp add: alphas fresh_star_def ty.supp supp_at_base)
  apply auto
  done


subsection {* Substitution function for types and type schemes *}

type_synonym 
  Subst = "(name \<times> ty) list"

fun
  lookup :: "Subst \<Rightarrow> name \<Rightarrow> ty"
where
  "lookup [] Y = Var Y"
| "lookup ((X, T) # Ts) Y = (if X = Y then T else lookup Ts Y)"

lemma lookup_eqvt[eqvt]:
  shows "(p \<bullet> lookup Ts T) = lookup (p \<bullet> Ts) (p \<bullet> T)"
  by (induct Ts T rule: lookup.induct) (simp_all)

nominal_function
  subst  :: "Subst \<Rightarrow> ty \<Rightarrow> ty" ("_<_>" [100,60] 120)
where
  "\<theta><Var X> = lookup \<theta> X"
| "\<theta><T1 \<rightarrow> T2> = (\<theta><T1>) \<rightarrow> (\<theta><T2>)"
  apply(simp add: eqvt_def subst_graph_aux_def)
  apply(rule TrueI)
  apply(case_tac x)
  apply(rule_tac y="b" in ty.exhaust)
  apply(blast)
  apply(blast)
  apply(simp_all)
  done

nominal_termination (eqvt)
  by lexicographic_order

lemma subst_id1:
  fixes T::"ty"
  shows "[]<T> = T"
by (induct T rule: ty.induct) (simp_all)

lemma subst_id2:
  fixes T::"ty"
  shows "[(X, Var X)]<T> = T"
by (induct T rule: ty.induct) (simp_all)

lemma supp_fun_app_eqvt:
  assumes e: "eqvt f"
  shows "supp (f a b) \<subseteq> supp a \<union> supp b"
  using supp_fun_app_eqvt[OF e] supp_fun_app
  by blast
 
lemma supp_subst:
  "supp (subst \<theta> t) \<subseteq> supp \<theta> \<union> supp t"
  apply (rule supp_fun_app_eqvt)
  unfolding eqvt_def 
  by (simp add: permute_fun_def subst.eqvt)
 
nominal_function
  substs :: "(name \<times> ty) list \<Rightarrow> tys \<Rightarrow> tys" ("_<_>" [100,60] 120)
where
  "fset (map_fset atom Xs) \<sharp>* \<theta> \<Longrightarrow> \<theta><All [Xs].T> = All [Xs].(\<theta><T>)"
  apply(simp add: eqvt_def substs_graph_aux_def)
  apply auto[2]
  apply (rule_tac y="b" and c="a" in tys.strong_exhaust)
  apply auto[1]
  apply(simp)
  apply(erule conjE)
  apply (erule Abs_res_fcb)
  apply (simp add: Abs_fresh_iff)
  apply(simp add: fresh_def)
  apply(simp add: supp_Abs)
  apply(rule impI)
  apply(subgoal_tac "x \<notin> supp \<theta>")
  prefer 2
  apply(auto simp add: fresh_star_def fresh_def)[1]
  apply(subgoal_tac "x \<in> supp T")
  using supp_subst
  apply(blast)
  using supp_subst
  apply(blast)
  apply clarify
  apply (simp add: subst.eqvt)
  apply (subst Abs_eq_iff)
  apply (rule_tac x="0::perm" in exI)
  apply (subgoal_tac "p \<bullet> \<theta>' = \<theta>'")
  apply (simp add: alphas fresh_star_zero)
  apply (subgoal_tac "\<And>x. x \<in> supp (subst \<theta>' (p \<bullet> T)) \<Longrightarrow> x \<in> p \<bullet> atom ` fset Xs \<longleftrightarrow> x \<in> atom ` fset Xsa")
  apply(simp)
  apply blast
  apply (subgoal_tac "x \<in> supp(p \<bullet> \<theta>', p \<bullet> T)")
  apply (simp add: supp_Pair eqvts eqvts_raw)
  apply auto[1]
  apply (subgoal_tac "(atom ` fset (p \<bullet> Xs)) \<sharp>* \<theta>'")
  apply (simp add: fresh_star_def fresh_def)
  apply(drule_tac p1="p" in iffD2[OF fresh_star_permute_iff])
  apply (simp add: eqvts eqvts_raw)
  apply (simp add: fresh_star_def fresh_def)
  apply (drule subsetD[OF supp_subst])
  apply (simp add: supp_Pair)
  apply (rule perm_supp_eq)
  apply (simp add: fresh_def fresh_star_def)
  apply blast
  done

nominal_termination (eqvt)
  by (lexicographic_order)


subsection {* Generalisation of types and type-schemes*}

fun
  subst_Dom_pi :: "Subst \<Rightarrow> perm \<Rightarrow> Subst" ("_|_")
where
  "[]|p = []"
| "((X,T)#\<theta>)|p = (p \<bullet> X, T)#(\<theta>|p)" 

fun
  subst_subst :: "Subst \<Rightarrow> Subst \<Rightarrow> Subst" ("_<_>"  [100,60] 120)
where
  "\<theta><[]> = []"
| "\<theta> <((X,T)#\<theta>')> = (X,\<theta><T>)#(\<theta><\<theta>'>)"

fun
  Dom :: "Subst \<Rightarrow> name set"
where
  "Dom [] = {}"
| "Dom ((X,T)#\<theta>) = {X} \<union> Dom \<theta>"

lemma Dom_eqvt[eqvt]:
  shows "p \<bullet> (Dom \<theta>) = Dom (p \<bullet> \<theta>)"
apply (induct \<theta> rule: Dom.induct) 
apply (simp_all add: permute_set_def)
apply (auto)
done

lemma Dom_subst:
  fixes \<theta>1 \<theta>2::"Subst"
  shows "Dom (\<theta>2<\<theta>1>) = (Dom \<theta>1)"
by (induct \<theta>1) (auto)

lemma Dom_pi:
  shows "Dom (\<theta>|p) = Dom (p \<bullet> \<theta>)"
by (induct \<theta>) (auto)

lemma Dom_fresh_lookup:
  fixes \<theta>::"Subst"
  assumes "\<forall>Y \<in> Dom \<theta>. atom Y \<sharp> X"
  shows "lookup \<theta> X = Var X"
using assms
by (induct \<theta>) (auto simp add: fresh_at_base)

lemma Dom_fresh_ty:
  fixes \<theta>::"Subst"
  and   T::"ty"
  assumes "\<forall>X \<in> Dom \<theta>. atom X \<sharp> T"
  shows "\<theta><T> = T"
using assms
by (induct T rule: ty.induct) (auto simp add: ty.fresh Dom_fresh_lookup)

lemma Dom_fresh_subst:
  fixes \<theta> \<theta>'::"Subst"
  assumes "\<forall>X \<in> Dom \<theta>. atom X \<sharp> \<theta>'"
  shows "\<theta><\<theta>'> = \<theta>'"
using assms
by (induct \<theta>') (auto simp add: fresh_Pair fresh_Cons Dom_fresh_ty)

lemma s1:
  assumes "name \<in> Dom \<theta>"
  shows "lookup \<theta> name = lookup \<theta>|p (p \<bullet> name)"
using assms
apply(induct \<theta>)
apply(auto)
done

lemma lookup_fresh:
  fixes X::"name"
  assumes a: "atom X \<sharp> \<theta>"
  shows "lookup \<theta> X = Var X"
  using a
  by (induct \<theta>) (auto simp add: fresh_Cons fresh_Pair fresh_at_base)

lemma lookup_Dom:
  fixes X::"name"
  assumes "X \<notin> Dom \<theta>"
  shows "lookup \<theta> X = Var X"
  using assms
  by (induct \<theta>) (auto)

lemma t:
  fixes T::"ty"
  assumes a: "(supp T - atom ` Dom \<theta>) \<sharp>* p"
  shows "\<theta><T> = \<theta>|p<p \<bullet> T>"
using a
apply(induct T rule: ty.induct)
defer
apply(simp add: ty.supp fresh_star_def)
apply(simp)
apply(case_tac "name \<in> Dom \<theta>")
apply(rule s1)
apply(assumption)
apply(subst lookup_Dom)
apply(assumption)
apply(subst lookup_Dom)
apply(simp add: Dom_pi)
apply(rule_tac p="- p" in permute_boolE)
apply(perm_simp add: permute_minus_cancel)
apply(simp)
apply(simp)
apply(simp add: ty.supp supp_at_base)
apply(simp add: fresh_star_def)
apply(drule_tac x="atom name" in bspec)
apply(auto)[1]
apply(simp add: fresh_def supp_perm)
done

nominal_function
  generalises :: "ty \<Rightarrow> tys \<Rightarrow> bool" ("_ \<prec>\<prec> _")
where
  "atom ` (fset Xs) \<sharp>* T \<Longrightarrow>  
     T \<prec>\<prec> All [Xs].T' \<longleftrightarrow> (\<exists>\<theta>. T = \<theta><T'> \<and> atom ` Dom \<theta> = atom ` fset Xs \<inter> supp T')"
apply(simp add: generalises_graph_aux_def eqvt_def)
apply(rule TrueI)
apply(case_tac x)
apply(simp)
apply(rule_tac y="b" and c="a" in tys.strong_exhaust)
apply(simp)
apply(clarify)
apply(simp only: tys.eq_iff map_fset_image)
apply(erule_tac c="Ta" in Abs_res_fcb2)
apply(simp)
apply(simp)
apply(simp add: fresh_star_def pure_fresh)
apply(simp add: fresh_star_def pure_fresh)
apply(simp add: fresh_star_def pure_fresh)
apply(perm_simp)
apply(subst perm_supp_eq)
apply(simp)
apply(simp)
apply(perm_simp)
apply(subst perm_supp_eq)
apply(simp)
apply(simp)
done

nominal_termination (eqvt)
  by lexicographic_order
  
lemma better:
  "T \<prec>\<prec> All [Xs].T' \<longleftrightarrow> (\<exists>\<theta>. T = \<theta><T'> \<and> atom ` Dom \<theta> = atom ` fset Xs \<inter> supp T')"
using at_set_avoiding3
apply -
apply(drule_tac x="atom ` fset Xs" in meta_spec)
apply(drule_tac x="T" in meta_spec)
apply(drule_tac x="All [Xs].T'" in meta_spec)
apply(drule meta_mp)
apply(simp)
apply(drule meta_mp)
apply(simp add: finite_supp)
apply(drule meta_mp)
apply(simp add: finite_supp)
apply(drule_tac meta_mp)
apply(simp add: fresh_star_def tys.fresh)
apply(clarify)
apply(rule_tac t="All [Xs].T'" and s="p \<bullet> All [Xs].T'" in subst)
apply(rule supp_perm_eq)
apply(assumption)
apply(perm_simp)
apply(subst generalises.simps)
apply(assumption)
apply(rule iffI)
defer
apply(clarify)
apply(rule_tac x="\<theta>|p" in exI)
apply(rule conjI)
apply(rule t)
apply(simp add: tys.supp)
apply (metis Diff_Int_distrib Int_Diff Int_commute inf_sup_absorb)
apply(simp add: Dom_pi)
apply(rotate_tac 3)
apply(drule_tac p="p" in permute_boolI)
apply(perm_simp)
apply(assumption)
apply(clarify)
apply(rule_tac x="\<theta>|- p" in exI)
apply(rule conjI)
apply(subst t[where p="- p"])
apply(simp add: tys.supp)
apply(rotate_tac 1)
apply(drule_tac p="p" in permute_boolI)
apply(perm_simp)
apply(simp add: permute_self)
apply(simp add: fresh_star_def)
apply(simp add: fresh_minus_perm)
apply (metis Diff_Int_distrib Int_Diff Int_commute inf_sup_absorb)
apply(simp)
apply(simp add: Dom_pi)
apply(rule_tac p="p" in permute_boolE)
apply(perm_simp add: permute_minus_cancel)
apply(assumption)
done


(* Tests *)

fun 
  compose::"Subst \<Rightarrow> Subst \<Rightarrow> Subst" ("_ \<circ> _" [100,100] 100)
where
  "\<theta>1 \<circ> [] = \<theta>1"
| "\<theta>1 \<circ> ((X,T)#\<theta>2) = (X,\<theta>1<T>)#(\<theta>1 \<circ> \<theta>2)"

lemma compose_ty:
  fixes  \<theta>1 \<theta>2 :: "Subst"
  and    T :: "ty"
  shows "\<theta>1<\<theta>2<T>> = (\<theta>1\<circ>\<theta>2)<T>"
proof (induct T rule: ty.induct)
  case (Var X) 
  have "\<theta>1<lookup \<theta>2 X> = lookup (\<theta>1\<circ>\<theta>2) X" 
    by (induct \<theta>2) (auto)
  then show ?case by simp
next
  case (Fun T1 T2)
  then show ?case by simp
qed

lemma compose_Dom:
  shows "Dom (\<theta>1 \<circ> \<theta>2) = Dom \<theta>1 \<union> Dom \<theta>2"
apply(induct \<theta>2)
apply(auto)
done

lemma t1:
  fixes T::"ty"
  and Xs::"name fset"
  shows "\<exists>\<theta>. atom ` Dom \<theta> = atom ` fset Xs \<and> \<theta><T> = T"
apply(induct Xs)
apply(rule_tac x="[]" in exI)
apply(simp add: subst_id1)
apply(clarify)
apply(rule_tac x="[(x, Var x)] \<circ> \<theta>" in exI)
apply(simp add: compose_ty[symmetric] subst_id2 compose_Dom)
done

nominal_function
  ftv  :: "ty \<Rightarrow> name fset"
where
  "ftv (Var X) = {|X|}"
| "ftv (T1 \<rightarrow> T2) = (ftv T1) |\<union>| (ftv T2)"
  apply(simp add: eqvt_def ftv_graph_aux_def)
  apply(rule TrueI)
  apply(rule_tac y="x" in ty.exhaust)
  apply(blast)
  apply(blast)
  apply(simp_all)
  done

nominal_termination (eqvt)
  by lexicographic_order

lemma tt:
  shows "supp T = atom ` fset (ftv T)"
apply(induct T rule: ty.induct)
apply(simp_all add: ty.supp supp_at_base)
apply(auto)
done


lemma t2:
  shows "T \<prec>\<prec> All [Xs].T"
unfolding better
using t1
apply -
apply(drule_tac x="Xs |\<inter>| ftv T" in meta_spec)
apply(drule_tac x="T" in meta_spec)
apply(clarify)
apply(rule_tac x="\<theta>" in exI)
apply(simp add: tt)
apply(auto)
done

(* HERE *)

lemma w1: 
  shows "\<theta><\<theta>'|p> = (\<theta><\<theta>'>)|p"
  by (induct \<theta>')(auto)

(*
lemma w2:
  assumes "name |\<in>| Dom \<theta>'" 
  shows "\<theta><lookup \<theta>' name> = lookup (\<theta><\<theta>'>) name"
using assms
apply(induct \<theta>')
apply(auto simp add: notin_empty_fset)
done

lemma w3:
  assumes "name |\<in>| Dom \<theta>" 
  shows "lookup \<theta> name = lookup (\<theta>|p) (p \<bullet> name)"
using assms
apply(induct \<theta>)
apply(auto simp add: notin_empty_fset)
done

lemma fresh_lookup:
  fixes X Y::"name"
  and   \<theta>::"Subst"
  assumes asms: "atom X \<sharp> Y" "atom X \<sharp> \<theta>"
  shows "atom X \<sharp> (lookup \<theta> Y)"
  using assms
  apply (induct \<theta>)
  apply (auto simp add: fresh_Cons fresh_Pair fresh_at_base ty.fresh)
  done

lemma test:
  fixes \<theta> \<theta>'::"Subst"
  and T::"ty"
  assumes "(p \<bullet> atom ` fset (Dom \<theta>')) \<sharp>* \<theta>" "supp All [Dom \<theta>'].T \<sharp>* p"
  shows "\<theta><\<theta>'<T>> = \<theta><\<theta>'|p><\<theta><p \<bullet> T>>"
using assms
apply(induct T rule: ty.induct)
defer
apply(auto simp add: tys.supp ty.supp fresh_star_def)[1]
apply(auto simp add: tys.supp ty.supp fresh_star_def supp_at_base)[1]
apply(case_tac "name |\<in>| Dom \<theta>'")
apply(subgoal_tac "atom (p \<bullet> name) \<sharp> \<theta>")
apply(subst (2) lookup_fresh)
apply(perm_simp)
apply(auto simp add: fresh_star_def)[1]
apply(simp)
apply(simp add: w1)
apply(simp add: w2)
apply(subst w3[symmetric])
apply(simp add: Dom_subst)
apply(simp)
apply(perm_simp)
apply(rotate_tac 2)
apply(drule_tac p="p" in permute_boolI)
apply(perm_simp)
apply(auto simp add: fresh_star_def)[1]
apply(metis notin_fset)
apply(simp add: lookup_Dom)
apply(perm_simp)
apply(subst Dom_fresh_ty)
apply(auto)[1]
apply(rule fresh_lookup)
apply(simp add: Dom_subst)
apply(simp add: Dom_pi)
apply(perm_simp)
apply(rotate_tac 2)
apply(drule_tac p="p" in permute_boolI)
apply(perm_simp)
apply(simp add: fresh_at_base)
apply (metis in_fset)
apply(simp add: Dom_subst)
apply(simp add: Dom_pi[symmetric])
apply(perm_simp)
apply(subst supp_perm_eq)
apply(simp add: supp_at_base fresh_star_def)
apply (smt Diff_iff atom_eq_iff image_iff insertI1 notin_fset)
apply(simp)
done

lemma generalises_subst:
  shows "T \<prec>\<prec> All [Xs].T' \<Longrightarrow> \<theta><T> \<prec>\<prec> \<theta><All [Xs].T'>"
using at_set_avoiding3
apply -
apply(drule_tac x="fset (map_fset atom Xs)" in meta_spec)
apply(drule_tac x="\<theta>" in meta_spec)
apply(drule_tac x="All [Xs].T'" in meta_spec)
apply(drule meta_mp)
apply(simp)
apply(drule meta_mp)
apply(simp add: finite_supp)
apply(drule meta_mp)
apply(simp add: finite_supp)
apply(drule meta_mp)
apply(simp add: tys.fresh fresh_star_def)
apply(erule exE)
apply(erule conjE)+
apply(rule_tac t="All[Xs].T'" and s="p \<bullet> (All [Xs].T')" in subst)
apply(rule supp_perm_eq)
apply(assumption)
apply(perm_simp)
apply(subst substs.simps)
apply(simp)
apply(simp add: better)
apply(erule exE)
apply(simp)
apply(rule_tac x="\<theta><\<theta>'|p>" in exI)
apply(rule conjI)
apply(rule test)
apply(simp)
apply(perm_simp)
apply(simp add: fresh_star_def)
apply(auto)[1]
apply(simp add: tys.supp)
apply(simp add: fresh_star_def)
apply(auto)[1]
oops

lemma generalises_subst:
  shows "T \<prec>\<prec> S \<Longrightarrow> \<theta><T> \<prec>\<prec> \<theta><S>"
unfolding generalises_def
apply(erule exE)+
apply(erule conjE)+
apply(rule_tac t="S" and s="All [Xs].T'" in subst)
apply(simp)
using at_set_avoiding3
apply -
apply(drule_tac x="fset (map_fset atom Xs)" in meta_spec)
apply(drule_tac x="\<theta>" in meta_spec)
apply(drule_tac x="All [Xs].T'" in meta_spec)
apply(drule meta_mp)
apply(simp)
apply(drule meta_mp)
apply(simp add: finite_supp)
apply(drule meta_mp)
apply(simp add: finite_supp)
apply(drule meta_mp)
apply(simp add: tys.fresh fresh_star_def)
apply(erule exE)
apply(erule conjE)+
apply(rule_tac t="All[Xs].T'" and s="p \<bullet> (All [Xs].T')" in subst)
apply(rule supp_perm_eq)
apply(assumption)
apply(perm_simp)
apply(subst substs.simps)
apply(perm_simp)
apply(simp)
apply(rule_tac x="\<theta><\<theta>'|p>" in exI)
apply(rule_tac x="p \<bullet> Xs" in exI)
apply(rule_tac x="\<theta><p \<bullet> T'>" in exI)
apply(rule conjI)
apply(simp)
apply(rule conjI)
defer
apply(simp add: Dom_subst)
apply(simp add: Dom_pi Dom_eqvt[symmetric])
apply(rule_tac t="T" and s="\<theta>'<T'>" in subst)
apply(simp)
apply(simp)
apply(rule test)
apply(perm_simp)
apply(rotate_tac 2)
apply(drule_tac p="p" in permute_boolI)
apply(perm_simp)
apply(auto simp add: fresh_star_def)
done


lemma r:
  "A - (B \<inter> A) = A - B"
by (metis Diff_Int Diff_cancel sup_bot_right)


lemma t3:
  "T \<prec>\<prec>  All [Xs].T' \<longleftrightarrow> (\<exists>\<theta>. T = \<theta><T'> \<and> Dom \<theta> = Xs)"
apply(auto)
defer
apply(simp add: generalises_def)
apply(auto)[1]
unfolding generalises_def
apply(auto)[1]
apply(simp add:  Abs_eq_res_set)
apply(simp add: Abs_eq_iff2)
apply(simp add: alphas)
apply(perm_simp)
apply(clarify)
apply(simp add: r)
apply(drule sym)
apply(simp)
apply(rule_tac x="\<theta>|p" in exI)
sorry

definition
  generalises_tys :: "tys \<Rightarrow> tys \<Rightarrow> bool" ("_ \<prec>\<prec> _")
where
  "S1 \<prec>\<prec> S2 = (\<forall>T::ty. T \<prec>\<prec> S1 \<longrightarrow> T \<prec>\<prec> S2)"

lemma
  "All [Xs1].T1 \<prec>\<prec> All [Xs2].T2 
     \<longleftrightarrow> (\<exists>\<theta>. Dom \<theta> = Xs2 \<and> T1 = \<theta><T2> \<and> (\<forall>X \<in> fset Xs1. atom X \<sharp> All [Xs2].T2))"
apply(rule iffI)
apply(simp add: generalises_tys_def)
apply(drule_tac x="T1" in spec)
apply(drule mp)
apply(rule t2)
apply(simp add: t3)
apply(clarify)
apply(rule_tac x="\<theta>" in exI)
apply(simp)
apply(rule ballI)
defer
apply(simp add: generalises_tys_def)
apply(clarify)
apply(simp add: t3)
apply(clarify)



lemma 
  "T \<prec>\<prec>  All [Xs].T' \<longleftrightarrow> (\<exists>\<theta>. T = \<theta><T'> \<and> Dom \<theta> = Xs)"
apply(auto)
defer
apply(simp add: generalises_def)
apply(auto)[1]
apply(auto)[1]
apply(drule sym)
apply(simp add: Abs_eq_iff2)
apply(simp add: alphas)
apply(auto)
apply(rule_tac x="map (\<lambda>(X, T). (p \<bullet> X, T)) \<theta>" in exI)
apply(auto)
oops

*)

end
