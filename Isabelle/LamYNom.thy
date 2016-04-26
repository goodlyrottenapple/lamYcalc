theory LamYNom
imports "Nominal2-Isabelle2016/Nominal/Nominal2" begin

text {* Disclaimer: Some of the definitions were copied over and adapted from Nominal2-Isabelle2015/Nominal/Nominal2/Ex/Lambda.thy *}

atom_decl name

atom_decl TV

nominal_datatype type = Typ TV | Arr type type ("_ \<rightarrow> _")

nominal_datatype lam =
  Var "name"
| App "lam" "lam"
| Lam x::name l::lam  binds x in l ("Lam [_]. _" [100, 100] 100)
| Y type

nominal_function
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_ [_ ::= _]" [90, 90, 90] 90)
where
  "(Var x)[y ::= s] = (if x = y then s else (Var x))"
| "(App t1 t2)[y ::= s] = App (t1[y ::= s]) (t2[y ::= s])"
| "atom x \<sharp> (y, s) \<Longrightarrow> (Lam [x]. t)[y ::= s] = Lam [x].(t[y ::= s])"
| "(Y t)[y ::= s] = Y t"
  apply(simp add: eqvt_def subst_graph_aux_def)
  apply(rule TrueI)
  using [[simproc del: alpha_lst]]
  apply(auto)
  apply(rule_tac y="a" and c="(aa, b)" in lam.strong_exhaust)
  apply(blast)+
  apply(simp_all add: fresh_star_def fresh_Pair_elim)
  apply (erule_tac c="(ya,sa)" in Abs_lst1_fcb2)
  apply(simp_all add: Abs_fresh_iff)
  apply(simp add: fresh_star_def fresh_Pair)
  apply(simp only: eqvt_at_def)
  apply(simp)
  apply(simp add: fresh_star_Pair perm_supp_eq)
  apply(simp only: eqvt_at_def)
  apply(perm_simp)
  apply(simp)
  apply(simp add: fresh_star_Pair perm_supp_eq)
done

nominal_termination (eqvt)
  by lexicographic_order


lemma forget:
  shows "atom x \<sharp> t \<Longrightarrow> t[x ::= s] = t"
  by (nominal_induct t avoiding: x s rule: lam.strong_induct)
     (auto simp add: fresh_at_base)

lemma fresh_type:
  fixes n :: name and t :: type
  shows "atom n \<sharp> t"
  by (nominal_induct t rule:type.strong_induct, auto)

lemma fresh_fact:
  fixes z::"name"
  assumes a: "atom z \<sharp> s"
      and b: "z = y \<or> atom z \<sharp> t"
  shows "atom z \<sharp> t[y ::= s]"
  using a b
  apply (nominal_induct t avoiding: z y s rule: lam.strong_induct)
  by (auto simp add:fresh_type)
 


lemma substitution_lemma:  
  assumes a: "x \<noteq> y" "atom x \<sharp> u"
  shows "t[x ::= s][y ::= u] = t[y ::= u][x ::= s[y ::= u]]"
using a 
by (nominal_induct t avoiding: x y s u rule: lam.strong_induct)
   (auto simp add: fresh_fact forget)

subsection {* well typed terms *}

inductive
  wt_terms :: "(name \<times> type) set \<Rightarrow> lam \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ : _")
where
  var: "(x,\<sigma>) \<in> \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Var x : \<sigma>"
| app: "\<lbrakk> \<Gamma> \<turnstile> M : \<sigma> \<rightarrow> \<tau> ; \<Gamma> \<turnstile> N : \<sigma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App M N : \<tau>"
(* condition "atom x \<sharp> \<Gamma>" in abst should ensure that (x,\<sigma>) is consistent with \<Gamma> *)
| abs: "\<lbrakk> atom x \<sharp> \<Gamma> ; \<Gamma> \<union> {(x,\<sigma>)} \<turnstile> M : \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x]. M : \<sigma> \<rightarrow> \<tau>"
| Y: "\<Gamma> \<turnstile> Y \<sigma> : (\<sigma> \<rightarrow> \<sigma>) \<rightarrow> \<sigma>"

equivariance wt_terms
nominal_inductive wt_terms
(*  avoids abs: "x" 
  apply (simp_all add: fresh_star_def fresh_Pair fresh_fact fresh_type)*)
done

subsection {* single-step beta-reduction *}

inductive 
  beta :: "lam \<Rightarrow> lam \<Rightarrow> bool" (" _ \<Rightarrow> _" [80,80] 80)
where
  red_L[intro]: "\<lbrakk> M \<Rightarrow> M' \<rbrakk> \<Longrightarrow> App M N \<Rightarrow> App M' N"
| red_R[intro]: "\<lbrakk> N \<Rightarrow> N' \<rbrakk> \<Longrightarrow> App M N \<Rightarrow> App M N'"
| abs[intro]: "\<lbrakk> M \<Rightarrow> M' \<rbrakk> \<Longrightarrow> Lam [x]. M \<Rightarrow> Lam [x]. M'"
| beta[intro]: "\<lbrakk> atom x \<sharp> N \<rbrakk> \<Longrightarrow> App (Lam [x]. M) N \<Rightarrow> M[x ::= N]"

equivariance beta
nominal_inductive beta
  avoids beta: "x"
  by (simp_all add: fresh_star_def fresh_Pair fresh_fact)


lemma beta_Ytyp:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
  and "M \<Rightarrow> M'"
  shows "\<Gamma> \<turnstile> M' : \<sigma>"
using assms(2,1) 
proof (nominal_induct  M M' arbitrary: \<Gamma> \<sigma> rule: beta.strong_induct)
case (red_L M M' N)
  from red_L(3) obtain \<tau> where 1: "\<Gamma> \<turnstile> M : \<tau> \<rightarrow> \<sigma>" "\<Gamma> \<turnstile> N : \<tau>"
    by (metis lam.distinct(1) lam.distinct(7) lam.distinct(9) lam.eq_iff(2) wt_terms.simps)
  with red_L(2) have "\<Gamma> \<turnstile> M' : \<tau> \<rightarrow> \<sigma>" by simp
  thus ?case 
  apply (rule wt_terms.app)
  using 1 by simp
next
case (red_R N N' M)
  from red_R(3) obtain \<tau> where 1: "\<Gamma> \<turnstile> M : \<tau> \<rightarrow> \<sigma>" "\<Gamma> \<turnstile> N : \<tau>"
    by (metis lam.distinct(1) lam.distinct(7) lam.distinct(9) lam.eq_iff(2) wt_terms.simps)
  with red_R(2) have 2: "\<Gamma> \<turnstile> N' : \<tau>" by simp
  show ?case 
  apply (rule wt_terms.app)
  using 1 2 by simp+
next
case (abs M M' x)
  from abs(3) obtain \<pi> \<tau> where 1: "\<sigma> = \<pi> \<rightarrow> \<tau>" "\<Gamma> \<turnstile> Lam [x]. M : \<pi> \<rightarrow> \<tau>" by (metis lam.distinct(3) lam.distinct(7) wt_terms.simps)
  then have 2: "atom x \<sharp> \<Gamma>" "\<Gamma> \<union> {(x,\<pi>)} \<turnstile> M : \<tau>" using wt_terms.cases sorry (* need a different cases rule *)
  with abs(2) have 3: "\<Gamma> \<union> {(x,\<pi>)} \<turnstile> M' : \<tau>" by simp
  
  show ?case
  apply (subst 1(1))
  apply (rule wt_terms.abs)
  using 2 3 by simp+
next
case (beta x N M) 
  from beta(2) obtain \<tau> where 1: "\<Gamma> \<turnstile> (Lam [x]. M) : \<tau> \<rightarrow> \<sigma>" "\<Gamma> \<turnstile> N : \<tau>" 
    by (metis lam.distinct(1) lam.distinct(7) lam.distinct(9) lam.eq_iff(2) wt_terms.simps)
  then have 2: "atom x \<sharp> \<Gamma>" "\<Gamma> \<union> {(x,\<tau>)} \<turnstile> M : \<sigma>" using wt_terms.cases sorry (* need a different cases rule *)
  show ?case sorry
qed

inductive 
  beta_eta_Y :: "lam \<Rightarrow> lam \<Rightarrow> bool" (" _ \<Rightarrow>Y _" [80,80] 80)
where
  red_L[intro]: "\<lbrakk> M \<Rightarrow>Y M' \<rbrakk> \<Longrightarrow> App M N \<Rightarrow>Y App M' N"
| red_R[intro]: "\<lbrakk> N \<Rightarrow>Y N' \<rbrakk> \<Longrightarrow> App M N \<Rightarrow>Y App M N'"
| abs[intro]: "\<lbrakk> M \<Rightarrow>Y M' \<rbrakk> \<Longrightarrow> Lam [x]. M \<Rightarrow>Y Lam [x]. M'"
| beta[intro]: "\<lbrakk> atom x \<sharp> N \<rbrakk> \<Longrightarrow> App (Lam [x]. M) N \<Rightarrow>Y M[x ::= N]"
| eta[intro]: "\<lbrakk> atom x \<sharp> M \<rbrakk> \<Longrightarrow> App (Lam [x]. M) (Var x) \<Rightarrow>Y M"
| Y[intro]: "App (Y \<sigma>) M \<Rightarrow>Y App M (App (Y \<sigma>) M)"

equivariance beta_eta_Y
nominal_inductive beta_eta_Y
  avoids beta: "x"
  by (simp_all add: fresh_star_def fresh_Pair fresh_fact)


lemma beta_Ytyp:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
  and "M \<Rightarrow>Y M'"
  shows "\<Gamma> \<turnstile> M' : \<sigma>"
using assms(2,1) 
proof (nominal_induct  M M' arbitrary: \<Gamma> \<sigma> rule: beta_eta_Y.strong_induct)
case (eta x M) 
  from eta(2) obtain \<tau> where 1: "\<Gamma> \<turnstile> (Lam [x]. M) : \<tau> \<rightarrow> \<sigma>" "\<Gamma> \<turnstile> (Var x) : \<tau>" 
    by (metis lam.distinct(1) lam.distinct(7) lam.distinct(9) lam.eq_iff(2) wt_terms.simps)
  then have 2: "atom x \<sharp> \<Gamma>" "\<Gamma> \<union> {(x,\<tau>)} \<turnstile> M : \<sigma>" using wt_terms.cases sorry (* need a different cases rule *)
  show ?case sorry (*prove that if x \<sharp> M together with \<Gamma> \<union> {(x,\<tau>)} \<turnstile> M : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> M : \<sigma> *)
next
case (Y \<tau> M)
  from Y obtain \<pi> where 1: "\<Gamma> \<turnstile> (Y \<tau>) : \<pi> \<rightarrow> \<sigma>" "\<Gamma> \<turnstile> M : \<pi>" 
    by (metis lam.distinct(1) lam.distinct(7) lam.distinct(9) lam.eq_iff(2) wt_terms.simps)

  have "\<Gamma> \<turnstile> (Y \<tau>) : (\<tau> \<rightarrow> \<tau>) \<rightarrow> \<tau>" by (rule wt_terms.Y)
  with 1(1) have "\<pi> \<rightarrow> \<sigma> = (\<tau> \<rightarrow> \<tau>) \<rightarrow> \<tau>" by (metis lam.distinct(11) lam.distinct(6) lam.distinct(9) lam.eq_iff(4) wt_terms.simps)
  then have 2: "\<pi> = \<tau> \<rightarrow> \<tau>" "\<sigma> = \<tau>" by simp+
  show ?case
    apply (subst 2)
    apply (rule wt_terms.app)
    defer
    apply (rule wt_terms.app)
    apply (rule wt_terms.Y)
    using 1(2) 2(1) by simp+
qed



(*
subsection {* parallel beta reduction *}

inductive 
  pbeta :: "(name \<times> type) set \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ \<Rightarrow>\<parallel> _ : _" [80,80] 80)
where
  refl[intro]: "\<lbrakk> (x,\<sigma>) \<in> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Var x) \<Rightarrow>\<parallel> (Var x) : \<sigma>"
| app[intro]: "\<lbrakk> \<Gamma> \<turnstile> M \<Rightarrow>\<parallel> M' : \<sigma> \<rightarrow> \<tau> ; \<Gamma> \<turnstile> N \<Rightarrow>\<parallel> N' : \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App M N \<Rightarrow>\<parallel> App M' N' : \<tau>"
| abs[intro]: "\<lbrakk> atom x \<sharp> \<Gamma> ; ({(x,\<sigma>)} \<union> \<Gamma>) \<turnstile> M \<Rightarrow>\<parallel> M' : \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x]. M \<Rightarrow>\<parallel> Lam [x]. M' : \<sigma> \<rightarrow> \<tau>"
| beta[intro]: "\<lbrakk> atom x \<sharp> N ; atom x \<sharp> N' ; atom x \<sharp> \<Gamma> ; (\<Gamma> \<union> {(x, \<sigma>)}) \<turnstile> M \<Rightarrow>\<parallel> M' : \<tau> ; \<Gamma> \<turnstile> N \<Rightarrow>\<parallel> N' : \<sigma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App (Lam [x]. M) N \<Rightarrow>\<parallel> M'[x ::= N'] : \<tau>"

equivariance pbeta

nominal_inductive pbeta
(*  avoids beta: "x" (*don't understand what this does exactly or why we need it...*)
  apply (simp_all add: fresh_star_def fresh_Pair fresh_fact fresh_type)
oops*)
done


nominal_function 
  not_abst :: "lam \<Rightarrow> bool"
where
  "not_abst (Var x) = True"
| "not_abst (App t1 t2) = True"
| "not_abst (Lam [x]. t) = False"
| "not_abst (Y t) = True"
apply (simp add: eqvt_def not_abst_graph_aux_def)
apply (rule TrueI)
apply (rule_tac y="x" in lam.exhaust)
using [[simproc del: alpha_lst]]
by auto

nominal_termination (eqvt) by lexicographic_order


subsection {* parallel beta reduction *}

inductive 
  pbeta_max :: "(name \<times> type) set \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ >>> _ : _" [80,80] 80)
where
  refl[intro]: "\<lbrakk> (x,\<sigma>) \<in> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Var x) >>> (Var x) : \<sigma>"
| app[intro]: "\<lbrakk> not_abst M ; \<Gamma> \<turnstile> M >>> M' : \<sigma> \<rightarrow> \<tau> ; \<Gamma> \<turnstile> N >>> N' : \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App M N >>> App M' N' : \<tau>"
| abs[intro]: "\<lbrakk> atom x \<sharp> \<Gamma> ; ({(x,\<sigma>)} \<union> \<Gamma>) \<turnstile> M >>> M' : \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x]. M >>> Lam [x]. M' : \<sigma> \<rightarrow> \<tau>"
| beta[intro]: "\<lbrakk> atom x \<sharp> N ; atom x \<sharp> N' ; atom x \<sharp> \<Gamma> ; (\<Gamma> \<union> {(x, \<sigma>)}) \<turnstile> M >>> M' : \<tau> ; \<Gamma> \<turnstile> N >>> N' : \<sigma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App (Lam [x]. M) N >>> M'[x ::= N'] : \<tau>"


equivariance pbeta_max

nominal_inductive pbeta_max
  (*avoids beta: "x" | abs: "x" (*don't understand what this does exactly or why we need it in the abs case ...*)
  by (simp_all add: fresh_star_def fresh_Pair fresh_fact)*)
done



lemma Ex1_5: "x \<noteq> y \<Longrightarrow> atom x \<sharp> u \<Longrightarrow> (s[x ::= t])[y ::= u] = s[y ::= u][x ::= t[y ::= u]]"
proof (nominal_induct s avoiding: x y u t rule:lam.strong_induct)
case (Var s) thus ?case
  apply (cases "x = s")
  apply (cases "y = s")
  apply simp
  defer
  apply simp
  apply (subst forget) using Var
  by simp+
next
case (App p q)
  thus ?case by simp
next
case (Lam z p)
  show ?case 
  apply (subst subst.simps(3), simp add: Lam fresh_fact)+
  using Lam by simp
next
case Y thus ?case by simp
qed

lemma Lem2_5_1:
  assumes "L \<turnstile> s \<Rightarrow>\<parallel> s' : a"
      and "L \<turnstile> t \<Rightarrow>\<parallel> t' : b"
    shows "L \<turnstile> (s[x ::= t]) \<Rightarrow>\<parallel> (s'[x ::= t']) : a"
using assms proof (nominal_induct L s s' a avoiding: x t t' b  rule:pbeta.strong_induct)
case (refl y)
  thus ?case 
  unfolding subst.simps
  apply (cases "y = x")
  defer
  apply auto[1]
  sorry

next
case app
  show ?case 
  unfolding subst.simps
  apply (rule pbeta.app)
  using app
  by auto
next
case (beta x' N N' \<Gamma> \<sigma> M M' \<tau>')
  have 1: "\<Gamma> \<turnstile> App (Lam [x']. M [x ::= t])
          (N [x ::= t]) \<Rightarrow>\<parallel> M' [x ::= t'] [x' ::= N' [x ::= t']] : \<tau>'"
  apply (subst subst.simps(3))
  defer
  apply (rule_tac pbeta.beta)
  using beta sorry

  show ?case unfolding subst.simps
  apply (subst Ex1_5) 
  defer
  defer
  using 1 apply simp
  using beta sorry
next
case abs
  show ?case 
  apply (subst subst.simps)
  defer
  apply (subst subst.simps)
  defer
  apply (rule_tac pbeta.abs)
  using abs apply simp
  using abs
qed
*)


(*
lemma Lem2_5_1:
  assumes "s \<rightarrow>\<parallel>b s'"
      and "t \<rightarrow>\<parallel>b t'"
      shows "(s[x ::= t]) \<rightarrow>\<parallel>b (s'[x ::= t'])"
using assms proof (nominal_induct s s' avoiding: x t t' rule:pbeta.strong_induct)
case (refl s)
  then show ?case by auto
  (*proof (nominal_induct s avoiding: x t t' rule:lam.strong_induct)
  case (Var n) 
    thus ?case unfolding subst.simps
    apply (cases "n = x") 
    apply simp+
    by (rule pbeta.refl)
  next
  case App thus ?case unfolding subst.simps apply (rule_tac pbeta.p_app) by simp+
  next
  case Lam thus ?case unfolding subst.simps by auto
  qed*)
next
case p_app
  show ?case 
  unfolding subst.simps
  apply (rule pbeta.p_app)
  using p_app
  by simp+
next
case (p_beta y q' q p p')
  have "App ((Lam [y]. p) [x ::= t]) (q [x ::= t]) \<rightarrow>\<parallel>b (p' [x ::= t'])[y ::= q'[x ::= t']]"
  apply (subst subst.simps(3))
  defer
  apply (rule_tac pbeta.p_beta)
  using p_beta by (simp add: fresh_fact)+

  then show ?case unfolding subst.simps
  apply (subst Ex1_5) using p_beta by simp+
next
case (p_abs p p' y) 
  show ?case 
  apply (subst subst.simps)
  using p_abs apply simp
  apply (subst subst.simps)
  using p_abs apply simp
  apply (rule_tac pbeta.p_abs)
  using p_abs by simp
qed


lemma pbeta_refl[intro]: "s \<rightarrow>\<parallel>b s"
apply (induct s rule:lam.induct)
by auto


lemma pbeta_max_ex:
  fixes a
  shows "\<exists>d. a >>> d"
apply (nominal_induct a rule:lam.strong_induct)
apply auto
apply (case_tac "not_abst lam1")
apply auto[1]
proof -
case goal1 
  thus ?case
  apply (nominal_induct lam1 d avoiding: da lam2 rule:pbeta_max.strong_induct)
  by auto
qed



lemma subst_rename: 
  assumes a: "atom y \<sharp> t"
  shows "t[x ::= s] = ((y \<leftrightarrow> x) \<bullet> t)[y ::= s]"
using a 
apply (nominal_induct t avoiding: x y s rule: lam.strong_induct)
apply (auto simp add:  fresh_at_base)
done


lemma fresh_in_pbeta: "s \<rightarrow>\<parallel>b s' \<Longrightarrow> atom (x::name) \<sharp> s \<Longrightarrow>  atom x \<sharp> s'"
apply (nominal_induct s s' rule:pbeta.strong_induct)
apply simp
apply simp
apply auto[1]
proof - 
case (goal1 xx)
  then have "atom x \<sharp> t" by simp
  { assume "x = xx" with goal1 have ?case by (simp add: fresh_fact) }
  { assume "x \<noteq> xx" with goal1 have ?case by (simp add: fresh_fact) }
  thus ?case using `x = xx \<Longrightarrow> atom x \<sharp> s' [xx ::= t']` by blast
qed


(* adopting great naming conventions so early on! *)
lemma aaaaa2: "(Lam [x]. s) \<rightarrow>\<parallel>b s' \<Longrightarrow> \<exists>t. s' = Lam [x]. t \<and> s \<rightarrow>\<parallel>b t"
proof (cases "(Lam [x]. s)" s' rule:pbeta.cases, simp)
  case (goal1 _ _ x')
    then have 1: "s \<rightarrow>\<parallel>b ((x' \<leftrightarrow> x) \<bullet> t2)" using pbeta.eqvt by (metis Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_commute flip_def permute_flip_cancel2 permute_plus)
    from goal1 have 2: "(x' \<leftrightarrow> x) \<bullet> s' = Lam [x]. ((x' \<leftrightarrow> x) \<bullet> t2)" by simp
    from goal1 have "atom x \<sharp> (Lam [x']. t2)"  using fresh_in_pbeta by (meson lam.fresh(3) list.set_intros(1))
    with 2 have "s' = Lam [x]. ((x' \<leftrightarrow> x) \<bullet> t2)" unfolding goal1 by (metis "2" flip_fresh_fresh goal1(3) lam.fresh(3) list.set_intros(1))
    with 1 show ?case by auto
qed

thm pbeta.cases
lemma pbeta_cases_2:
  shows "atom x \<sharp> t \<Longrightarrow> App (Lam [x]. s) t \<rightarrow>\<parallel>b a2 \<Longrightarrow> 
    (\<And>s' t'. a2 = App (Lam [x]. s') t' \<Longrightarrow> atom x \<sharp> t' \<Longrightarrow> s \<rightarrow>\<parallel>b s' \<Longrightarrow> t \<rightarrow>\<parallel>b t' \<Longrightarrow> P) \<Longrightarrow>
    (\<And>t' s'. a2 = s' [x ::= t'] \<Longrightarrow> atom x \<sharp> t' \<Longrightarrow> atom x \<sharp> t \<Longrightarrow> s \<rightarrow>\<parallel>b s' \<Longrightarrow> t \<rightarrow>\<parallel>b t' \<Longrightarrow> P) \<Longrightarrow> P"
apply atomize_elim
proof (cases "App (Lam [x]. s) t" a2 rule:pbeta.cases, simp)
case goal1 
  then obtain s'' where 1: "s' = Lam [x]. s''" "s \<rightarrow>\<parallel>b s''" using aaaaa2 by blast
  thus ?case using goal1 fresh_in_pbeta  by auto
next
case (goal2 xx _ ss)
  have 1: "s' [xx ::= t'] = ((x \<leftrightarrow> xx) \<bullet> s') [x ::= t']"
    by (metis (no_types, lifting) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def fresh_in_pbeta goal2(3) goal2(7) permute_flip_cancel permute_plus subst_rename) 
  from goal2 have 2: "s \<rightarrow>\<parallel>b ((x \<leftrightarrow> xx) \<bullet> s')"
    by (metis Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def pbeta.eqvt permute_flip_cancel permute_plus)
  from goal2 have 3: "atom x \<sharp> t'" using fresh_in_pbeta by simp
  with goal2 1 2 show ?case by auto
qed


lemma pbeta_max_closes_pbeta:
  fixes a b d
  assumes "a >>> d"
  and "a \<rightarrow>\<parallel>b b"
  shows "b \<rightarrow>\<parallel>b d"
using assms proof (nominal_induct arbitrary: b rule:pbeta_max.strong_induct)
case (cd_refl a)  
  show ?case using cd_refl pbeta.cases by fastforce
next
case (cd_beta u ard ar al ald)
  from cd_beta(2,7) show ?case
  apply (rule_tac pbeta_cases_2)
  apply (simp, simp)
  proof -
  case (goal2 arb alb)
    with cd_beta have "alb \<rightarrow>\<parallel>b ald" "arb \<rightarrow>\<parallel>b ard" by simp+
    thus ?case unfolding goal2 apply (rule_tac Lem2_5_1) by simp+
  next
  case (goal1 alb arb)
    with cd_beta have ih: "alb \<rightarrow>\<parallel>b ald" "arb \<rightarrow>\<parallel>b ard" by simp+
    show ?case unfolding goal1 
    apply (rule_tac pbeta.p_beta) using goal1 cd_beta ih
    by simp_all
  qed
next
case (cd_app al ald ar ard) 
  from cd_app(6,1) show ?case
  apply (cases "App al ar" b rule:pbeta.cases)
  defer
  apply simp
  using cd_app by auto
next
case (cd_abs al ald x) thus ?case using aaaaa2 by blast
qed


lemma Lem2_5_2: 
  assumes "a \<rightarrow>\<parallel>b b"
      and "a \<rightarrow>\<parallel>b c"
    shows "\<exists>d. b \<rightarrow>\<parallel>b d \<and> c \<rightarrow>\<parallel>b d"
proof -
  obtain d where 1: "a >>> d" using pbeta_max_ex by auto
  have "b \<rightarrow>\<parallel>b d \<and> c \<rightarrow>\<parallel>b d" 
  apply rule 
  apply (rule_tac pbeta_max_closes_pbeta)
  using 1 assms apply simp+
  apply (rule_tac pbeta_max_closes_pbeta)
  using 1 assms apply simp+
  done
  thus ?thesis by auto
qed


inductive beta_c :: "lam \<Rightarrow> lam \<Rightarrow> bool" ("_ \<longrightarrow>b* _" [80,80] 80)
where
  base[intro]: "a \<longrightarrow>b b \<Longrightarrow> a \<longrightarrow>b* b"
| refl[intro]: "a \<longrightarrow>b* a"
| trans[intro]: "\<lbrakk> a \<longrightarrow>b* b ; b \<longrightarrow>b* c \<rbrakk> \<Longrightarrow> a \<longrightarrow>b* c"


inductive pbeta_c :: "lam \<Rightarrow> lam \<Rightarrow> bool" ("_ \<rightarrow>\<parallel>b* _" [80,80] 80)
where
  base[intro]: "a \<rightarrow>\<parallel>b b \<Longrightarrow> a \<rightarrow>\<parallel>b* b"
| refl[intro]: "a \<rightarrow>\<parallel>b* a"
| trans[intro]: "\<lbrakk> a \<rightarrow>\<parallel>b* b ; b \<rightarrow>\<parallel>b* c \<rbrakk> \<Longrightarrow> a \<rightarrow>\<parallel>b* c"


definition DP :: "(lam \<Rightarrow> lam \<Rightarrow> bool) \<Rightarrow> (lam \<Rightarrow> lam \<Rightarrow> bool) \<Rightarrow> bool" where
"DP R T = (\<forall>a b c. R a b \<and> T a c \<longrightarrow> (\<exists>d. T b d \<and> R c d))"

lemma DP_R_R_imp_DP_R_Rc_pbeta:
  assumes "DP pbeta pbeta"
    shows "DP pbeta pbeta_c"
using assms unfolding DP_def
apply auto
proof -
case goal1 
  from goal1(3,2) show ?case
  apply (induct arbitrary: b rule:pbeta_c.induct)
  using goal1(1) by blast+
qed

lemma DP_R_R_imp_DP_Rc_Rc_pbeta:
  assumes "DP pbeta pbeta"
    shows "DP pbeta_c pbeta_c"
using assms unfolding DP_def
apply auto
proof -
case goal1 
  from goal1(2,3) show ?case
  apply (induct arbitrary: c rule:pbeta_c.induct)
  using DP_R_R_imp_DP_R_Rc_pbeta using DP_def assms apply fastforce
  apply auto
  by blast
qed

lemma M1: "m \<longrightarrow>b* m' \<Longrightarrow> m \<rightarrow>\<parallel>b* m'" sorry
lemma M2: "m \<rightarrow>\<parallel>b* m' \<Longrightarrow> m \<longrightarrow>b* m'"
proof (nominal_induct m avoiding: m' rule:lam.strong_induct)
print_cases
case (Var x) thus ?case 
  apply (cases rule:pbeta_c.cases)
  apply (cases "Var x" m' rule:pbeta.cases)
  apply simp 
  apply auto
  proof -
  case goal1 from goal1(1,2) show ?case sorry
  qed
next
case (App p q) from App(3) show ?case
  apply (cases rule:pbeta_c.cases)
defer
apply auto[1]
defer
  apply (cases "App p q" m' rule:pbeta.cases)
  apply auto[1]
  apply auto[1]
  sorry
next
case (Lam x p p') thus ?case sorry
qed



lemma church_rosser:
  assumes "a \<longrightarrow>b* b"
      and "a \<longrightarrow>b* c"
    shows "\<exists>d. b \<longrightarrow>b* d \<and> c \<longrightarrow>b* d"
proof -
  from assms have "a \<rightarrow>\<parallel>b* b" "a \<rightarrow>\<parallel>b* c" using M1 by simp+
  then obtain d where "b \<rightarrow>\<parallel>b* d" "c \<rightarrow>\<parallel>b* d" by (metis DP_R_R_imp_DP_Rc_Rc_pbeta DP_def Lem2_5_2) 
  thus ?thesis using M2 by blast
qed
*)

end

