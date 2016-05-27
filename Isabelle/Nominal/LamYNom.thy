theory LamYNom2
imports "Nominal2-Isabelle2016/Nominal/Nominal2" begin

text {* Disclaimer: Some of the definitions were copied over and adapted from Nominal2-Isabelle2015/Nominal/Nominal2/Ex/Lambda.thy *}

atom_decl name

atom_decl TV

nominal_datatype type = Typ TV | Arr type type ("_ \<rightarrow> _")

nominal_datatype trm =
  Var name
| App trm trm
| Lam x::name l::trm  binds x in l ("Lam [_]. _" [100, 100] 100)
| Y type

nominal_function
  subst :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm"  ("_ [_ ::= _]" [90, 90, 90] 90)
where
  "(Var x)[y ::= s] = (if x = y then s else (Var x))"
| "(App t1 t2)[y ::= s] = App (t1[y ::= s]) (t2[y ::= s])"
| "atom x \<sharp> (y, s) \<Longrightarrow> (Lam [x]. t)[y ::= s] = Lam [x].(t[y ::= s])"
| "(Y t)[y ::= s] = Y t"
  apply(simp add: eqvt_def subst_graph_aux_def)
  apply(rule TrueI)
  using [[simproc del: alpha_lst]]
  apply(auto)
  apply(rule_tac y="a" and c="(aa, b)" in trm.strong_exhaust)
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

lemma "Lam [x]. Var x = Lam [y]. Var y" by simp

nominal_termination (eqvt)
  by lexicographic_order


lemma forget:
  shows "atom x \<sharp> t \<Longrightarrow> t[x ::= s] = t"
  by (nominal_induct t avoiding: x s rule: trm.strong_induct)
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
  apply (nominal_induct t avoiding: z y s rule: trm.strong_induct)
  by (auto simp add:fresh_type)
 


lemma substitution_lemma:  
  assumes a: "x \<noteq> y" "atom x \<sharp> u"
  shows "t[x ::= s][y ::= u] = t[y ::= u][x ::= s[y ::= u]]"
using a 
by (nominal_induct t avoiding: x y s u rule: trm.strong_induct)
   (auto simp add: fresh_fact forget)

subsection {* well typed terms *}

inductive wf_ctxt :: "(name \<times> type) list \<Rightarrow> bool"
where
    nil:  "wf_ctxt []"
  | cons:  "\<lbrakk> wf_ctxt \<Gamma> ; atom x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> wf_ctxt ((x,\<sigma>)#\<Gamma>)"
equivariance wf_ctxt


inductive
  wt_terms :: "(name \<times> type) list \<Rightarrow> trm \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ : _")
where
  var: "\<lbrakk> (x,\<sigma>) \<in> set \<Gamma> ; wf_ctxt \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x : \<sigma>"
| app: "\<lbrakk> \<Gamma> \<turnstile> M : \<sigma> \<rightarrow> \<tau> ; \<Gamma> \<turnstile> N : \<sigma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App M N : \<tau>"
(* condition "atom x \<sharp> \<Gamma>" in abst should ensure that (x,\<sigma>) is consistent with \<Gamma> *)
| abs: "\<lbrakk> atom x \<sharp> \<Gamma> ; ((x,\<sigma>)#\<Gamma>) \<turnstile> M : \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x]. M : \<sigma> \<rightarrow> \<tau>"
| Y: "\<lbrakk> wf_ctxt \<Gamma> \<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile> Y \<sigma> : (\<sigma> \<rightarrow> \<sigma>) \<rightarrow> \<sigma>"

equivariance wt_terms
nominal_inductive wt_terms
avoids abs: "x" 
  by (simp_all add: fresh_star_def fresh_Pair fresh_fact fresh_type)


(*lemma wf_ctxt_subset: "wf_ctxt \<Gamma> \<Longrightarrow> \<Gamma>' \<subseteq> \<Gamma> \<Longrightarrow> wf_ctxt \<Gamma>'"
proof (induct \<Gamma> arbitrary: \<Gamma>' rule:wf_ctxt.induct)
case nil 
  thus ?case
  apply simp
  by (rule wf_ctxt.nil)
next
case (cons \<Gamma> x \<sigma>)
  show ?case
  proof (cases "(x, \<sigma>) \<in> \<Gamma>")
  case True 
    then have "insert (x, \<sigma>) \<Gamma> = \<Gamma>" by auto
    thus ?thesis using cons by simp
  next
  case False 
    with cons have 1: "(\<Gamma>' - {(x, \<sigma>)}) \<subseteq> \<Gamma>" by auto
    with cons have "wf_ctxt (\<Gamma>' - {(x, \<sigma>)})" by simp

    from 1 cons(3) have "atom x \<sharp> (\<Gamma>' - {(x, \<sigma>)})" try
    with cons(3) have "wf_ctxt (insert (x, \<sigma>) (\<Gamma>' - {(x, \<sigma>)}))" using wf_ctxt.cons
*)
lemma wf_ctxt_cons: "wf_ctxt ((x, \<sigma>)#\<Gamma>) \<Longrightarrow> wf_ctxt \<Gamma> \<and> atom x \<sharp> \<Gamma>"
apply (cases rule:wf_ctxt.cases)
by auto


lemma wt_terms_impl_wf_ctxt: "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> wf_ctxt \<Gamma>"
apply (induct rule:wt_terms.induct)
by (auto simp add: wf_ctxt_cons)


lemma weakening:
  fixes \<Gamma> \<Gamma>' M \<sigma>
  assumes "\<Gamma> \<turnstile> M : \<sigma>" and "set \<Gamma> \<subseteq> set \<Gamma>'"
  and "wf_ctxt \<Gamma>'"
  shows "\<Gamma>' \<turnstile> M : \<sigma>"
using assms proof (nominal_induct \<Gamma> M \<sigma> avoiding: \<Gamma>' rule:wt_terms.strong_induct)
case var 
  show ?case 
  apply (rule wt_terms.var) 
  using var by auto
next
case app
  show ?case
  apply (rule wt_terms.app)
  using app by auto
next
case (abs x \<Gamma> \<sigma> M \<tau>)
  have 1: "wf_ctxt ((x, \<sigma>) # \<Gamma>')" 
  apply (rule cons)
  using abs by simp+

  show ?case
  apply (rule wt_terms.abs)
  using "1" wf_ctxt.cases apply auto[1]
  apply (rule abs(4))
  using abs apply auto[1]
  using 1 by simp
next
case Y thus ?case using wt_terms.Y by simp
qed


lemma wf_ctxt_exchange: "wf_ctxt ((x,\<sigma>) # (y,\<pi>) # \<Gamma>) \<Longrightarrow> wf_ctxt ((y,\<pi>) # (x,\<sigma>) # \<Gamma>)"
proof goal_cases
case 1 
  then have 1: "wf_ctxt ((y,\<pi>) # \<Gamma>)" "atom x \<sharp> ((y,\<pi>) # \<Gamma>)" by (simp add: wf_ctxt_cons)+
  from 1(1) have 2: "wf_ctxt \<Gamma>" "atom y \<sharp> \<Gamma>" by (simp add: wf_ctxt_cons)+
  from 1(2) have 3: "atom x \<sharp> \<Gamma>" using fresh_Cons by blast
  from 1(2) 2(2) have 4: "atom y \<sharp> ((x,\<sigma>) # \<Gamma>)" by (metis fresh_Cons fresh_Pair fresh_at_base(2) fresh_type)

  show ?case
  apply (rule cons)
  apply (rule cons)
  by (simp add: 2 3 4)+
qed

lemma exchange: "(x,\<sigma>) # (y,\<pi>) # \<Gamma> \<turnstile> M : \<delta> \<Longrightarrow> (y,\<pi>) # (x,\<sigma>) # \<Gamma> \<turnstile> M : \<delta>"
proof goal_cases
case 1
  have "set ((x,\<sigma>) # (y,\<pi>) # \<Gamma>) \<subseteq> set ((y,\<pi>) # (x,\<sigma>) # \<Gamma>)" by auto
  thus ?case using 1 weakening wt_terms_impl_wf_ctxt wf_ctxt_exchange by blast
qed

inductive 
  beta_Y :: "trm \<Rightarrow> trm \<Rightarrow> bool" (" _ \<Rightarrow> _" [80,80] 80)
where
  red_L[intro]: "\<lbrakk> M \<Rightarrow> M' \<rbrakk> \<Longrightarrow> App M N \<Rightarrow> App M' N"
| red_R[intro]: "\<lbrakk> N \<Rightarrow> N' \<rbrakk> \<Longrightarrow> App M N \<Rightarrow> App M N'"
| abs[intro]: "\<lbrakk> M \<Rightarrow> M' \<rbrakk> \<Longrightarrow> Lam [x]. M \<Rightarrow> Lam [x]. M'"
| beta[intro]: "\<lbrakk> atom x \<sharp> N \<rbrakk> \<Longrightarrow> App (Lam [x]. M) N \<Rightarrow> M[x ::= N]"
(*| eta[intro]: "\<lbrakk> atom x \<sharp> M \<rbrakk> \<Longrightarrow> App (Lam [x]. M) (Var x) \<Rightarrow>Y M"*)
| Y[intro]: "App (Y \<sigma>) M \<Rightarrow> App M (App (Y \<sigma>) M)"

equivariance beta_Y
nominal_inductive beta_Y
  avoids beta: "x" | abs: "x"
  by (simp_all add: fresh_star_def fresh_Pair fresh_fact fresh_type)



lemma  wt_terms_cases_2:
  shows "\<Gamma> \<turnstile> Lam [x]. M : a3 \<Longrightarrow> atom x \<sharp> \<Gamma>\<Longrightarrow> (\<And>\<sigma> \<tau>. a3 = \<sigma> \<rightarrow> \<tau> \<Longrightarrow> ((x, \<sigma>)#\<Gamma>) \<turnstile> M : \<tau> \<Longrightarrow> P) \<Longrightarrow> P"
apply atomize_elim
apply (cases \<Gamma> "Lam [x]. M" a3 rule:wt_terms.cases, simp)
proof goal_cases
case (1 x' \<sigma> M' \<tau>) 
  then have 2: "M = (x' \<leftrightarrow> x) \<bullet> M'"
  by (metis Abs1_eq_iff'(3) Nominal2_Base.swap_self flip_commute flip_def permute_zero)
  from 1 have "((x' \<leftrightarrow> x) \<bullet> ((x', \<sigma>) # \<Gamma>)) \<turnstile> (x' \<leftrightarrow> x) \<bullet> M' : (x' \<leftrightarrow> x) \<bullet> \<tau>"
  by (rule_tac wt_terms.eqvt)
  with 2 fresh_type have 3: "((x' \<leftrightarrow> x) \<bullet> ((x', \<sigma>) # \<Gamma>)) \<turnstile> M : \<tau>" by (simp add: flip_fresh_fresh)

  have "(x' \<leftrightarrow> x) \<bullet> (x', \<sigma>) = (x, \<sigma>)" using fresh_type by (simp add: flip_fresh_fresh)
  then have "(x' \<leftrightarrow> x) \<bullet> ((x', \<sigma>) # \<Gamma>) = (x, \<sigma>) # ((x' \<leftrightarrow> x) \<bullet> \<Gamma>)" by simp

  with 3 have 4: "(x, \<sigma>) # ((x' \<leftrightarrow> x) \<bullet> \<Gamma>) \<turnstile> M : \<tau>" by simp
  with 4 1 have "(x, \<sigma>) # \<Gamma> \<turnstile> M : \<tau>" by (simp add: flip_fresh_fresh)
  with 1  show ?case by simp
qed


lemma subst_typ_aux: "(x, \<tau>) # \<Gamma> \<turnstile> Var y : \<sigma> \<Longrightarrow> x = y \<Longrightarrow> \<tau> = \<sigma>"
proof (rule ccontr, goal_cases)
case 1 
  then have "wf_ctxt ((y, \<tau>) # \<Gamma>)" by (simp add: wt_terms_impl_wf_ctxt)
  then have "atom y \<sharp> \<Gamma>" by (simp add: wf_ctxt_cons)
  then have "(y, \<sigma>) \<notin> set \<Gamma>" by (metis (mono_tags, lifting) fresh_Cons fresh_PairD(1) fresh_append fresh_at_base(2) split_list)
  with 1(3) have 2: "(y, \<sigma>) \<notin> set ((y, \<tau>) # \<Gamma>)" by simp
  from 1(1) have "(y, \<sigma>) \<in> set ((y, \<tau>) # \<Gamma>)" apply (cases rule:wt_terms.cases) by auto
  with 2 show ?case by simp
qed


lemma subst_typ:
  assumes "((x,\<tau>)#\<Gamma>) \<turnstile> M : \<sigma>" and "\<Gamma> \<turnstile> N : \<tau>"
  shows "\<Gamma> \<turnstile> M[x ::= N] : \<sigma>"
using assms proof (nominal_induct M avoiding: \<Gamma> x N arbitrary: \<sigma> rule: trm.strong_induct)
case (Var y)
  show ?case
  proof (cases "x = y")
  case True 
    show ?thesis 
    apply (simp add: True)
    using Var subst_typ_aux True by blast
  next
  case False
    from Var have 1: "wf_ctxt \<Gamma>" using wt_terms_impl_wf_ctxt wf_ctxt_cons by auto
    from Var have "(y,\<sigma>) \<in> set ((x, \<tau>) # \<Gamma>)" apply (cases rule:wt_terms.cases) by auto
    with False have 2: "(y,\<sigma>) \<in> set \<Gamma>" by simp

    show ?thesis
    apply (simp add: False)
    using Var
    apply (rule_tac wt_terms.var)
    using 1 2 by simp+
  qed
next
case (App M' N')
  from App(3) obtain \<pi> where  "(x, \<tau>) # \<Gamma> \<turnstile> M' : \<pi> \<rightarrow> \<sigma>" "(x, \<tau>) # \<Gamma> \<turnstile> N' : \<pi>" 
    by (cases rule:wt_terms.cases, simp)
  with App(1,2,4) have ih: "\<Gamma> \<turnstile> M'[x ::= N] : \<pi> \<rightarrow> \<sigma>" "\<Gamma> \<turnstile> N'[x ::= N] : \<pi>" by simp+
  show ?case
  unfolding subst.simps
  apply (rule wt_terms.app)
  using ih by simp+
next
case (Lam x' M)
  from Lam(5) obtain \<pi> \<delta> where 1: "\<sigma> = \<pi> \<rightarrow> \<delta>" "(x, \<tau>) # \<Gamma> \<turnstile> Lam [x']. M : \<pi> \<rightarrow> \<delta>" by (cases rule:wt_terms.cases, simp)
  from 1(2) have "(x', \<pi>) # (x, \<tau>) # \<Gamma> \<turnstile> M : \<delta>" apply (rule wt_terms_cases_2)
    using Lam(1,2) apply (simp add: fresh_Cons fresh_Pair fresh_type)
    by simp
  then have "(x, \<tau>) # (x', \<pi>) # \<Gamma> \<turnstile> M : \<delta>" by (rule exchange)

  with Lam(4,6) have ih: "(x', \<pi>) # \<Gamma> \<turnstile> M [x ::= N] : \<delta>"
    by (meson Lam.hyps(1) cons set_subset_Cons weakening wt_terms_impl_wf_ctxt)

  show ?case apply (subst subst.simps)
  using Lam apply simp
  unfolding 1(1)
  apply (rule wt_terms.abs)
  using Lam apply simp
  using ih by simp
next
case (Y \<gamma>)
  from Y(1) have 1: "\<sigma> = (\<gamma> \<rightarrow> \<gamma>) \<rightarrow> \<gamma>" by (cases rule:wt_terms.cases, simp)
  show ?case unfolding subst.simps 1
  apply (rule wt_terms.Y)
  using Y wt_terms_impl_wf_ctxt wf_ctxt_cons by simp
qed

lemma beta_Y_typ:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
  and "M \<Rightarrow> M'"
  shows "\<Gamma> \<turnstile> M' : \<sigma>"
using assms(2,1)
proof (nominal_induct  M M' avoiding: \<Gamma> arbitrary: \<sigma> rule: beta_Y.strong_induct)
case (red_L M M' N)
  from red_L(3) obtain \<tau> where 1: "\<Gamma> \<turnstile> M : \<tau> \<rightarrow> \<sigma>" "\<Gamma> \<turnstile> N : \<tau>"
    apply (cases rule:wt_terms.cases) by simp
  with red_L(2) have "\<Gamma> \<turnstile> M' : \<tau> \<rightarrow> \<sigma>" by simp
  thus ?case 
    apply (rule wt_terms.app)
    using 1 by simp
next
case (red_R N N' M)
  from red_R(3) obtain \<tau> where 1: "\<Gamma> \<turnstile> M : \<tau> \<rightarrow> \<sigma>" "\<Gamma> \<turnstile> N : \<tau>"
    apply (cases rule:wt_terms.cases) by simp
  with red_R(2) have 2: "\<Gamma> \<turnstile> N' : \<tau>" by simp
  show ?case 
    apply (rule wt_terms.app)
    using 1 2 by simp+
next
case (abs M M' x)
  from abs(4) obtain \<pi> \<tau> where 1: "\<sigma> = \<pi> \<rightarrow> \<tau>" "\<Gamma> \<turnstile> Lam [x]. M : \<pi> \<rightarrow> \<tau>"
    apply (cases rule:wt_terms.cases) using abs.prems by blast
  from 1(2) abs(1) have 2: "((x,\<pi>)#\<Gamma>) \<turnstile> M : \<tau>" by (rule wt_terms_cases_2, simp)
  with abs(3) have 3: "((x,\<pi>)#\<Gamma>) \<turnstile> M' : \<tau>" by simp
  
  show ?case
    apply (subst 1(1))
    apply (rule wt_terms.abs)
    using abs 2 3 by simp+
next
case (beta x N M) 
  from beta(3) obtain \<tau> where 1: "\<Gamma> \<turnstile> Lam [x]. M : \<tau> \<rightarrow> \<sigma>" "\<Gamma> \<turnstile> N : \<tau>" 
    apply (cases rule:wt_terms.cases) by simp
  from 1(1) beta(1) have 2: "((x,\<tau>)#\<Gamma>) \<turnstile> M : \<sigma>" by (rule wt_terms_cases_2, simp)
  show ?case
    apply (rule subst_typ)
    using 2 1(2) by simp+
next
case (Y \<tau> M)
  from Y obtain \<pi> where 1: "\<Gamma> \<turnstile> (Y \<tau>) : \<pi> \<rightarrow> \<sigma>" "\<Gamma> \<turnstile> M : \<pi>" 
    apply (cases rule:wt_terms.cases) by simp
  have "\<Gamma> \<turnstile> (Y \<tau>) : (\<tau> \<rightarrow> \<tau>) \<rightarrow> \<tau>" apply (rule wt_terms.Y)
    using wt_terms_impl_wf_ctxt Y by simp
  with 1(1) have "\<pi> \<rightarrow> \<sigma> = (\<tau> \<rightarrow> \<tau>) \<rightarrow> \<tau>" apply (cases rule:wt_terms.cases) by simp
  then have 2: "\<pi> = \<tau> \<rightarrow> \<tau>" "\<sigma> = \<tau>" by simp+
  show ?case
    apply (subst 2)
    apply (rule wt_terms.app)
    defer
    apply (rule wt_terms.app)
    apply (rule wt_terms.Y)
    using wt_terms_impl_wf_ctxt Y apply simp
    using 1(2) 2(1) by simp+
qed




subsection {* parallel beta reduction *}

inductive 
  pbeta :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<Rightarrow>\<parallel> _" [80,80] 80)
where
  refl[intro]: "(Var x) \<Rightarrow>\<parallel> (Var x)"
| reflY[intro]: "Y \<sigma> \<Rightarrow>\<parallel> Y \<sigma>"
| app[intro]: "\<lbrakk> M \<Rightarrow>\<parallel> M' ; N \<Rightarrow>\<parallel> N' \<rbrakk> \<Longrightarrow> App M N \<Rightarrow>\<parallel> App M' N'"
| abs[intro]: "\<lbrakk> M \<Rightarrow>\<parallel> M' \<rbrakk> \<Longrightarrow> Lam [x]. M \<Rightarrow>\<parallel> Lam [x]. M'"
| beta[intro]: "\<lbrakk> atom x \<sharp> N ; atom x \<sharp> N' ; M \<Rightarrow>\<parallel> M' ; N \<Rightarrow>\<parallel> N' \<rbrakk> \<Longrightarrow> App (Lam [x]. M) N \<Rightarrow>\<parallel> M'[x ::= N']"
| Y[intro]: "\<lbrakk> M \<Rightarrow>\<parallel> M' \<rbrakk> \<Longrightarrow> App (Y \<sigma>) M \<Rightarrow>\<parallel> App M' (App (Y \<sigma>) M')"

equivariance pbeta

nominal_inductive pbeta
 avoids beta: "x" | abs: "x"
  by (simp_all add: fresh_star_def fresh_Pair fresh_fact fresh_type)



nominal_function 
  not_abst :: "trm \<Rightarrow> bool"
where
  "not_abst (Var x) = True"
| "not_abst (App t1 t2) = True"
| "not_abst (Lam [x]. t) = False"
| "not_abst (Y t) = True"
apply (simp add: eqvt_def not_abst_graph_aux_def)
apply (rule TrueI)
apply (rule_tac y="x" in trm.exhaust)
using [[simproc del: alpha_lst]]
by auto
nominal_termination (eqvt) by lexicographic_order


nominal_function 
  not_Y :: "trm \<Rightarrow> bool"
where
  "not_Y (Var x) = True"
| "not_Y (App t1 t2) = True"
| "not_Y (Lam [x]. t) = True"
| "not_Y (Y t) = False"
apply (simp add: eqvt_def not_Y_graph_aux_def)
apply (rule TrueI)
apply (rule_tac y="x" in trm.exhaust)
using [[simproc del: alpha_lst]]
by auto
nominal_termination (eqvt) by lexicographic_order



subsection {* parallel beta reduction *}

inductive 
  pbeta_max :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ >>> _" [80,80] 80)
where
  refl[intro]: "(Var x) >>> (Var x)"
| reflY[intro]: "Y \<sigma> >>> Y \<sigma>"
| app[intro]: "\<lbrakk> not_abst M ; not_Y M ;  M >>> M' ; N >>> N' \<rbrakk> \<Longrightarrow> App M N >>> App M' N'"
| abs[intro]: "\<lbrakk> M >>> M' \<rbrakk> \<Longrightarrow> Lam [x]. M >>> Lam [x]. M'"
| beta[intro]: "\<lbrakk> atom x \<sharp> N ; atom x \<sharp> N' ; M >>> M' ; N >>> N' \<rbrakk> \<Longrightarrow> App (Lam [x]. M) N >>> M'[x ::= N']"
| Y[intro]: "\<lbrakk> M >>> M' \<rbrakk> \<Longrightarrow> App (Y \<sigma>) M >>> App M' (App (Y \<sigma>) M')"

equivariance pbeta_max

nominal_inductive pbeta_max
  avoids beta: "x" | abs: "x" (*don't understand what this does exactly or why we need it in the abs case ...*)
  by (simp_all add: fresh_star_def fresh_Pair fresh_fact fresh_type)




lemma Lem2_5_1:
  assumes "s \<Rightarrow>\<parallel> s'"
      and "t \<Rightarrow>\<parallel> t'"
      shows "(s[x ::= t]) \<Rightarrow>\<parallel> (s'[x ::= t'])"
using assms proof (nominal_induct s s' avoiding: x t t' rule:pbeta.strong_induct)
case (refl s)
  then show ?case by auto
next
case (reflY s)
  then show ?case by auto
next
case app
  show ?case 
  unfolding subst.simps
  apply (rule pbeta.app)
  using app
  by simp+
next
case (abs p p' y) 
  show ?case 
  apply (subst subst.simps)
  using abs apply simp
  apply (subst subst.simps)
  using abs apply simp
  apply (rule_tac pbeta.abs)
  using abs by simp
next
case (beta y q q' p p')
  have "App ((Lam [y]. p) [x ::= t]) (q [x ::= t]) \<Rightarrow>\<parallel> (p' [x ::= t'])[y ::= q'[x ::= t']]"
  apply (subst subst.simps(3))
  defer
  apply (rule_tac pbeta.beta)
  using beta by (simp add: fresh_fact)+

  then show ?case unfolding subst.simps
  apply (subst substitution_lemma) 
  using beta by (simp add: fresh_fact)+
next
case (Y M M' \<sigma>) 
  show ?case unfolding subst.simps
  apply (rule_tac pbeta.Y)
  using Y by simp
qed


lemma pbeta_refl[intro]: "s \<Rightarrow>\<parallel> s"
apply (induct s rule:trm.induct)
by auto

lemma not_Y_ex: "\<not>(not_Y M) \<Longrightarrow> \<exists>\<sigma>. M = Y \<sigma>"
apply (cases M rule:not_Y.cases)
by auto

lemma pbeta_max_ex:
  fixes a
  shows "\<exists>d. a >>> d"
apply (nominal_induct a rule:trm.strong_induct)
apply auto
apply (case_tac "not_abst trm1")
apply (case_tac "not_Y trm1")
apply auto[1]
proof goal_cases
case (1 trm1 trm2 d da)
  then obtain \<sigma> where 2: "trm1 = Y \<sigma>" using not_Y_ex by auto
  have "App (Y \<sigma>) trm2 >>> App da (App (Y \<sigma>) da)"
  apply (rule_tac pbeta_max.Y)
  by (rule 1(2))
  thus ?case unfolding 2 by auto
next
case (2 trm1 trm2 d da)
  thus ?case
  apply (nominal_induct trm1 d avoiding: da trm2 rule:pbeta_max.strong_induct)
  by auto
qed


lemma subst_rename: 
  assumes a: "atom y \<sharp> t"
  shows "t[x ::= s] = ((y \<leftrightarrow> x) \<bullet> t)[y ::= s]"
using a 
apply (nominal_induct t avoiding: x y s rule: trm.strong_induct)
apply (auto simp add: fresh_at_base)
by (simp add: flip_fresh_fresh fresh_type)



lemma fresh_in_pbeta: "s \<Rightarrow>\<parallel> s' \<Longrightarrow> atom (x::name) \<sharp> s \<Longrightarrow>  atom x \<sharp> s'"
apply (nominal_induct s s' rule:pbeta.strong_induct)
apply simp
apply simp
apply auto[1]
proof goal_cases
case 1 thus ?case by auto
next
case (2 xx N N' M M')
  then have "atom x \<sharp> N'" by simp
  { assume "x = xx" with 2 have ?case by (simp add: fresh_fact) }
  { assume "x \<noteq> xx" with 2 have ?case by (simp add: fresh_fact) }
  thus ?case using \<open>x = xx \<Longrightarrow> atom x \<sharp> M' [xx ::= N']\<close> by blast
next
case 3 thus ?case by simp
qed


(* adopting great naming conventions so early on! *)
lemma aaaaa2: "(Lam [x]. s) \<Rightarrow>\<parallel> s' \<Longrightarrow> \<exists>t. s' = Lam [x]. t \<and> s \<Rightarrow>\<parallel> t"
proof (cases "(Lam [x]. s)" s' rule:pbeta.cases, simp)
  case (goal1 _ _ x')
    then have 1: "s \<Rightarrow>\<parallel> ((x' \<leftrightarrow> x) \<bullet> M')" using pbeta.eqvt by (metis Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_commute flip_def permute_flip_cancel2 permute_plus)
    from goal1 have 2: "(x' \<leftrightarrow> x) \<bullet> s' = Lam [x]. ((x' \<leftrightarrow> x) \<bullet> M')" by simp
    from goal1 have "atom x \<sharp> (Lam [x']. M')"  using fresh_in_pbeta by (meson trm.fresh(3) list.set_intros(1))
    with 2 have "s' = Lam [x]. ((x' \<leftrightarrow> x) \<bullet> M')" unfolding goal1 by (metis "2" flip_fresh_fresh goal1(3) trm.fresh(3) list.set_intros(1))
    with 1 show ?case by auto
qed

thm pbeta.cases
lemma pbeta_cases_2:
  shows "atom x \<sharp> t \<Longrightarrow> App (Lam [x]. s) t \<Rightarrow>\<parallel> a2 \<Longrightarrow> 
    (\<And>s' t'. a2 = App (Lam [x]. s') t' \<Longrightarrow> atom x \<sharp> t' \<Longrightarrow> s \<Rightarrow>\<parallel> s' \<Longrightarrow> t \<Rightarrow>\<parallel> t' \<Longrightarrow> P) \<Longrightarrow>
    (\<And>t' s'. a2 = s' [x ::= t'] \<Longrightarrow> atom x \<sharp> t \<Longrightarrow> atom x \<sharp> t' \<Longrightarrow> s \<Rightarrow>\<parallel> s' \<Longrightarrow> t \<Rightarrow>\<parallel> t' \<Longrightarrow> P) \<Longrightarrow> P"
apply atomize_elim
proof (cases "App (Lam [x]. s) t" a2 rule:pbeta.cases, simp)
case goal1 
  then obtain s'' where 1: "M' = Lam [x]. s''" "s \<Rightarrow>\<parallel> s''" using aaaaa2 by blast
  thus ?case using goal1 fresh_in_pbeta  by auto
next
case (goal2 xx _ ss)
  have 1: "M' [xx ::= N'] = ((x \<leftrightarrow> xx) \<bullet> M') [x ::= N']"
    by (metis (no_types, lifting) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def fresh_in_pbeta goal2(3) goal2(7) permute_flip_cancel permute_plus subst_rename) 
  from goal2 have 2: "s \<Rightarrow>\<parallel> ((x \<leftrightarrow> xx) \<bullet> M')"
    by (metis Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def pbeta.eqvt permute_flip_cancel permute_plus)
  from goal2 have 3: "atom x \<sharp> N'" using fresh_in_pbeta by simp
  with goal2 1 2 show ?case by auto
qed


lemma pbeta_max_closes_pbeta:
  fixes a b d
  assumes "a >>> d"
  and "a \<Rightarrow>\<parallel> b"
  shows "b \<Rightarrow>\<parallel> d"
using assms proof (nominal_induct arbitrary: b rule:pbeta_max.strong_induct)
case (refl a)  
  show ?case using refl pbeta.cases by fastforce
next
case (reflY a) then have 1: "b = Y a" apply (cases rule: pbeta.cases) by simp
  show ?case unfolding 1 by auto
next
case (beta u ar ard al ald)
  from beta(1,7) show ?case
  apply (rule_tac pbeta_cases_2)
  apply (simp, simp)
  proof -
  case (goal2 arb alb)
    with beta have "alb \<Rightarrow>\<parallel> ald" "arb \<Rightarrow>\<parallel> ard" by simp+
    thus ?case unfolding goal2 apply (rule_tac Lem2_5_1) by simp+
  next
  case (goal1 alb arb)
    with beta have ih: "alb \<Rightarrow>\<parallel> ald" "arb \<Rightarrow>\<parallel> ard" by simp+
    show ?case unfolding goal1 
    apply (rule_tac pbeta.beta) using goal1 beta ih
    by simp_all
  qed
next
case (app al ald ar ard) 
  from app(7,1,2) show ?case
  apply (cases "App al ar" b rule:pbeta.cases)
  using app apply auto[1]
  apply simp
  by simp
next
case (abs al ald x) thus ?case using aaaaa2 by blast
next
case (Y M M' \<sigma>) 
  from Y(3) show ?case
  apply (cases rule:pbeta.cases)
  proof goal_cases
  case (1 M'' N'')
    from 1(2) have 2: "M'' = Y \<sigma>" by (cases rule:pbeta.cases, simp)
    show ?case unfolding 1 2
    apply (rule pbeta.Y)
    using 1 Y by simp
  next
  case (2 M'') show ?case unfolding 2
    apply (rule pbeta.app)
    using Y 2 apply simp
    apply (rule pbeta.app)
    apply (rule pbeta.reflY)
    using Y 2 by simp
  qed
qed

lemma Lem2_5_2: 
  assumes "a \<Rightarrow>\<parallel> b"
      and "a \<Rightarrow>\<parallel> c"
    shows "\<exists>d. b \<Rightarrow>\<parallel> d \<and> c \<Rightarrow>\<parallel> d"
proof -
  obtain d where 1: "a >>> d" using pbeta_max_ex by auto
  have "b \<Rightarrow>\<parallel> d \<and> c \<Rightarrow>\<parallel> d" 
  apply rule 
  apply (rule_tac pbeta_max_closes_pbeta)
  using 1 assms apply simp+
  apply (rule_tac pbeta_max_closes_pbeta)
  using 1 assms apply simp+
  done
  thus ?thesis by auto
qed



inductive close :: "(trm \<Rightarrow> trm \<Rightarrow> bool) \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool" ("_* _  _" [80,80] 80) for R::"trm \<Rightarrow> trm \<Rightarrow> bool"
where
  base[intro]: "R a b \<Longrightarrow> R* a b"
| refl[intro]: "R* a a"
| trans[intro]: "\<lbrakk> R* a b ; R* b c \<rbrakk> \<Longrightarrow> R* a c"



lemma beta_Y_c_typ:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
  and "beta_Y* M M'"
  shows "\<Gamma> \<turnstile> M' : \<sigma>"
using assms(2,1)
apply (induct M M' arbitrary: \<sigma> rule: close.induct)
using beta_Y_typ by auto



definition DP :: "(trm \<Rightarrow> trm \<Rightarrow> bool) \<Rightarrow> (trm \<Rightarrow> trm \<Rightarrow> bool) \<Rightarrow> bool" where
"DP R T = (\<forall>a b c. R a b \<and> T a c \<longrightarrow> (\<exists>d. T b d \<and> R c d))"

lemma DP_R_R_imp_DP_R_Rc_pbeta:
  assumes "DP pbeta pbeta"
    shows "DP pbeta (close pbeta)"
using assms unfolding DP_def
apply auto
proof -
case goal1 
  from goal1(3,2) show ?case
  apply (induct arbitrary: b rule:close.induct)
  using goal1(1) by blast+
qed

lemma DP_R_R_imp_DP_Rc_Rc_pbeta:
  assumes "DP pbeta pbeta"
    shows "DP (close pbeta) (close pbeta)"
using assms unfolding DP_def
apply auto
proof -
case goal1 
  from goal1(2,3) show ?case
  apply (induct arbitrary: c rule:close.induct)
  using DP_R_R_imp_DP_R_Rc_pbeta using DP_def assms apply fastforce
  apply auto
  by blast
qed



lemma M1': "M \<Rightarrow> M' \<Longrightarrow> M \<Rightarrow>\<parallel> M'"
apply (induct M M' rule:beta_Y.induct)
by auto

lemma M1: "beta_Y* M M' \<Longrightarrow> pbeta* M M'"
apply (induct M M' rule:close.induct)
apply auto
apply (rule base)
by (simp add: M1')


lemma red_r_close: "beta_Y* N N' \<Longrightarrow> beta_Y* (App M N) (App M N')"
apply (induct rule:close.induct)
by auto

lemma red_l_close: "beta_Y* M M' \<Longrightarrow> beta_Y* (App M N) (App M' N)"
apply (induct rule:close.induct)
by auto

lemma abs_close: "beta_Y* M M' \<Longrightarrow> beta_Y* (Lam [x]. M) (Lam [x]. M')"
apply (induct rule:close.induct)
by auto

lemma M2: "pbeta* M M' \<Longrightarrow> beta_Y* M M'"
proof (induct M M' rule:close.induct)
case refl show ?case by (rule close.refl)
next
case trans 
  show ?case apply (rule close.trans)
  using trans by simp+
next
case base thus ?case
  proof (induct rule:pbeta.induct)
  case refl show ?case by (rule close.refl)
  next
  case reflY show ?case by (rule close.refl)
  case (app M M' N N') 
    show ?case
    apply (rule_tac b="App M N'" in close.trans)
    using red_r_close app.hyps(4) apply auto[1]
    using red_l_close app.hyps(2) by auto[1]
  next
  case (abs M M' x)
    show ?case
    using abs abs_close by simp
  next
  case (beta x N N' M M')
    show ?case
    apply (rule_tac b="App (Lam [x]. M') N" in close.trans)
    apply (rule red_l_close)
    apply (rule abs_close)
    using beta apply simp
    apply (rule_tac b="App (Lam [x]. M') N'" in close.trans)
    apply (rule red_r_close)
    using beta apply simp
    apply (rule close.base)
    apply (rule beta_Y.beta)
    using beta by simp
  next
  case (Y M M' \<sigma>) 
    show ?case
    apply (rule_tac b="App M (App (Y \<sigma>) M)" in close.trans)
    apply (rule close.base)
    apply (rule beta_Y.Y)
    apply (rule_tac b="App M' (App (Y \<sigma>) M)" in close.trans)
    apply (rule red_l_close)
    using Y apply simp
    apply (rule red_r_close)
    apply (rule red_r_close)
    using Y by simp
  qed
qed

lemma church_rosser_typ:
  assumes "\<Gamma> \<turnstile> a : \<sigma>"
      and "beta_Y* a b"
      and "beta_Y* a c"
    shows "\<exists>d. beta_Y* b d \<and> beta_Y* c d \<and> \<Gamma> \<turnstile> d : \<sigma>"
proof -
  from assms have "pbeta* a b" "pbeta* a c" using M1 base by simp+
  then obtain d where "pbeta* b d" "pbeta* c d" by (metis DP_R_R_imp_DP_Rc_Rc_pbeta DP_def Lem2_5_2) 
  thus ?thesis using M2 beta_Y_c_typ assms by blast
qed

end

