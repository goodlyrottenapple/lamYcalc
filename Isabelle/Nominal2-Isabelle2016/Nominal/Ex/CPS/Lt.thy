header {* The Call-by-Value Lambda Calculus *}
theory Lt
imports "../../Nominal2"
begin

atom_decl name

nominal_datatype lt =
    Var name       ("_~"  [150] 149)
  | App lt lt         (infixl "$$" 100)
  | Lam x::"name" t::"lt"  binds  x in t

nominal_function
  subst :: "lt \<Rightarrow> name \<Rightarrow> lt \<Rightarrow> lt"  ("_ [_ ::= _]" [90, 90, 90] 90)
where
  "(Var x)[y ::= s] = (if x = y then s else (Var x))"
| "(App t1 t2)[y ::= s] = App (t1[y ::= s]) (t2[y ::= s])"
| "atom x \<sharp> (y, s) \<Longrightarrow> (Lam x t)[y ::= s] = Lam x (t[y ::= s])"
  unfolding eqvt_def subst_graph_aux_def
  apply (simp)
  apply(rule TrueI)
  using [[simproc del: alpha_lst]]
  apply(auto simp add: lt.distinct lt.eq_iff)
  apply(rule_tac y="a" and c="(aa, b)" in lt.strong_exhaust)
  apply blast
  apply(simp_all add: fresh_star_def fresh_Pair_elim)
  apply (erule_tac c="(ya,sa)" in Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: perm_supp_eq fresh_star_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: perm_supp_eq fresh_star_Pair)
done

nominal_termination (eqvt) by lexicographic_order

lemma forget[simp]:
  shows "atom x \<sharp> M \<Longrightarrow> M[x ::= s] = M"
  by (nominal_induct M avoiding: x s rule: lt.strong_induct)
     (auto simp add: lt.fresh fresh_at_base)

lemma [simp]: "supp (M[x ::= V]) <= (supp(M) - {atom x}) Un (supp V)"
  by (nominal_induct M avoiding: x V rule: lt.strong_induct)
     (auto simp add: lt.supp supp_at_base, blast, blast)

nominal_function
  isValue:: "lt => bool"
where
  "isValue (Var x) = True"
| "isValue (Lam y N) = True"
| "isValue (A $$ B) = False"
  unfolding eqvt_def isValue_graph_aux_def
  by (auto)
     (erule lt.exhaust, auto)

nominal_termination (eqvt)
  by (relation "measure size") (simp_all)

inductive
  eval :: "[lt, lt] \<Rightarrow> bool" (" _ \<longrightarrow>\<^isub>\<beta> _" [80,80] 80)
  where
   evbeta: "\<lbrakk>atom x \<sharp> V; isValue V\<rbrakk> \<Longrightarrow> ((Lam x M) $$ V) \<longrightarrow>\<^isub>\<beta> (M[x ::= V])"
|  ev1: "\<lbrakk>isValue V; M \<longrightarrow>\<^isub>\<beta> M' \<rbrakk> \<Longrightarrow> (V $$ M) \<longrightarrow>\<^isub>\<beta> (V $$ M')"
|  ev2: "M \<longrightarrow>\<^isub>\<beta> M' \<Longrightarrow> (M $$ N) \<longrightarrow>\<^isub>\<beta> (M' $$ N)"

equivariance eval

nominal_inductive eval
done

(*lemmas [simp] = lt.supp(2)*)

lemma closedev1: assumes "s \<longrightarrow>\<^isub>\<beta> t"
  shows "supp t <= supp s"
  using assms
    by (induct, auto simp add: lt.supp)


lemma [simp]: "~ ((Lam x M) \<longrightarrow>\<^isub>\<beta> N)"
by (rule, erule eval.cases, simp_all)

lemma [simp]: assumes "M \<longrightarrow>\<^isub>\<beta> N" shows "~ isValue M"
using assms
by (cases, auto)


inductive
  eval_star :: "[lt, lt] \<Rightarrow> bool" (" _ \<longrightarrow>\<^isub>\<beta>\<^sup>* _" [80,80] 80)
  where
   evs1: "M \<longrightarrow>\<^isub>\<beta>\<^sup>* M"
|  evs2: "\<lbrakk>M \<longrightarrow>\<^isub>\<beta> M'; M' \<longrightarrow>\<^isub>\<beta>\<^sup>*  M'' \<rbrakk> \<Longrightarrow> M \<longrightarrow>\<^isub>\<beta>\<^sup>*  M''"

lemma eval_evs: assumes *: "M \<longrightarrow>\<^isub>\<beta> M'" shows "M \<longrightarrow>\<^isub>\<beta>\<^sup>* M'"
by (rule evs2, rule *, rule evs1)

lemma eval_trans[trans]:
  assumes "M1  \<longrightarrow>\<^isub>\<beta>\<^sup>* M2"
      and "M2  \<longrightarrow>\<^isub>\<beta>\<^sup>*  M3"
  shows "M1  \<longrightarrow>\<^isub>\<beta>\<^sup>* M3"
  using assms
  by (induct, auto intro: evs2)

lemma evs3[rule_format]: assumes "M1  \<longrightarrow>\<^isub>\<beta>\<^sup>* M2"
  shows "M2  \<longrightarrow>\<^isub>\<beta> M3 \<longrightarrow> M1  \<longrightarrow>\<^isub>\<beta>\<^sup>* M3"
  using assms
    by (induct, auto intro: eval_evs evs2)

equivariance eval_star

lemma evbeta':
  fixes x :: name
  assumes "isValue V" and "atom x\<sharp>V" and "N = (M[x ::= V])"
  shows "((Lam x M) $$ V) \<longrightarrow>\<^isub>\<beta>\<^sup>* N"
  using assms by simp (rule evs2, rule evbeta, simp_all add: evs1)

end



