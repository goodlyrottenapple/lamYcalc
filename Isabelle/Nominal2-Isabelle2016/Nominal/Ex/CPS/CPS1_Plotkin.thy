header {* CPS conversion *}
theory CPS1_Plotkin
imports Lt
begin

nominal_function
  CPS :: "lt \<Rightarrow> lt" ("_*" [250] 250)
where
  "atom k \<sharp> x \<Longrightarrow> (x~)* = (Lam k ((k~) $$ (x~)))"
| "atom k \<sharp> (x, M) \<Longrightarrow> (Lam x M)* = Lam k (k~ $$ Lam x (M*))"
| "atom k \<sharp> (M, N) \<Longrightarrow> atom m \<sharp> (N, k) \<Longrightarrow> atom n \<sharp> (k, m) \<Longrightarrow>
    (M $$ N)* = Lam k (M* $$ Lam m (N* $$ Lam n (m~ $$ n~ $$ k~)))"
unfolding eqvt_def CPS_graph_aux_def
apply (simp)
using [[simproc del: alpha_lst]]
apply (simp_all add: fresh_Pair_elim)
apply (rule_tac y="x" in lt.exhaust)
apply (auto)[3]
apply (rule_tac x="name" and ?'a="name" in obtain_fresh)
using [[simproc del: alpha_lst]]
apply (simp_all add: fresh_at_base)[3]
apply (rule_tac x="(lt1, lt2)" and ?'a="name" in obtain_fresh)
apply (rule_tac x="(lt2, a)" and ?'a="name" in obtain_fresh)
apply (rule_tac x="(a, aa)" and ?'a="name" in obtain_fresh)
apply (simp add: fresh_Pair_elim fresh_at_base)
apply (rule_tac x="(name, lt)" and ?'a="name" in obtain_fresh)
apply (simp add: fresh_Pair_elim fresh_at_base)[2]
apply (simp add: Abs1_eq_iff lt.fresh fresh_at_base)
--"-"
apply(rule_tac s="[[atom ka]]lst. ka~ $$ Lam x (CPS_sumC M)" in trans)
apply (case_tac "k = ka")
apply simp
thm Abs1_eq_iff
apply(subst Abs1_eq_iff)
apply(rule disjI2)
apply(rule conjI)
apply(simp)
apply(rule conjI)
apply (simp only: lt.perm_simps(1) lt.perm_simps(2) flip_def[symmetric] lt.eq_iff)
apply (subst  flip_at_base_simps(2))
apply(simp)
apply (intro conjI refl)
apply (rule flip_fresh_fresh[symmetric])
apply (simp_all add: lt.fresh)
apply (metis fresh_eqvt_at lt.fsupp)
apply (case_tac "ka = x")
apply simp_all[2]
apply (metis Abs_fresh_iff(3) atom_eq_iff finite_set fresh_Cons fresh_Nil fresh_atom fresh_eqvt_at fresh_finite_atom_set fresh_set lt.fsupp)
apply (metis Abs_fresh_iff(3) atom_eq_iff finite_set fresh_Cons fresh_Nil fresh_atom fresh_eqvt_at fresh_finite_atom_set fresh_set lt.fsupp)
--"-"
apply (simp add: Abs1_eq(3))
apply (erule Abs_lst1_fcb2)
apply (simp_all add: Abs_fresh_iff fresh_Nil fresh_star_def eqvt_at_def)[4]
--"-"
apply (rename_tac k' M N m' n')
apply (subgoal_tac "atom k \<sharp> CPS_sumC M \<and> atom k' \<sharp> CPS_sumC M \<and> atom k \<sharp> CPS_sumC N \<and> atom k' \<sharp> CPS_sumC N \<and>
                    atom m \<sharp> CPS_sumC N \<and> atom m' \<sharp> CPS_sumC N")
prefer 2
apply (intro conjI)
apply (erule fresh_eqvt_at, simp add: finite_supp, assumption)+
apply clarify
apply (case_tac "k = k'", case_tac [!] "m' = k",case_tac [!]"m = k'",case_tac[!] "m = m'")
apply (simp_all add: Abs1_eq_iff lt.fresh flip_def[symmetric] fresh_at_base flip_fresh_fresh permute_eq_iff)
by (metis flip_at_base_simps(3) flip_at_simps(2) flip_commute permute_flip_at)+

nominal_termination (eqvt) by lexicographic_order

lemmas [simp] = fresh_Pair_elim CPS.simps(2,3)[simplified fresh_Pair_elim]

lemma [simp]: "supp (M*) = supp M"
  by (induct rule: CPS.induct, simp_all add: lt.supp supp_at_base fresh_at_base fresh_def supp_Pair)
     (simp_all only: atom_eq_iff[symmetric], blast+)

lemma [simp]: "x \<sharp> M* = x \<sharp> M"
  unfolding fresh_def by simp

nominal_function
  convert:: "lt => lt" ("_+" [250] 250)
where
  "(Var x)+ = Var x"
| "(Lam x M)+ = Lam x (M*)"
| "(M $$ N)+ = M $$ N"
  unfolding convert_graph_aux_def eqvt_def
  apply (simp)
  apply(rule TrueI)
  apply (erule lt.exhaust)
  using [[simproc del: alpha_lst]]
  apply (simp_all)
  apply (simp add: Abs1_eq_iff CPS.eqvt)
  by blast

nominal_termination (eqvt)
  by (relation "measure size") (simp_all)

lemma convert_supp[simp]:
  shows "supp (M+) = supp M"
  by (induct M rule: lt.induct, simp_all add: lt.supp)

lemma convert_fresh[simp]:
  shows "x \<sharp> (M+) = x \<sharp> M"
  unfolding fresh_def by simp

lemma [simp]:
  shows "isValue (p \<bullet> (M::lt)) = isValue M"
  by (nominal_induct M rule: lt.strong_induct) auto

nominal_function
  Kapply :: "lt \<Rightarrow> lt \<Rightarrow> lt"       (infixl ";" 100)
where
  "Kapply (Lam x M) K = K $$ (Lam x M)+"
| "Kapply (Var x) K = K $$ Var x"
| "isValue M \<Longrightarrow> isValue N \<Longrightarrow> Kapply (M $$ N) K = M+ $$ N+ $$ K"
| "isValue M \<Longrightarrow> \<not>isValue N \<Longrightarrow> atom n \<sharp> M \<Longrightarrow> atom n \<sharp> K \<Longrightarrow>
    Kapply (M $$ N) K = N; (Lam n (M+ $$ Var n $$ K))"
| "\<not>isValue M \<Longrightarrow> atom m \<sharp> N \<Longrightarrow> atom m \<sharp> K \<Longrightarrow> atom n \<sharp> m \<Longrightarrow> atom n \<sharp> K \<Longrightarrow>
    Kapply (M $$ N) K = M; (Lam m (N*  $$ (Lam n (Var m $$ Var n $$ K))))"
  unfolding Kapply_graph_aux_def eqvt_def
  apply (simp)
using [[simproc del: alpha_lst]]
apply (simp_all)
apply (case_tac x)
apply (rule_tac y="a" in lt.exhaust)
apply (auto)
apply (case_tac "isValue lt1")
apply (case_tac "isValue lt2")
apply (auto)[1]
apply (rule_tac x="(lt1, ba)" and ?'a="name" in obtain_fresh)
apply (simp add: fresh_Pair_elim fresh_at_base)
apply (rule_tac x="(lt2, ba)" and ?'a="name" in obtain_fresh)
apply (rule_tac x="(a, ba)" and ?'a="name" in obtain_fresh)
apply (simp add: fresh_Pair_elim fresh_at_base)
apply (auto simp add: Abs1_eq_iff eqvts)[1]
apply (rename_tac M N u K)
apply (subgoal_tac "Lam n (M+ $$ n~ $$ K) =  Lam u (M+ $$ u~ $$ K)")
apply (simp only:)
apply (auto simp add: Abs1_eq_iff flip_fresh_fresh fresh_at_base)[1]
apply (subgoal_tac "Lam m (Na* $$ Lam n (m~ $$ n~ $$ Ka)) = Lam ma (Na* $$ Lam na (ma~ $$ na~ $$ Ka))")
apply (simp only:)
apply (simp add: Abs1_eq_iff flip_fresh_fresh fresh_at_base)
apply (case_tac "m = ma")
apply simp_all
apply (case_tac "m = na")
apply(simp_all add: flip_fresh_fresh)
done

nominal_termination (eqvt)
  by (relation "measure (\<lambda>(t, _). size t)") (simp_all)

section{* lemma related to Kapply *}

lemma [simp]: "isValue V \<Longrightarrow> V; K = K $$ (V+)"
  by (nominal_induct V rule: lt.strong_induct) auto

section{* lemma related to CPS conversion *}

lemma value_CPS:
  assumes "isValue V"
  and "atom a \<sharp> V"
  shows "V* = Lam a (a~ $$ V+)"
  using assms
proof (nominal_induct V avoiding: a rule: lt.strong_induct, simp_all add: lt.fresh)
  fix name :: name and lt aa
  assume a: "atom name \<sharp> aa" "\<And>b. \<lbrakk>isValue lt; atom b \<sharp> lt\<rbrakk> \<Longrightarrow> lt* = Lam b (b~ $$ lt+)"
    "atom aa \<sharp> lt \<or> aa = name"
  obtain ab :: name where b: "atom ab \<sharp> (name, lt, a)" using obtain_fresh by blast
  show "Lam name lt* = Lam aa (aa~ $$ Lam name (lt*))" using a b
    by (simp add: Abs1_eq_iff fresh_at_base lt.fresh)
qed

section{* first lemma CPS subst *}

lemma CPS_subst_fv:
  assumes *:"isValue V"
  shows "((M[x ::= V])* = (M*)[x ::= V+])"
using * proof (nominal_induct M avoiding: V x rule: lt.strong_induct)
  case (Var name)
  assume *: "isValue V"
  obtain a :: name where a: "atom a \<sharp> (x, name, V)" using obtain_fresh by blast
  show "((name~)[x ::= V])* = (name~)*[x ::= V+]" using a
    by (simp add: fresh_at_base * value_CPS)
next
  case (Lam name lt V x)
  assume *: "atom name \<sharp> V" "atom name \<sharp> x" "\<And>b ba. isValue b \<Longrightarrow> (lt[ba ::= b])* = lt*[ba ::= b+]"
    "isValue V"
  obtain a :: name where a: "atom a \<sharp> (name, lt, lt[x ::= V], x, V)" using obtain_fresh by blast
  show "(Lam name lt[x ::= V])* = Lam name lt*[x ::= V+]" using * a
    by (simp add: fresh_at_base)
next
  case (App lt1 lt2 V x)
  assume *: "\<And>b ba. isValue b \<Longrightarrow> (lt1[ba ::= b])* = lt1*[ba ::= b+]" "\<And>b ba. isValue b \<Longrightarrow> (lt2[ba ::= b])* = lt2*[ba ::= b+]"
    "isValue V"
  obtain a :: name where a: "atom a \<sharp> (lt1[x ::= V], lt1, lt2[x ::= V], lt2, V, x)" using obtain_fresh by blast
  obtain b :: name where b: "atom b \<sharp> (lt2[x ::= V], lt2, a, V, x)" using obtain_fresh by blast
  obtain c :: name where c: "atom c \<sharp> (a, b, V, x)" using obtain_fresh by blast
  show "((lt1 $$ lt2)[x ::= V])* = (lt1 $$ lt2)*[x ::= V+]" using * a b c
    by (simp add: fresh_at_base)
qed

lemma [simp]: "isValue V \<Longrightarrow> isValue (V+)"
  by (nominal_induct V rule: lt.strong_induct, auto)

lemma CPS_eval_Kapply:
  assumes a: "isValue K"
  shows "(M* $$ K) \<longrightarrow>\<^isub>\<beta>\<^sup>* (M ; K)"
  using a
proof (nominal_induct M avoiding: K rule: lt.strong_induct, simp_all)
  case (Var name K)
  assume *: "isValue K"
  obtain a :: name where a: "atom a \<sharp> (name, K)" using obtain_fresh by blast
  show "(name~)* $$ K \<longrightarrow>\<^isub>\<beta>\<^sup>* K $$ name~" using * a
    by simp (rule evbeta', simp_all add: fresh_at_base)
next
  fix name :: name and lt K
  assume *: "atom name \<sharp> K" "\<And>b. isValue b \<Longrightarrow> lt* $$ b \<longrightarrow>\<^isub>\<beta>\<^sup>* lt ; b" "isValue K"
  obtain a :: name where a: "atom a \<sharp> (name, K, lt)" using obtain_fresh by blast
  then have b: "atom name \<sharp> a" using fresh_PairD(1) fresh_at_base atom_eq_iff by metis
  show "Lam name lt* $$ K \<longrightarrow>\<^isub>\<beta>\<^sup>* K $$ Lam name (lt*)" using * a b
    by simp (rule evbeta', simp_all)
next
  fix lt1 lt2 K
  assume *: "\<And>b. isValue b \<Longrightarrow>  lt1* $$ b \<longrightarrow>\<^isub>\<beta>\<^sup>* lt1 ; b" "\<And>b. isValue b \<Longrightarrow>  lt2* $$ b \<longrightarrow>\<^isub>\<beta>\<^sup>* lt2 ; b" "isValue K"
  obtain a :: name where a: "atom a \<sharp> (lt1, lt2, K)" using obtain_fresh by blast
  obtain b :: name where b: "atom b \<sharp> (lt1, lt2, K, a)" using obtain_fresh by blast
  obtain c :: name where c: "atom c \<sharp> (lt1, lt2, K, a, b)" using obtain_fresh by blast
  have d: "atom a \<sharp> lt1" "atom a \<sharp> lt2" "atom a \<sharp> K" "atom b \<sharp> lt1" "atom b \<sharp> lt2" "atom b \<sharp> K" "atom b \<sharp> a"
    "atom c \<sharp> lt1" "atom c \<sharp> lt2" "atom c \<sharp> K" "atom c \<sharp> a" "atom c \<sharp> b" using fresh_Pair a b c by simp_all
  have "(lt1 $$ lt2)* $$ K \<longrightarrow>\<^isub>\<beta>\<^sup>* lt1* $$ Lam b (lt2* $$ Lam c (b~ $$ c~ $$ K))" using * d
    by (simp add: fresh_at_base) (rule evbeta', simp_all add: fresh_at_base)
  also have "... \<longrightarrow>\<^isub>\<beta>\<^sup>* lt1 $$ lt2 ; K" proof (cases "isValue lt1")
    assume e: "isValue lt1"
    have "lt1* $$ Lam b (lt2* $$ Lam c (b~ $$ c~ $$ K)) \<longrightarrow>\<^isub>\<beta>\<^sup>* Lam b (lt2* $$ Lam c (b~ $$ c~ $$ K)) $$ lt1+"
      using * d e by simp
    also have "... \<longrightarrow>\<^isub>\<beta>\<^sup>* lt2* $$ Lam c (lt1+ $$ c~ $$ K)"
      by (rule evbeta')(simp_all add: * d e)
    also have "... \<longrightarrow>\<^isub>\<beta>\<^sup>* lt1 $$ lt2 ; K" proof (cases "isValue lt2")
      assume f: "isValue lt2"
      have "lt2* $$ Lam c (lt1+ $$ c~ $$ K) \<longrightarrow>\<^isub>\<beta>\<^sup>* Lam c (lt1+ $$ c~ $$ K) $$ lt2+" using * d e f by simp
      also have "... \<longrightarrow>\<^isub>\<beta>\<^sup>* lt1+ $$ lt2+ $$ K"
        by (rule evbeta', simp_all add: d e f)
      finally show ?thesis using * d e f by simp
    next
      assume f: "\<not> isValue lt2"
      have "lt2* $$ Lam c (lt1+ $$ c~ $$ K) \<longrightarrow>\<^isub>\<beta>\<^sup>* lt2 ; Lam c (lt1+ $$ c~ $$ K)" using * d e f by simp
      also have "... \<longrightarrow>\<^isub>\<beta>\<^sup>* lt2 ; Lam a (lt1+ $$ a~ $$ K)" using Kapply.simps(4) d e evs1 f by metis
      finally show ?thesis using * d e f by simp
    qed
    finally show ?thesis .
  qed (metis Kapply.simps(5) isValue.simps(2) * d)
  finally show "(lt1 $$ lt2)* $$ K \<longrightarrow>\<^isub>\<beta>\<^sup>* lt1 $$ lt2 ; K" .
qed

lemma Kapply_eval:
  assumes a: "M \<longrightarrow>\<^isub>\<beta> N" "isValue K"
  shows "(M; K) \<longrightarrow>\<^isub>\<beta>\<^sup>*  (N; K)"
  using assms
proof (induct arbitrary: K rule: eval.induct)
  case (evbeta x V M)
  fix K
  assume a: "isValue K" "isValue V" "atom x \<sharp> V"
  have "Lam x (M*) $$ V+ $$ K \<longrightarrow>\<^isub>\<beta>\<^sup>* (((M*)[x ::= V+]) $$ K)"
    by (rule evs2,rule ev2,rule Lt.evbeta) (simp_all add: fresh_def a[simplified fresh_def] evs1)
  also have "... = ((M[x ::= V])* $$ K)" by (simp add: CPS_subst_fv a)
  also have "... \<longrightarrow>\<^isub>\<beta>\<^sup>* ((M[x ::= V]) ; K)" by (rule CPS_eval_Kapply, simp_all add: a)
  finally show "(Lam x M $$ V ; K) \<longrightarrow>\<^isub>\<beta>\<^sup>*  ((M[x ::= V]) ; K)" using a by simp
next
  case (ev1 V M N)
  fix V M N K
  assume a: "isValue V" "M \<longrightarrow>\<^isub>\<beta> N" "\<And>K. isValue K \<Longrightarrow> M ; K \<longrightarrow>\<^isub>\<beta>\<^sup>* N ; K" "isValue K"
  obtain a :: name where b: "atom a \<sharp> (V, K, M, N)" using obtain_fresh by blast
  show "V $$ M ; K \<longrightarrow>\<^isub>\<beta>\<^sup>* V $$ N ; K" proof (cases "isValue N")
    assume "\<not> isValue N"
    then show "V $$ M ; K \<longrightarrow>\<^isub>\<beta>\<^sup>* V $$ N ; K" using a b by simp
  next
    assume n: "isValue N"
    have c: "M; Lam a (V+ $$ a~ $$ K) \<longrightarrow>\<^isub>\<beta>\<^sup>* Lam a (V+ $$ a~ $$ K) $$ N+" using a b by (simp add: n)
    also have d: "... \<longrightarrow>\<^isub>\<beta>\<^sup>* V+ $$ N+ $$ K" by (rule evbeta') (simp_all add: a b n)
    finally show "V $$ M ; K \<longrightarrow>\<^isub>\<beta>\<^sup>* V $$ N ; K" using a b by (simp add: n)
  qed
next
  case (ev2 M M' N)
  assume *: "M \<longrightarrow>\<^isub>\<beta> M'" "\<And>K. isValue K \<Longrightarrow>  M ; K \<longrightarrow>\<^isub>\<beta>\<^sup>* M' ; K" "isValue K"
  obtain a :: name where a: "atom a \<sharp> (K, M, N, M')" using obtain_fresh by blast
  obtain b :: name where b: "atom b \<sharp> (a, K, M, N, M', N+)" using obtain_fresh by blast
  have d: "atom a \<sharp> K" "atom a \<sharp> M" "atom a \<sharp> N" "atom a \<sharp> M'" "atom b \<sharp> a" "atom b \<sharp> K"
    "atom b \<sharp> M" "atom b \<sharp> N" "atom b \<sharp> M'" using a b fresh_Pair by simp_all
  have "M $$ N ; K  \<longrightarrow>\<^isub>\<beta>\<^sup>* M' ; Lam a (N* $$ Lam b (a~ $$ b~ $$ K))" using * d by simp
  also have "... \<longrightarrow>\<^isub>\<beta>\<^sup>* M' $$ N ; K" proof (cases "isValue M'")
    assume "\<not> isValue M'"
    then show ?thesis using * d by (simp_all add: evs1)
  next
    assume e: "isValue M'"
    then have "M' ; Lam a (N* $$ Lam b (a~ $$ b~ $$ K)) = Lam a (N* $$ Lam b (a~ $$ b~ $$ K)) $$ M'+" by simp
    also have "... \<longrightarrow>\<^isub>\<beta>\<^sup>* (N* $$ Lam b (a~ $$ b~ $$ K))[a ::= M'+]"
      by (rule evbeta') (simp_all add: fresh_at_base e d)
    also have "... = N* $$ Lam b (M'+ $$ b~ $$ K)" using * d by (simp add: fresh_at_base)
    also have "... \<longrightarrow>\<^isub>\<beta>\<^sup>* M' $$ N ; K" proof (cases "isValue N")
      assume f: "isValue N"
      have "N* $$ Lam b (M'+ $$ b~ $$ K) \<longrightarrow>\<^isub>\<beta>\<^sup>* Lam b (M'+ $$ b~ $$ K) $$ N+"
        by (rule eval_trans, rule CPS_eval_Kapply) (simp_all add: d e f * evs1)
      also have "... \<longrightarrow>\<^isub>\<beta>\<^sup>* M' $$ N ; K" by (rule evbeta') (simp_all add: d e f evs1)
      finally show ?thesis .
    next
      assume "\<not> isValue N"
      then show ?thesis using d e
        by (metis CPS_eval_Kapply Kapply.simps(4) isValue.simps(2))
    qed
    finally show ?thesis .
  qed
  finally show ?case .
qed

lemma Kapply_eval_rtrancl:
  assumes H: "M \<longrightarrow>\<^isub>\<beta>\<^sup>*  N" and "isValue K"
  shows "(M;K) \<longrightarrow>\<^isub>\<beta>\<^sup>* (N;K)"
  using H
  by (induct) (metis Kapply_eval assms(2) eval_trans evs1)+

lemma
  assumes "isValue V" "M \<longrightarrow>\<^isub>\<beta>\<^sup>* V"
  shows "M* $$ (Lam x (x~)) \<longrightarrow>\<^isub>\<beta>\<^sup>* V+"
proof-
  obtain y::name where *: "atom y \<sharp> V" using obtain_fresh by blast
  have e: "Lam x (x~) = Lam y (y~)"
    by (simp add: Abs1_eq_iff lt.fresh fresh_at_base)
  have "M* $$ Lam x (x~) \<longrightarrow>\<^isub>\<beta>\<^sup>* M ; Lam x (x~)"
    by(rule CPS_eval_Kapply,simp_all add: assms)
  also have "... \<longrightarrow>\<^isub>\<beta>\<^sup>* (V ; Lam x (x~))" by (rule Kapply_eval_rtrancl, simp_all add: assms)
  also have "... = V ; Lam y (y~)" using e by (simp only:)
  also have "... \<longrightarrow>\<^isub>\<beta>\<^sup>* (V+)" by (simp add: assms, rule evbeta') (simp_all add: assms *)
  finally show "M* $$ (Lam x (x~)) \<longrightarrow>\<^isub>\<beta>\<^sup>* (V+)" .
qed

end



