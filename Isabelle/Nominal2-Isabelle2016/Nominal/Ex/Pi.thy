(* Theory be Kirstin Peters *)

theory Pi
  imports "../Nominal2"
begin

atom_decl name

subsection {* Capture-Avoiding Substitution of Names *}

definition
  subst_name :: "name \<Rightarrow> name \<Rightarrow> name \<Rightarrow> name" ("_[_:::=_]" [110, 110, 110] 110)
where
  "a[b:::=c] \<equiv> if (a = b) then c else a"

declare subst_name_def[simp]

lemma subst_name_mix_eqvt[eqvt]:
  fixes p :: perm
  and   a :: name
  and   b :: name
  and   c :: name

  shows "p \<bullet> (a[b:::=c]) = (p \<bullet> a)[(p \<bullet> b):::=(p \<bullet> c)]"
proof -
  show ?thesis
    by(auto)
qed

nominal_function
  subst_name_list :: "name \<Rightarrow> (name \<times> name) list \<Rightarrow> name"
where
  "subst_name_list a [] = a"
| "subst_name_list a ((b, c)#xs) = (if (a = b) then c else (subst_name_list a xs))"
  apply(simp add: eqvt_def subst_name_list_graph_aux_def)
  apply(simp)
  apply(auto)
  apply(rule_tac y="b" in list.exhaust)
  by(auto)

nominal_termination (eqvt)
  by (lexicographic_order)


section {* The Synchronous Pi-Calculus *}

subsection {* Syntax: Synchronous, Monadic Pi-Calculus with n-ary, Mixed Choice *}

nominal_datatype
      guardedTerm_mix = Output name name piMix                     ("_!<_>\<onesuperior>._" [120, 120, 110] 110)
                      | Input name b::name P::piMix  binds b in P  ("_?<_>\<onesuperior>._" [120, 120, 110] 110)
                      | Tau piMix                                  ("<\<tau>\<onesuperior>>._" [110] 110)
  and sumList_mix     = SumNil                                     ("\<zero>\<onesuperior>")
                      | AddSummand guardedTerm_mix sumList_mix     (infixr "\<oplus>\<onesuperior>" 65)
  and piMix           = Res a::name P::piMix         binds a in P  ("<\<nu>_>\<onesuperior>_" [100, 100] 100)
                      | Par piMix piMix                            (infixr "\<parallel>\<onesuperior>" 85)
                      | Match name name piMix                      ("[_\<frown>\<onesuperior>_]_" [120, 120, 110] 110)
                      | Sum sumList_mix                            ("\<oplus>\<onesuperior>{_}" 90)
                      | Rep name b::name P::piMix    binds b in P  ("\<infinity>_?<_>\<onesuperior>._" [120, 120, 110] 110)
                      | Succ                                       ("succ\<onesuperior>")

lemmas piMix_strong_induct  = guardedTerm_mix_sumList_mix_piMix.strong_induct
lemmas piMix_fresh          = guardedTerm_mix_sumList_mix_piMix.fresh
lemmas piMix_eq_iff         = guardedTerm_mix_sumList_mix_piMix.eq_iff
lemmas piMix_distinct       = guardedTerm_mix_sumList_mix_piMix.distinct
lemmas piMix_size           = guardedTerm_mix_sumList_mix_piMix.size

subsection {* Alpha-Conversion Lemmata *}

lemma alphaRes_mix:
  fixes a :: name
  and   P :: piMix
  and   z :: name

  assumes "atom z \<sharp> P"

  shows "<\<nu>a>\<onesuperior>P = <\<nu>z>\<onesuperior>((atom a \<rightleftharpoons> atom z) \<bullet> P)"
proof(cases "a = z")
  assume "a = z"
  thus ?thesis
    by(simp)
next
  assume "a \<noteq> z"
  thus ?thesis
    using assms
    by (simp add: flip_def piMix_eq_iff Abs1_eq_iff fresh_permute_left)
qed

lemma alphaInput_mix:
  fixes a :: name
  and   b :: name
  and   P :: piMix
  and   z :: name

  assumes "atom z \<sharp> P"

  shows "a?<b>\<onesuperior>.P = a?<z>\<onesuperior>.((atom b \<rightleftharpoons> atom z) \<bullet> P)"
proof(cases "b = z")
  assume "b = z"
  thus ?thesis
    by(simp)
next
  assume "b \<noteq> z"
  thus ?thesis
    using assms
    by(simp add: flip_def piMix_eq_iff Abs1_eq_iff fresh_permute_left)
qed

lemma alphaRep_mix:
  fixes a :: name
  and   b :: name
  and   P :: piMix
  and   z :: name

  assumes "atom z \<sharp> P"

  shows "\<infinity>a?<b>\<onesuperior>.P = \<infinity>a?<z>\<onesuperior>.((atom b \<rightleftharpoons> atom z) \<bullet> P)"
proof(cases "b = z")
  assume "b = z"
  thus ?thesis
    by(simp)
next
  assume "b \<noteq> z"
  thus ?thesis
    using assms
    by(simp add: flip_def piMix_eq_iff Abs1_eq_iff fresh_permute_left)
qed

subsection {* Capture-Avoiding Substitution of Names *}

lemma testl:
  assumes a: "\<exists>y. f = Inl y"
  shows "(p \<bullet> (Sum_Type.projl f)) = Sum_Type.projl (p \<bullet> f)"
using a by auto

lemma testrr:
  assumes a: "\<exists>y. f = Inr (Inr y)"
  shows "(p \<bullet> (Sum_Type.projr (Sum_Type.projr f))) = Sum_Type.projr (Sum_Type.projr (p \<bullet> f))"
using a by auto

lemma testlr:
  assumes a: "\<exists>y. f = Inr (Inl y)"
  shows "(p \<bullet> (Sum_Type.projl (Sum_Type.projr f))) = Sum_Type.projl (Sum_Type.projr (p \<bullet> f))"
using a by auto

nominal_function (default "case_sum (\<lambda>x. Inl undefined) (case_sum (\<lambda>x. Inr (Inl undefined)) (\<lambda>x. Inr (Inr undefined)))")
  subsGuard_mix :: "guardedTerm_mix \<Rightarrow> name \<Rightarrow> name \<Rightarrow> guardedTerm_mix"  ("_[_::=\<onesuperior>\<onesuperior>_]" [100, 100, 100] 100) and
  subsList_mix  :: "sumList_mix \<Rightarrow> name \<Rightarrow> name \<Rightarrow> sumList_mix"          ("_[_::=\<onesuperior>\<twosuperior>_]" [100, 100, 100] 100) and
  subs_mix      :: "piMix \<Rightarrow> name \<Rightarrow> name \<Rightarrow> piMix"                      ("_[_::=\<onesuperior>_]" [100, 100, 100] 100)
where
  "(a!<b>\<onesuperior>.P)[x::=\<onesuperior>\<onesuperior>y] = (a[x:::=y])!<(b[x:::=y])>\<onesuperior>.(P[x::=\<onesuperior>y])"
| "\<lbrakk>atom b \<sharp> (x, y)\<rbrakk> \<Longrightarrow> (a?<b>\<onesuperior>.P)[x::=\<onesuperior>\<onesuperior>y] = (a[x:::=y])?<b>\<onesuperior>.(P[x::=\<onesuperior>y])"
| "(<\<tau>\<onesuperior>>.P)[x::=\<onesuperior>\<onesuperior>y] = <\<tau>\<onesuperior>>.(P[x::=\<onesuperior>y])"
| "(\<zero>\<onesuperior>)[x::=\<onesuperior>\<twosuperior>y] = \<zero>\<onesuperior>"
| "(g \<oplus>\<onesuperior> xg)[x::=\<onesuperior>\<twosuperior>y] = (g[x::=\<onesuperior>\<onesuperior>y]) \<oplus>\<onesuperior> (xg[x::=\<onesuperior>\<twosuperior>y])"
| "\<lbrakk>atom a \<sharp> (x, y)\<rbrakk> \<Longrightarrow> (<\<nu>a>\<onesuperior>P)[x::=\<onesuperior>y] = <\<nu>a>\<onesuperior>(P[x::=\<onesuperior>y])"
| "(P \<parallel>\<onesuperior> Q)[x::=\<onesuperior>y] = (P[x::=\<onesuperior>y]) \<parallel>\<onesuperior> (Q[x::=\<onesuperior>y])"
| "([a\<frown>\<onesuperior>b]P)[x::=\<onesuperior>y] = ([(a[x:::=y])\<frown>\<onesuperior>(b[x:::=y])](P[x::=\<onesuperior>y]))"
| "(\<oplus>\<onesuperior>{xg})[x::=\<onesuperior>y] = \<oplus>\<onesuperior>{(xg[x::=\<onesuperior>\<twosuperior>y])}"
| "\<lbrakk>atom b \<sharp> (x, y)\<rbrakk> \<Longrightarrow> (\<infinity>a?<b>\<onesuperior>.P)[x::=\<onesuperior>y] = \<infinity>(a[x:::=y])?<b>\<onesuperior>.(P[x::=\<onesuperior>y])"
| "(succ\<onesuperior>)[x::=\<onesuperior>y] = succ\<onesuperior>"
  using [[simproc del: alpha_lst]]
  apply(auto simp add: piMix_distinct piMix_eq_iff)
  apply(simp add: eqvt_def  subsGuard_mix_subsList_mix_subs_mix_graph_aux_def)
  --"Covered all cases"
  apply(case_tac x)
  apply(simp)
  apply(case_tac a)
  apply(simp)
  apply (rule_tac y="aa" and c="(b, c)" in guardedTerm_mix_sumList_mix_piMix.strong_exhaust(1))
  apply(blast)
  apply(auto simp add: fresh_star_def)[1]
  apply(blast)
  apply(simp)
  apply(case_tac b)
  apply(simp)
  apply(case_tac a)
  apply(simp)
  apply (rule_tac ya="aa" in guardedTerm_mix_sumList_mix_piMix.strong_exhaust(2))
  apply(blast)
  apply(blast)
  apply(simp)
  apply(case_tac ba)
  apply(simp)
  apply (rule_tac yb="a" and c="(bb,c)" in guardedTerm_mix_sumList_mix_piMix.strong_exhaust(3))
  using [[simproc del: alpha_lst]]
  apply(auto simp add: fresh_star_def)[1]
  apply(blast)
  apply(blast)
  apply(blast)
  using [[simproc del: alpha_lst]]
  apply(auto simp add: fresh_star_def)[1]
  apply(simp)
  --"compatibility"
  apply (simp only: meta_eq_to_obj_eq[OF subs_mix_def, symmetric, unfolded fun_eq_iff])
  apply (subgoal_tac "eqvt_at (\<lambda>(a, b, c). subs_mix a b c) (P, xa, ya)")
  apply (thin_tac "eqvt_at subsGuard_mix_subsList_mix_subs_mix_sumC (Inr (Inr (P, xa, ya)))")
  apply (thin_tac "eqvt_at subsGuard_mix_subsList_mix_subs_mix_sumC (Inr (Inr (Pa, xa, ya)))")
  prefer 2
  apply (simp only: eqvt_at_def subs_mix_def)
  apply rule
  apply(simp (no_asm))
  apply (subst testrr)
  apply (simp add: subsGuard_mix_subsList_mix_subs_mix_sumC_def)
  apply (simp add: THE_default_def)
apply (case_tac "Ex1 (subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (P, xa, ya))))")
apply simp_all[2]
apply auto[1]
apply (erule_tac x="x" in allE)
apply simp
apply(thin_tac "\<forall>p. p \<bullet> The (subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (P, xa, ya)))) =
            (if \<exists>!x. subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (p \<bullet> P, p \<bullet> xa, p \<bullet> ya))) x
             then THE x. subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (p \<bullet> P, p \<bullet> xa, p \<bullet> ya))) x
             else Inr (Inr undefined))")
apply(thin_tac "\<forall>p. p \<bullet> (if \<exists>!x. subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (Pa, xa, ya))) x
                 then THE x. subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (Pa, xa, ya))) x
                 else Inr (Inr undefined)) =
            (if \<exists>!x. subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (p \<bullet> Pa, p \<bullet> xa, p \<bullet> ya))) x
             then THE x. subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (p \<bullet> Pa, p \<bullet> xa, p \<bullet> ya))) x
             else Inr (Inr undefined))")
apply (thin_tac "atom b \<sharp> (xa, ya)")
apply (thin_tac "atom ba \<sharp> (xa, ya)")
apply (thin_tac "[[atom b]]lst. P = [[atom ba]]lst. Pa")
apply(cases rule: subsGuard_mix_subsList_mix_subs_mix_graph.cases)
apply assumption
apply (metis Inr_not_Inl)
apply (metis Inr_not_Inl)
apply (metis Inr_not_Inl)
apply (metis Inr_inject Inr_not_Inl)
apply (metis Inr_inject Inr_not_Inl)
apply (rule_tac x="<\<nu>a>\<onesuperior>Sum_Type.projr
                            (Sum_Type.projr
                              (subsGuard_mix_subsList_mix_subs_mix_sum (Inr (Inr (Pb, xb, y)))))" in exI)
apply clarify
apply (rule the1_equality)
apply blast apply assumption
apply (rule_tac x="Sum_Type.projr
                       (Sum_Type.projr (subsGuard_mix_subsList_mix_subs_mix_sum (Inr (Inr (Pb, xb, y))))) \<parallel>\<onesuperior>
                      Sum_Type.projr
                       (Sum_Type.projr (subsGuard_mix_subsList_mix_subs_mix_sum (Inr (Inr (Q, xb, y)))))" in exI)
apply clarify
apply (rule the1_equality)
apply blast apply assumption
apply (rule_tac x="[(a[xb:::=y])\<frown>\<onesuperior>(bb[xb:::=y])]Sum_Type.projr
                                                    (Sum_Type.projr
(subsGuard_mix_subsList_mix_subs_mix_sum (Inr (Inr (Pb, xb, y)))))" in exI)
apply clarify
apply (rule the1_equality)
apply blast apply assumption
apply (rule_tac x="\<oplus>\<onesuperior>{Sum_Type.projl
                          (Sum_Type.projr
                            (subsGuard_mix_subsList_mix_subs_mix_sum (Inr (Inl (xg, xb, y)))))}" in exI)
apply clarify
apply (rule the1_equality)
apply blast apply assumption
apply (rule_tac x="\<infinity>(a[xb:::=y])?<bb>\<onesuperior>.Sum_Type.projr
                                           (Sum_Type.projr
                                             (subsGuard_mix_subsList_mix_subs_mix_sum
                                               (Inr (Inr (Pb, xb, y)))))" in exI)
apply clarify
apply (rule the1_equality)
apply blast apply assumption
apply (rule_tac x="succ\<onesuperior>" in exI)
apply clarify
apply (rule the1_equality)
apply blast apply assumption
apply simp
(* Here the only real goal compatibility is left *)
  apply (erule Abs_lst1_fcb)
  apply (simp_all add: Abs_fresh_iff fresh_fun_eqvt_app)
  apply (subgoal_tac "atom ba \<sharp> (\<lambda>(a, x, y). subs_mix a x y) (P, xa, ya)")
  apply simp
  apply (erule fresh_eqvt_at)
  apply(simp add: finite_supp)
  apply(simp)
  apply(simp add: eqvt_at_def)
  apply(drule_tac x="(b \<leftrightarrow> ba)" in spec)
  apply(simp)
  apply (simp only: meta_eq_to_obj_eq[OF subs_mix_def, symmetric, unfolded fun_eq_iff])
  apply(rename_tac b P ba xa ya Pa)
 apply (subgoal_tac "eqvt_at (\<lambda>(a, b, c). subs_mix a b c) (P, xa, ya)")
  apply (thin_tac "eqvt_at subsGuard_mix_subsList_mix_subs_mix_sumC (Inr (Inr (P, xa, ya)))")
  apply (thin_tac "eqvt_at subsGuard_mix_subsList_mix_subs_mix_sumC (Inr (Inr (Pa, xa, ya)))")
  prefer 2
  apply (simp only: eqvt_at_def subs_mix_def)
  apply rule
  apply(simp (no_asm))
  apply (subst testrr)
  apply (simp add: subsGuard_mix_subsList_mix_subs_mix_sumC_def)
  apply (simp add: THE_default_def)
apply (case_tac "Ex1 (subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (P, xa, ya))))")
apply simp_all[2]
apply auto[1]
apply (erule_tac x="x" in allE)
apply simp
apply(thin_tac "\<forall>p. p \<bullet> The (subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (P, xa, ya)))) =
            (if \<exists>!x. subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (p \<bullet> P, p \<bullet> xa, p \<bullet> ya))) x
             then THE x. subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (p \<bullet> P, p \<bullet> xa, p \<bullet> ya))) x
             else Inr (Inr undefined))")
apply(thin_tac "\<forall>p. p \<bullet> (if \<exists>!x. subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (Pa, xa, ya))) x
                 then THE x. subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (Pa, xa, ya))) x
                 else Inr (Inr undefined)) =
            (if \<exists>!x. subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (p \<bullet> Pa, p \<bullet> xa, p \<bullet> ya))) x
             then THE x. subsGuard_mix_subsList_mix_subs_mix_graph (Inr (Inr (p \<bullet> Pa, p \<bullet> xa, p \<bullet> ya))) x
             else Inr (Inr undefined))")
apply (thin_tac "atom b \<sharp> (xa, ya)")
apply (thin_tac "atom ba \<sharp> (xa, ya)")
apply (thin_tac "[[atom b]]lst. P = [[atom ba]]lst. Pa")
apply(cases rule: subsGuard_mix_subsList_mix_subs_mix_graph.cases)
apply assumption
apply (metis Inr_not_Inl)
apply (metis Inr_not_Inl)
apply (metis Inr_not_Inl)
apply (metis Inr_inject Inr_not_Inl)
apply (metis Inr_inject Inr_not_Inl)
apply (rule_tac x="<\<nu>a>\<onesuperior>Sum_Type.projr
                            (Sum_Type.projr
                              (subsGuard_mix_subsList_mix_subs_mix_sum (Inr (Inr (Pb, xb, y)))))" in exI)
apply clarify
apply (rule the1_equality)
apply blast apply assumption
apply (rule_tac x="Sum_Type.projr
                       (Sum_Type.projr (subsGuard_mix_subsList_mix_subs_mix_sum (Inr (Inr (Pb, xb, y))))) \<parallel>\<onesuperior>
                      Sum_Type.projr
                       (Sum_Type.projr (subsGuard_mix_subsList_mix_subs_mix_sum (Inr (Inr (Q, xb, y)))))" in exI)
apply clarify
apply (rule the1_equality)
apply blast apply assumption
apply (rule_tac x="[(a[xb:::=y])\<frown>\<onesuperior>(bb[xb:::=y])]Sum_Type.projr
                                                    (Sum_Type.projr
(subsGuard_mix_subsList_mix_subs_mix_sum (Inr (Inr (Pb, xb, y)))))" in exI)
apply clarify
apply (rule the1_equality)
apply blast apply assumption
apply (rule_tac x="\<oplus>\<onesuperior>{Sum_Type.projl
                          (Sum_Type.projr
                            (subsGuard_mix_subsList_mix_subs_mix_sum (Inr (Inl (xg, xb, y)))))}" in exI)
apply clarify
apply (rule the1_equality)
apply blast apply assumption
apply (rule_tac x="\<infinity>(a[xb:::=y])?<bb>\<onesuperior>.Sum_Type.projr
                                           (Sum_Type.projr
                                             (subsGuard_mix_subsList_mix_subs_mix_sum
                                               (Inr (Inr (Pb, xb, y)))))" in exI)
apply clarify
apply (rule the1_equality)
apply blast apply assumption
apply (rule_tac x="succ\<onesuperior>" in exI)
apply clarify
apply (rule the1_equality)
apply blast apply assumption
apply simp
(* Here the only real goal compatibility is left *)
  apply (erule Abs_lst1_fcb)
  apply (simp_all add: Abs_fresh_iff fresh_fun_eqvt_app)
  apply (subgoal_tac "atom ba \<sharp> (\<lambda>(a, x, y). subs_mix a x y) (P, xa, ya)")
  apply simp
  apply (erule fresh_eqvt_at)
  apply(simp add: finite_supp)
  apply(simp)
  apply(simp add: eqvt_at_def)
  apply(drule_tac x="(b \<leftrightarrow> ba)" in spec)
  apply(simp)
  done

nominal_termination (eqvt)
  by (lexicographic_order)

lemma forget_mix:
  fixes g  :: guardedTerm_mix
  and   xg :: sumList_mix
  and   P  :: piMix
  and   x  :: name
  and   y  :: name

  shows "atom x \<sharp> g \<longrightarrow> g[x::=\<onesuperior>\<onesuperior>y] = g"
  and   "atom x \<sharp> xg \<longrightarrow> xg[x::=\<onesuperior>\<twosuperior>y] = xg"
  and   "atom x \<sharp> P \<longrightarrow> P[x::=\<onesuperior>y] = P"
proof -
  show  "atom x \<sharp> g \<longrightarrow> g[x::=\<onesuperior>\<onesuperior>y] = g"
  and   "atom x \<sharp> xg \<longrightarrow> xg[x::=\<onesuperior>\<twosuperior>y] = xg"
  and   "atom x \<sharp> P \<longrightarrow> P[x::=\<onesuperior>y] = P"
    using assms
    apply(nominal_induct g and xg and P avoiding: x y rule: piMix_strong_induct)
    by(auto simp add: piMix_eq_iff piMix_fresh fresh_at_base)
qed

lemma fresh_fact_mix:
  fixes g  :: guardedTerm_mix
  and   xg :: sumList_mix
  and   P  :: piMix
  and   x  :: name
  and   y  :: name
  and   z  :: name

  assumes "atom z \<sharp> y"

  shows "(z = x \<or> atom z \<sharp> g) \<longrightarrow> atom z \<sharp> g[x::=\<onesuperior>\<onesuperior>y]"
  and   "(z = x \<or> atom z \<sharp> xg) \<longrightarrow> atom z \<sharp> xg[x::=\<onesuperior>\<twosuperior>y]"
  and   "(z = x \<or> atom z \<sharp> P) \<longrightarrow> atom z \<sharp> P[x::=\<onesuperior>y]"
proof -
  show  "(z = x \<or> atom z \<sharp> g) \<longrightarrow> atom z \<sharp> g[x::=\<onesuperior>\<onesuperior>y]"
  and   "(z = x \<or> atom z \<sharp> xg) \<longrightarrow> atom z \<sharp> xg[x::=\<onesuperior>\<twosuperior>y]"
  and   "(z = x \<or> atom z \<sharp> P) \<longrightarrow> atom z \<sharp> P[x::=\<onesuperior>y]"
    using assms
    apply(nominal_induct g and xg and P avoiding: x y z rule: piMix_strong_induct)
    by(auto simp add: piMix_fresh fresh_at_base)
qed

lemma substitution_lemma_mix:
  fixes g  :: guardedTerm_mix
  and   xg :: sumList_mix
  and   P  :: piMix
  and   s  :: name
  and   u  :: name
  and   x  :: name
  and   y  :: name

  assumes "x \<noteq> y"
  and     "atom x \<sharp> u"

  shows "g[x::=\<onesuperior>\<onesuperior>s][y::=\<onesuperior>\<onesuperior>u] = g[y::=\<onesuperior>\<onesuperior>u][x::=\<onesuperior>\<onesuperior>s[y:::=u]]"
  and   "xg[x::=\<onesuperior>\<twosuperior>s][y::=\<onesuperior>\<twosuperior>u] = xg[y::=\<onesuperior>\<twosuperior>u][x::=\<onesuperior>\<twosuperior>s[y:::=u]]"
  and   "P[x::=\<onesuperior>s][y::=\<onesuperior>u] = P[y::=\<onesuperior>u][x::=\<onesuperior>s[y:::=u]]"
proof -
  show  "g[x::=\<onesuperior>\<onesuperior>s][y::=\<onesuperior>\<onesuperior>u] = g[y::=\<onesuperior>\<onesuperior>u][x::=\<onesuperior>\<onesuperior>s[y:::=u]]"
  and   "xg[x::=\<onesuperior>\<twosuperior>s][y::=\<onesuperior>\<twosuperior>u] = xg[y::=\<onesuperior>\<twosuperior>u][x::=\<onesuperior>\<twosuperior>s[y:::=u]]"
  and   "P[x::=\<onesuperior>s][y::=\<onesuperior>u] = P[y::=\<onesuperior>u][x::=\<onesuperior>s[y:::=u]]"
    using assms
    apply(nominal_induct g and xg and P avoiding: x y s u rule: piMix_strong_induct)
    apply(simp_all add: fresh_fact_mix forget_mix)
    by(auto simp add: fresh_at_base)
qed

lemma perm_eq_subst_mix:
  fixes g  :: guardedTerm_mix
  and   xg :: sumList_mix
  and   P  :: piMix
  and   x  :: name
  and   y  :: name

  shows "atom y \<sharp> g \<longrightarrow> (atom x \<rightleftharpoons> atom y) \<bullet> g = g[x::=\<onesuperior>\<onesuperior>y]"
  and   "atom y \<sharp> xg \<longrightarrow> (atom x \<rightleftharpoons> atom y) \<bullet> xg = xg[x::=\<onesuperior>\<twosuperior>y]"
  and   "atom y \<sharp> P \<longrightarrow> (atom x \<rightleftharpoons> atom y) \<bullet> P = P[x::=\<onesuperior>y]"
proof -
  show  "atom y \<sharp> g \<longrightarrow> (atom x \<rightleftharpoons> atom y) \<bullet> g = g[x::=\<onesuperior>\<onesuperior>y]"
  and   "atom y \<sharp> xg \<longrightarrow> (atom x \<rightleftharpoons> atom y) \<bullet> xg = xg[x::=\<onesuperior>\<twosuperior>y]"
  and   "atom y \<sharp> P \<longrightarrow> (atom x \<rightleftharpoons> atom y) \<bullet> P = P[x::=\<onesuperior>y]"
    apply(nominal_induct g and xg and P avoiding: x y rule: piMix_strong_induct)
    by(auto simp add: piMix_fresh fresh_at_base)
qed

lemma subst_id_mix:
  fixes g  :: guardedTerm_mix
  and   xg :: sumList_mix
  and   P  :: piMix
  and   x  :: name

  shows "g[x::=\<onesuperior>\<onesuperior>x] = g" and "xg[x::=\<onesuperior>\<twosuperior>x] = xg" and "P[x::=\<onesuperior>x] = P"
proof -
  show  "g[x::=\<onesuperior>\<onesuperior>x] = g" and "xg[x::=\<onesuperior>\<twosuperior>x] = xg" and "P[x::=\<onesuperior>x] = P"
    apply(nominal_induct g and xg and P avoiding: x rule: piMix_strong_induct)
    by(auto)
qed

lemma alphaRes_subst_mix:
  fixes a :: name
  and   P :: piMix
  and   z :: name

  assumes "atom z \<sharp> P"

  shows "<\<nu>a>\<onesuperior>P = <\<nu>z>\<onesuperior>(P[a::=\<onesuperior>z])"
proof(cases "a = z")
  assume "a = z"
  thus ?thesis
    by(simp add: subst_id_mix)
next
  assume "a \<noteq> z"
  thus ?thesis
    using assms
    by(simp add: alphaRes_mix perm_eq_subst_mix)
qed

lemma alphaInput_subst_mix:
  fixes a :: name
  and   b :: name
  and   P :: piMix
  and   z :: name

  assumes "atom z \<sharp> P"

  shows "a?<b>\<onesuperior>.P = a?<z>\<onesuperior>.(P[b::=\<onesuperior>z])"
proof(cases "b = z")
  assume "b = z"
  thus ?thesis
    by(simp add: subst_id_mix)
next
  assume "b \<noteq> z"
  thus ?thesis
    using assms
    by(simp add: alphaInput_mix perm_eq_subst_mix)
qed

lemma alphaRep_subst_mix:
  fixes a :: name
  and   b :: name
  and   P :: piMix
  and   z :: name

  assumes "atom z \<sharp> P"

  shows "\<infinity>a?<b>\<onesuperior>.P = \<infinity>a?<z>\<onesuperior>.(P[b::=\<onesuperior>z])"
proof(cases "b = z")
  assume "b = z"
  thus ?thesis
    by(simp add: subst_id_mix)
next
  assume "b \<noteq> z"
  thus ?thesis
    using assms
    by(simp add: alphaRep_mix perm_eq_subst_mix)
qed

inductive
  fresh_list_guard_mix :: "name list \<Rightarrow> guardedTerm_mix \<Rightarrow> bool"
where
  "fresh_list_guard_mix [] g"
| "\<lbrakk>atom n \<sharp> g; fresh_list_guard_mix xn g\<rbrakk> \<Longrightarrow> fresh_list_guard_mix (n#xn) g"

equivariance fresh_list_guard_mix
nominal_inductive fresh_list_guard_mix
  done

inductive
  fresh_list_sumList_mix :: "name list \<Rightarrow> sumList_mix \<Rightarrow> bool"
where
  "fresh_list_sumList_mix [] xg"
| "\<lbrakk>atom n \<sharp> xg; fresh_list_sumList_mix xn xg\<rbrakk> \<Longrightarrow> fresh_list_sumList_mix (n#xn) xg"

equivariance fresh_list_sumList_mix
nominal_inductive fresh_list_sumList_mix
  done

inductive
  fresh_list_mix :: "name list \<Rightarrow> piMix \<Rightarrow> bool"
where
  "fresh_list_mix [] P"
| "\<lbrakk>atom n \<sharp> P; fresh_list_mix xn P\<rbrakk> \<Longrightarrow> fresh_list_mix (n#xn) P"

equivariance fresh_list_mix
nominal_inductive fresh_list_mix
  done

end
