theory Let
imports "../Nominal2" 
begin

atom_decl name

nominal_datatype trm =
  Var "name"
| App "trm" "trm"
| Lam x::"name" t::"trm"  binds  x in t
| Let as::"assn" t::"trm"   binds "bn as" in t
and assn =
  ANil
| ACons "name" "trm" "assn"
binder
  bn
where
  "bn ANil = []"
| "bn (ACons x t as) = (atom x) # (bn as)"

print_theorems

thm alpha_trm_raw_alpha_assn_raw_alpha_bn_raw.intros
thm bn_raw.simps
thm permute_bn_raw.simps
thm trm_assn.perm_bn_alpha
thm trm_assn.permute_bn

thm trm_assn.fv_defs
thm trm_assn.eq_iff 
thm trm_assn.bn_defs
thm trm_assn.bn_inducts
thm trm_assn.perm_simps
thm trm_assn.permute_bn
thm trm_assn.induct
thm trm_assn.inducts
thm trm_assn.distinct
thm trm_assn.supp
thm trm_assn.fresh
thm trm_assn.exhaust
thm trm_assn.strong_exhaust
thm trm_assn.perm_bn_simps

lemma alpha_bn_inducts_raw[consumes 1]:
  "\<lbrakk>alpha_bn_raw a b; P3 ANil_raw ANil_raw;
 \<And>trm_raw trm_rawa assn_raw assn_rawa name namea.
    \<lbrakk>alpha_trm_raw trm_raw trm_rawa; alpha_bn_raw assn_raw assn_rawa;
     P3 assn_raw assn_rawa\<rbrakk>
    \<Longrightarrow> P3 (ACons_raw name trm_raw assn_raw)
        (ACons_raw namea trm_rawa assn_rawa)\<rbrakk> \<Longrightarrow> P3 a b"
  by (erule alpha_trm_raw_alpha_assn_raw_alpha_bn_raw.inducts(3)[of _ _ "\<lambda>x y. True" _ "\<lambda>x y. True", simplified]) auto

lemmas alpha_bn_inducts[consumes 1] = alpha_bn_inducts_raw[quot_lifted]



lemma alpha_bn_refl: "alpha_bn x x"
  by (induct x rule: trm_assn.inducts(2))
     (rule TrueI, auto simp add: trm_assn.eq_iff)
lemma alpha_bn_sym: "alpha_bn x y \<Longrightarrow> alpha_bn y x"
  sorry
lemma alpha_bn_trans: "alpha_bn x y \<Longrightarrow> alpha_bn y z \<Longrightarrow> alpha_bn x z"
  sorry

lemma bn_inj[rule_format]:
  assumes a: "alpha_bn x y"
  shows "bn x = bn y \<longrightarrow> x = y"
  by (rule alpha_bn_inducts[OF a]) (simp_all add: trm_assn.bn_defs)

lemma bn_inj2:
  assumes a: "alpha_bn x y"
  shows "\<And>q r. (q \<bullet> bn x) = (r \<bullet> bn y) \<Longrightarrow> permute_bn q x = permute_bn r y"
using a
apply(induct rule: alpha_bn_inducts)
apply(simp add: trm_assn.perm_bn_simps)
apply(simp add: trm_assn.perm_bn_simps)
apply(simp add: trm_assn.bn_defs)
done


function
  apply_assn :: "(trm \<Rightarrow> nat) \<Rightarrow> assn \<Rightarrow> nat"
where
  "apply_assn f ANil = (0 :: nat)"
| "apply_assn f (ACons x t as) = max (f t) (apply_assn f as)"
apply(case_tac x)
apply(case_tac b rule: trm_assn.exhaust(2))
apply(simp_all)
done

termination by lexicographic_order

lemma [eqvt]:
  "p \<bullet> (apply_assn f a) = apply_assn (p \<bullet> f) (p \<bullet> a)"
  apply(induct f a rule: apply_assn.induct)
  apply simp
  apply(simp only: apply_assn.simps trm_assn.perm_simps)
  apply(perm_simp)
  apply(simp)
  done

lemma alpha_bn_apply_assn:
  assumes "alpha_bn as bs"
  shows "apply_assn f as = apply_assn f bs"
  using assms
  apply (induct rule: alpha_bn_inducts)
  apply simp_all
  done

nominal_function
    height_trm :: "trm \<Rightarrow> nat"
where
  "height_trm (Var x) = 1"
| "height_trm (App l r) = max (height_trm l) (height_trm r)"
| "height_trm (Lam v b) = 1 + (height_trm b)"
| "height_trm (Let as b) = max (apply_assn height_trm as) (height_trm b)"
  apply (simp only: eqvt_def height_trm_graph_aux_def)
  apply (rule, perm_simp, rule, rule TrueI)
  apply (case_tac x rule: trm_assn.exhaust(1))
  apply (auto)[4]
  apply (drule_tac x="assn" in meta_spec)
  apply (drule_tac x="trm" in meta_spec)
  apply (simp add: alpha_bn_refl)
  using [[simproc del: alpha_lst]]
  apply(simp_all)
  apply (erule_tac c="()" in Abs_lst1_fcb2)
  apply (simp_all add: pure_fresh fresh_star_def eqvt_at_def)[4]
  apply (erule conjE)
  apply (subst alpha_bn_apply_assn)
  apply assumption
  apply (rule arg_cong) back
  apply (erule_tac c="()" in Abs_lst_fcb2)
  apply (simp_all add: pure_fresh fresh_star_def)[3]
  apply (simp_all add: eqvt_at_def)[2]
  done

definition "height_assn = apply_assn height_trm"

function
  apply_assn2 :: "(trm \<Rightarrow> trm) \<Rightarrow> assn \<Rightarrow> assn"
where
  "apply_assn2 f ANil = ANil"
| "apply_assn2 f (ACons x t as) = ACons x (f t) (apply_assn2 f as)"
  apply(case_tac x)
  apply(case_tac b rule: trm_assn.exhaust(2))
  apply(simp_all)
  done

termination by lexicographic_order

lemma [eqvt]:
  "p \<bullet> (apply_assn2 f a) = apply_assn2 (p \<bullet> f) (p \<bullet> a)"
  apply(induct f a rule: apply_assn2.induct)
  apply simp_all
  done

lemma bn_apply_assn2: "bn (apply_assn2 f as) = bn as"
  apply (induct as rule: trm_assn.inducts(2))
  apply (rule TrueI)
  apply (simp_all add: trm_assn.bn_defs)
  done

nominal_function
    subst  :: "name \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm"
where
  "subst s t (Var x) = (if (s = x) then t else (Var x))"
| "subst s t (App l r) = App (subst s t l) (subst s t r)"
| "atom v \<sharp> (s, t) \<Longrightarrow> subst s t (Lam v b) = Lam v (subst s t b)"
| "set (bn as) \<sharp>* (s, t) \<Longrightarrow> subst s t (Let as b) = Let (apply_assn2 (subst s t) as) (subst s t b)"
  apply (simp only: eqvt_def subst_graph_aux_def)
  apply (rule, perm_simp, rule)
  apply (rule TrueI)
  apply (case_tac x)
  apply (rule_tac y="c" and c="(a,b)" in trm_assn.strong_exhaust(1))
  apply (auto simp add: fresh_star_def)[3]
  apply (drule_tac x="assn" in meta_spec)
  apply (simp add: Abs1_eq_iff alpha_bn_refl)
  apply simp_all[7]
  prefer 2
  apply(simp)
  using [[simproc del: alpha_lst]]
  apply(simp)
  apply(erule conjE)+
  apply (erule_tac c="(sa, ta)" in Abs_lst1_fcb2)
  apply (simp add: Abs_fresh_iff)
  apply (simp add: fresh_star_def)
  apply (simp_all add: fresh_star_Pair_elim perm_supp_eq eqvt_at_def)[2]
  apply (simp add: bn_apply_assn2)
  apply(erule conjE)+
  apply(rule conjI)
  apply (erule_tac c="(sa, ta)" in Abs_lst_fcb2)
  apply (simp add: fresh_star_def Abs_fresh_iff)
  apply assumption+
  apply (simp_all add: fresh_star_Pair_elim perm_supp_eq eqvt_at_def trm_assn.fv_bn_eqvt)[2]
  apply (erule alpha_bn_inducts)
  apply simp_all
  done

lemma lets_bla:
  "x \<noteq> z \<Longrightarrow> y \<noteq> z \<Longrightarrow> x \<noteq> y \<Longrightarrow>(Let (ACons x (Var y) ANil) (Var x)) \<noteq> (Let (ACons x (Var z) ANil) (Var x))"
  by (simp add: trm_assn.eq_iff)

lemma lets_ok:
  "(Let (ACons x (Var y) ANil) (Var x)) = (Let (ACons y (Var y) ANil) (Var y))"
  apply (simp add: trm_assn.eq_iff Abs_eq_iff )
  apply (rule_tac x="(x \<leftrightarrow> y)" in exI)
  apply (simp_all add: alphas atom_eqvt supp_at_base fresh_star_def trm_assn.bn_defs trm_assn.supp)
  done

lemma lets_ok3:
  "x \<noteq> y \<Longrightarrow>
   (Let (ACons x (App (Var y) (Var x)) (ACons y (Var y) ANil)) (App (Var x) (Var y))) \<noteq>
   (Let (ACons y (App (Var x) (Var y)) (ACons x (Var x) ANil)) (App (Var x) (Var y)))"
  apply (simp add: trm_assn.eq_iff)
  done

lemma lets_not_ok1:
  "x \<noteq> y \<Longrightarrow>
   (Let (ACons x (Var x) (ACons y (Var y) ANil)) (App (Var x) (Var y))) \<noteq>
   (Let (ACons y (Var x) (ACons x (Var y) ANil)) (App (Var x) (Var y)))"
  apply (simp add: alphas trm_assn.eq_iff trm_assn.supp fresh_star_def atom_eqvt Abs_eq_iff trm_assn.bn_defs)
  done

lemma lets_nok:
  "x \<noteq> y \<Longrightarrow> x \<noteq> z \<Longrightarrow> z \<noteq> y \<Longrightarrow>
   (Let (ACons x (App (Var z) (Var z)) (ACons y (Var z) ANil)) (App (Var x) (Var y))) \<noteq>
   (Let (ACons y (Var z) (ACons x (App (Var z) (Var z)) ANil)) (App (Var x) (Var y)))"
  apply (simp add: alphas trm_assn.eq_iff fresh_star_def trm_assn.bn_defs Abs_eq_iff trm_assn.supp trm_assn.distinct)
  done

lemma
  fixes a b c :: name
  assumes x: "a \<noteq> c" and y: "b \<noteq> c"
  shows "\<exists>p.([atom a], Var c) \<approx>lst (op =) supp p ([atom b], Var c)"
  apply (rule_tac x="(a \<leftrightarrow> b)" in exI)
  apply (simp add: alphas trm_assn.supp supp_at_base x y fresh_star_def atom_eqvt)
  by (metis Rep_name_inverse atom_name_def flip_fresh_fresh fresh_atom fresh_perm x y)

end
