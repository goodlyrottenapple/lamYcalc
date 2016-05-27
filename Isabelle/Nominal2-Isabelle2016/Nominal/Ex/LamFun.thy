theory LamFun
imports "../Nominal2" Quotient_Option
begin

atom_decl name

nominal_datatype lam =
  Var "name"
| App "lam" "lam"
| Lam x::"name" l::"lam"  binds x in l

thm lam.distinct
thm lam.induct
thm lam.exhaust
thm lam.fv_defs
thm lam.bn_defs
thm lam.perm_simps
thm lam.eq_iff
thm lam.fv_bn_eqvt
thm lam.size_eqvt
thm lam.size
thm lam_raw.size
thm lam.fresh

primrec match_Var_raw where
  "match_Var_raw (Var_raw x) = Some x"
| "match_Var_raw (App_raw x y) = None"
| "match_Var_raw (Lam_raw n t) = None"

quotient_definition
  "match_Var :: lam \<Rightarrow> name option"
is match_Var_raw

lemma [quot_respect]: "(alpha_lam_raw ===> op =) match_Var_raw match_Var_raw"
  by (rule, induct_tac a b rule: alpha_lam_raw.induct, simp_all)

lemmas match_Var_simps = match_Var_raw.simps[quot_lifted]

primrec match_App_raw where
  "match_App_raw (Var_raw x) = None"
| "match_App_raw (App_raw x y) = Some (x, y)"
| "match_App_raw (Lam_raw n t) = None"

quotient_definition
  "match_App :: lam \<Rightarrow> (lam \<times> lam) option"
is match_App_raw

lemma [quot_respect]:
  "(alpha_lam_raw ===> option_rel (prod_rel alpha_lam_raw alpha_lam_raw)) match_App_raw match_App_raw"
  by (intro fun_relI, induct_tac a b rule: alpha_lam_raw.induct, simp_all)

lemmas match_App_simps = match_App_raw.simps[quot_lifted]

definition next_name where
  "next_name (s :: 'a :: fs) = (THE x. \<forall>a \<in> supp s. atom x \<noteq> a)"

lemma lam_eq: "Lam a t = Lam b s \<longleftrightarrow> (a \<leftrightarrow> b) \<bullet> t = s"
  apply (simp add: lam.eq_iff Abs_eq_iff alphas)
  sorry

lemma lam_half_inj: "(Lam z s = Lam z sa) = (s = sa)"
  by (auto simp add: lam_eq)

definition
  "match_Lam (S :: 'a :: fs) t = (if (\<exists>n s. (t = Lam n s)) then
    (let z = next_name (S, t) in Some (z, THE s. t = Lam z s)) else None)"

lemma match_Lam_simps:
  "match_Lam S (Var n) = None"
  "match_Lam S (App l r) = None"
  "match_Lam S (Lam z s) = (let n = next_name (S, (Lam z s)) in Some (n, (z \<leftrightarrow> n) \<bullet> s))"
  apply (simp_all add: match_Lam_def lam.distinct)
  apply (auto simp add: lam_eq)
  done

lemma app_some: "match_App x = Some (a, b) \<Longrightarrow> x = App a b"
by (induct x rule: lam.induct) (simp_all add: match_App_simps)


lemma lam_some: "match_Lam S x = Some (n, t) \<Longrightarrow> x = Lam n t"
  apply (induct x rule: lam.induct)
  apply (simp add: match_Lam_simps)
  apply (simp add: match_Lam_simps)
  apply (simp add: match_Lam_simps Let_def lam_eq)
  apply clarify
  done

function subst where
"subst v s t = (
  case match_Var t of Some n \<Rightarrow> if n = v then s else Var n | None \<Rightarrow>
  case match_App t of Some (l, r) \<Rightarrow> App (subst v s l) (subst v s r) | None \<Rightarrow>
  case match_Lam (v, s) t of Some (n, s') \<Rightarrow> Lam n (subst v s s') | None \<Rightarrow> undefined)"
print_theorems
thm subst_rel.intros[no_vars]
by pat_completeness auto

termination apply (relation "measure (\<lambda>(_, _, t). size t)")
  apply auto[1]
  apply (case_tac a) apply simp
  apply (frule lam_some) apply (simp add: lam.size)
  apply (case_tac a) apply simp
  apply (frule app_some) apply (simp add: lam.size)
  apply (case_tac a) apply simp
  apply (frule app_some) apply (simp add: lam.size)
done

lemma subst_eqs:
  "subst y s (Var x) = (if x = y then s else (Var x))"
  "subst y s (App l r) = App (subst y s l) (subst y s r)"
  "subst y s (Lam x t) =
    (let n = next_name ((y, s), Lam x t) in Lam n (subst y s ((x \<leftrightarrow> n) \<bullet> t)))"
  apply (subst subst.simps)
  apply (simp only: match_Var_simps option.simps)
  apply (subst subst.simps)
  apply (simp only: match_App_simps option.simps prod.simps match_Var_simps)
  apply (subst subst.simps)
  apply (simp only: match_App_simps option.simps prod.simps match_Var_simps match_Lam_simps Let_def)
  done

lemma subst_eqvt:
  "p \<bullet> (subst v s t) = subst (p \<bullet> v) (p \<bullet> s) (p \<bullet> t)"
  proof (induct v s t rule: subst.induct)
    case (1 v s t)
    show ?case proof (cases t rule: lam.exhaust)
      fix n
      assume "t = Var n"
      then show ?thesis by (simp add: match_Var_simps)
    next
      fix l r
      assume "t = App l r"
      then show ?thesis
        apply (simp only: subst_eqs lam.perm_simps)
        apply (subst 1(2)[of "(l, r)" "l" "r"])
        apply (simp add: match_Var_simps)
        apply (simp add: match_App_simps)
        apply (rule refl)
        apply (subst 1(3)[of "(l, r)" "l" "r"])
        apply (simp add: match_Var_simps)
        apply (simp add: match_App_simps)
        apply (rule refl)
        apply (rule refl)
        done
    next
      fix n t'
      assume "t = Lam n t'"
      then show ?thesis
        apply (simp only: subst_eqs lam.perm_simps Let_def)
        apply (subst 1(1))
        apply (simp add: match_Var_simps)
        apply (simp add: match_App_simps)
        apply (simp add: match_Lam_simps Let_def)
        apply (rule refl)
        (* next_name is not equivariant :( *)
        apply (simp only: lam_eq)
        sorry
    qed
  qed

lemma subst_eqvt':
  "p \<bullet> (subst v s t) = subst (p \<bullet> v) (p \<bullet> s) (p \<bullet> t)"
  apply (induct t arbitrary: v s rule: lam.induct)
  apply (simp only: subst_eqs lam.perm_simps eqvts)
  apply (simp only: subst_eqs lam.perm_simps)
  apply (simp only: subst_eqs lam.perm_simps Let_def)
  apply (simp only: lam_eq)
  sorry

lemma subst_eq3:
  "atom x \<sharp> (y, s) \<Longrightarrow> subst y s (Lam x t) = Lam x (subst y s t)"
  apply (simp only: subst_eqs Let_def)
  apply (simp only: lam_eq)
  (* p # y   p # s   subst_eqvt *)
  (* p \<bullet> -p \<bullet> (subst y s t) = subst y s t *)
  sorry

end



