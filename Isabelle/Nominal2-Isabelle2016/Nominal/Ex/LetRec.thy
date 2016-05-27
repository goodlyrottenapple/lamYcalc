theory LetRec
imports "../Nominal2"
begin

atom_decl name

nominal_datatype let_rec:
 trm =
  Var "name"
| App "trm" "trm"
| Lam x::"name" t::"trm"     binds (set) x in t
| Let_Rec bp::"bp" t::"trm"  binds (set) "bn bp" in bp t
and bp =
  Bp "name" "trm"
binder
  bn::"bp \<Rightarrow> atom set"
where
  "bn (Bp x t) = {atom x}"

thm let_rec.distinct
thm let_rec.induct
thm let_rec.exhaust
thm let_rec.fv_defs
thm let_rec.bn_defs
thm let_rec.perm_simps
thm let_rec.eq_iff
thm let_rec.fv_bn_eqvt
thm let_rec.size_eqvt


nominal_function
    height_trm :: "trm \<Rightarrow> nat"
and height_bp :: "bp \<Rightarrow> nat"
where
  "height_trm (Var x) = 1"
| "height_trm (App l r) = max (height_trm l) (height_trm r)"
| "height_trm (Lam v b) = 1 + (height_trm b)"
| "height_trm (Let_Rec bp b) = max (height_bp bp) (height_trm b)"
| "height_bp (Bp v t) = height_trm t"
  apply (simp add: eqvt_def height_trm_height_bp_graph_aux_def)
  apply(rule TrueI)
  using [[simproc del: alpha_set]]
  apply auto
  apply (case_tac x)
  apply (case_tac a rule: let_rec.exhaust(1))
  using [[simproc del: alpha_set]]
  apply auto
  apply (case_tac b rule: let_rec.exhaust(2))
  apply blast
  apply (erule Abs_set_fcb)
  apply (simp_all add: pure_fresh)[2]
  apply (simp only: eqvt_at_def)
  apply(perm_simp)
  apply(simp)
  apply (simp add: Abs_eq_iff2)
  apply (simp add: alphas)
  apply clarify
  apply (rule trans)
  apply(rule_tac p="p" in supp_perm_eq[symmetric])
  apply (simp add: pure_supp fresh_star_def)
  apply(simp add: eqvt_at_def)
  done

nominal_termination (eqvt) by lexicographic_order

thm height_trm_height_bp.eqvt


end



