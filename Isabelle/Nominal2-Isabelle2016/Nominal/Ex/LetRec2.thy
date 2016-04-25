theory LetRec2
imports "../Nominal2"
begin

atom_decl name

nominal_datatype trm =
  Var "name"
| App "trm" "trm"
| Lam x::"name" t::"trm"  binds x in t
| Let as::"assn" t::"trm"   binds "bn as" in t
| Let_rec as::"assn" t::"trm"   binds "bn as" in as t
and assn =
  ANil
| ACons "name" "trm" "assn"
binder
  bn
where
  "bn (ANil) = []"
| "bn (ACons x t as) = (atom x) # (bn as)"

thm trm_assn.eq_iff
thm trm_assn.supp

ML {*
@{term Trueprop} ;
@{const_name HOL.eq}
*}

thm trm_assn.fv_defs
thm trm_assn.eq_iff
thm trm_assn.bn_defs
thm trm_assn.perm_simps
thm trm_assn.induct
thm trm_assn.distinct



section {* Tests *}


(* why is this not in HOL simpset? *)
(*
lemma set_sub: "{a, b} - {b} = {a} - {b}"
by auto

lemma lets_bla:
  "x \<noteq> z \<Longrightarrow> y \<noteq> z \<Longrightarrow> x \<noteq> y \<Longrightarrow>(Lt (Lcons x (Vr y) Lnil) (Vr x)) \<noteq> (Lt (Lcons x (Vr z) Lnil) (Vr x))"
  apply (auto simp add: trm_lts.eq_iff alphas set_sub supp_at_base)
  done

lemma lets_ok:
  "(Lt (Lcons x (Vr x) Lnil) (Vr x)) = (Lt (Lcons y (Vr y) Lnil) (Vr y))"
  apply (simp add: trm_lts.eq_iff)
  apply (rule_tac x="(x \<leftrightarrow> y)" in exI)
  apply (simp_all add: alphas fresh_star_def eqvts supp_at_base)
  done

lemma lets_ok3:
  "x \<noteq> y \<Longrightarrow>
   (Lt (Lcons x (Ap (Vr y) (Vr x)) (Lcons y (Vr y) Lnil)) (Ap (Vr x) (Vr y))) \<noteq>
   (Lt (Lcons y (Ap (Vr x) (Vr y)) (Lcons x (Vr x) Lnil)) (Ap (Vr x) (Vr y)))"
  apply (simp add: alphas trm_lts.eq_iff)
  done


lemma lets_not_ok1:
  "x \<noteq> y \<Longrightarrow>
   (Lt (Lcons x (Vr x) (Lcons y (Vr y) Lnil)) (Ap (Vr x) (Vr y))) \<noteq>
   (Lt (Lcons y (Vr x) (Lcons x (Vr y) Lnil)) (Ap (Vr x) (Vr y)))"
  apply (simp add: alphas trm_lts.eq_iff)
  done

lemma lets_nok:
  "x \<noteq> y \<Longrightarrow> x \<noteq> z \<Longrightarrow> z \<noteq> y \<Longrightarrow>
   (Lt (Lcons x (Ap (Vr z) (Vr z)) (Lcons y (Vr z) Lnil)) (Ap (Vr x) (Vr y))) \<noteq>
   (Lt (Lcons y (Vr z) (Lcons x (Ap (Vr z) (Vr z)) Lnil)) (Ap (Vr x) (Vr y)))"
  apply (simp add: alphas trm_lts.eq_iff fresh_star_def)
  done

lemma lets_ok4:
  "(Lt (Lcons x (Ap (Vr y) (Vr x)) (Lcons y (Vr y) Lnil)) (Ap (Vr x) (Vr y))) =
   (Lt (Lcons y (Ap (Vr x) (Vr y)) (Lcons x (Vr x) Lnil)) (Ap (Vr y) (Vr x)))"
  apply (simp add: alphas trm_lts.eq_iff supp_at_base)
  apply (rule_tac x="(x \<leftrightarrow> y)" in exI)
  apply (simp add: atom_eqvt fresh_star_def)
  done
*)
end



