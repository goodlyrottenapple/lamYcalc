header {* CPS transformation of Danvy and Nielsen *}
theory CPS2_DanvyNielsen
imports Lt
begin

nominal_datatype cpsctxt =
  Hole
| CFun cpsctxt lt
| CArg lt cpsctxt
| CAbs x::name c::cpsctxt binds x in c

nominal_function
  fill   :: "cpsctxt \<Rightarrow> lt \<Rightarrow> lt"         ("_<_>" [200, 200] 100)
where
  fill_hole : "Hole<M> = M"
| fill_fun  : "(CFun C N)<M> = (C<M>) $$ N"
| fill_arg  : "(CArg N C)<M> = N $$ (C<M>)"
| fill_abs  : "atom x \<sharp> M \<Longrightarrow> (CAbs x C)<M> = Lam x (C<M>)"
  unfolding eqvt_def fill_graph_aux_def
  apply simp
  using [[simproc del: alpha_lst]]
  apply auto
  apply (rule_tac y="a" and c="b" in cpsctxt.strong_exhaust)
  using [[simproc del: alpha_lst]]
  apply (auto simp add: fresh_star_def)
  apply (erule Abs_lst1_fcb)
  apply (simp_all add: Abs_fresh_iff)[2]
  apply (erule fresh_eqvt_at)
  apply (simp add: finite_supp)
  apply (simp add: fresh_Pair)
  apply (simp add: eqvt_at_def)
  apply (simp add: flip_fresh_fresh)
  done

nominal_termination (eqvt) by lexicographic_order

nominal_function
  ccomp :: "cpsctxt => cpsctxt => cpsctxt"
where
  "ccomp Hole C  = C"
| "atom x \<sharp> C' \<Longrightarrow> ccomp (CAbs x C) C' = CAbs x (ccomp C C')"
| "ccomp (CArg N C) C' = CArg N (ccomp C C')"
| "ccomp (CFun C N) C'  = CFun (ccomp C C') N"
  unfolding eqvt_def ccomp_graph_aux_def
  apply simp
  using [[simproc del: alpha_lst]]
  apply auto
  apply (rule_tac y="a" and c="b" in cpsctxt.strong_exhaust)
  using [[simproc del: alpha_lst]]
  apply (auto simp add: fresh_star_def)
  apply (erule Abs_lst1_fcb)
  apply (simp_all add: Abs_fresh_iff)
  apply (erule fresh_eqvt_at)
  apply (simp add: finite_supp)
  apply (simp add: fresh_Pair)
  apply (simp add: eqvt_at_def)
  apply (simp add: flip_fresh_fresh)
  done

nominal_termination (eqvt) by lexicographic_order

nominal_function
    CPSv :: "lt => lt"
and CPS :: "lt => cpsctxt" where
  "CPSv (Var x) = x~"
| "CPS (Var x) = CFun Hole (x~)"
| "atom b \<sharp> M \<Longrightarrow> CPSv (Lam y M) = Lam y (Lam b ((CPS M)<Var b>))"
| "atom b \<sharp> M \<Longrightarrow> CPS (Lam y M) = CFun Hole (Lam y (Lam b ((CPS M)<Var b>)))"
| "CPSv (M $$ N) = Lam x (Var x)"
| "isValue M \<Longrightarrow> isValue N \<Longrightarrow> CPS (M $$ N) = CArg (CPSv M $$ CPSv N) Hole"
| "isValue M \<Longrightarrow> ~isValue N \<Longrightarrow> atom a \<sharp> M \<Longrightarrow> CPS (M $$ N) =
     ccomp (CPS N) (CAbs a (CArg (CPSv M $$ Var a) Hole))"
| "~isValue M \<Longrightarrow> isValue N \<Longrightarrow> atom a \<sharp> N \<Longrightarrow> CPS (M $$ N) =
     ccomp (CPS M) (CAbs a (CArg (Var a $$ (CPSv N)) Hole))"
| "~isValue M \<Longrightarrow> ~isValue N \<Longrightarrow> atom a \<sharp> (N, b) \<Longrightarrow> CPS (M $$ N) =
     ccomp (CPS M) (CAbs a (ccomp (CPS N) (CAbs b (CArg (Var a $$ Var b) Hole))))"
  using [[simproc del: alpha_lst]]
  apply auto
  defer
  apply (case_tac x)
  apply (rule_tac y="a" in lt.exhaust)
  using [[simproc del: alpha_lst]]
  apply auto
  apply (rule_tac x="lt" and ?'a="name" in obtain_fresh)
  apply (simp add: Abs1_eq_iff)
  apply blast+
  apply (rule_tac y="b" in lt.exhaust)
  apply auto
  apply (rule_tac ?'a="name" in obtain_fresh)
  apply (rule_tac x="(lt1, lt2, a)" and ?'a="name" in obtain_fresh)
  apply (simp add: fresh_Pair_elim)
  apply (case_tac "isValue lt1", case_tac [!] "isValue lt2")[1]
  apply (simp_all add: fresh_Pair)[4]
  apply (rule_tac x="lt" and ?'a="name" in obtain_fresh)
  apply (simp add: Abs1_eq_iff)
  apply blast
--""
  apply (rule_tac x="(y, ya, b, ba, M, Ma)" and ?'a="name" in obtain_fresh)
  apply (subgoal_tac "Lam b (Sum_Type.projr (CPSv_CPS_sumC (Inr M))<(b~)>) = Lam a (Sum_Type.projr (CPSv_CPS_sumC (Inr M))<(a~)>)")
  apply (subgoal_tac "Lam ba (Sum_Type.projr (CPSv_CPS_sumC (Inr Ma))<(ba~)>) = Lam a (Sum_Type.projr (CPSv_CPS_sumC (Inr Ma))<(a~)>)")
  apply (simp only:)
  apply (erule Abs_lst1_fcb)
  apply (simp add: Abs_fresh_iff)
  apply (simp_all add: Abs_fresh_iff lt.fresh fresh_Pair_elim fresh_at_base swap_fresh_fresh)[2]
  (* need an invariant to get eqvt_at (Proj) *)
  defer defer
  apply simp
  apply (simp_all add: Abs1_eq_iff fresh_Pair_elim fresh_at_base)[2]
  defer defer
  defer
  apply (simp add: Abs1_eq_iff fresh_at_base lt.fresh)
  apply (rule arg_cong) back
  defer
  apply (rule arg_cong) back
  defer
  apply (rule arg_cong) back
  defer
  oops --"The goals seem reasonable"

end
