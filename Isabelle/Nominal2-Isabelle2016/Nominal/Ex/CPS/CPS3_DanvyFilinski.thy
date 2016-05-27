header {* CPS transformation of Danvy and Filinski *}
theory CPS3_DanvyFilinski imports Lt begin

nominal_function
  CPS1 :: "lt \<Rightarrow> (lt \<Rightarrow> lt) \<Rightarrow> lt" ("_*_"  [100,100] 100)
and
  CPS2 :: "lt \<Rightarrow> lt \<Rightarrow> lt" ("_^_" [100,100] 100)
where
  "eqvt k \<Longrightarrow> (x~)*k = k (x~)"
| "eqvt k \<Longrightarrow> (M$$N)*k = M*(%m. (N*(%n.((m $$ n) $$ (Lam c (k (c~)))))))"
| "eqvt k \<Longrightarrow> atom c \<sharp> (x, M) \<Longrightarrow> (Lam x M)*k = k (Lam x (Lam c (M^(c~))))"
| "\<not>eqvt k \<Longrightarrow> (CPS1 t k) = t"
| "(x~)^l = l $$ (x~)"
| "(M$$N)^l = M*(%m. (N*(%n.((m $$ n) $$ l))))"
| "atom c \<sharp> (x, M) \<Longrightarrow> (Lam x M)^l = l $$ (Lam x (Lam c (M^(c~))))"
  apply (simp add: eqvt_def CPS1_CPS2_graph_aux_def)
  using [[simproc del: alpha_lst]]
  apply auto
  apply (case_tac x)
  apply (case_tac a)
  apply (case_tac "eqvt b")
  apply (rule_tac y="aa" in lt.strong_exhaust)
  apply auto[4]
  apply (rule_tac x="(name, lt)" and ?'a="name" in obtain_fresh)
  apply (simp add: fresh_at_base Abs1_eq_iff)
  apply (case_tac b)
  apply (rule_tac y="a" in lt.strong_exhaust)
  apply auto[3]
  apply (rule_tac x="(name, lt)" and ?'a="name" in obtain_fresh) 
  apply (simp add: fresh_at_base Abs1_eq_iff)
--"-"
  apply (subgoal_tac "Lam c (ka (c~)) = Lam ca (ka (ca~))")
  apply (simp only:)
  apply (simp add: Abs1_eq_iff)
  apply (case_tac "c=ca")
  apply simp_all[2]
  apply rule
  apply (perm_simp)
  apply (simp add: eqvt_def)
  apply (simp add: fresh_def)
  apply (rule contra_subsetD[OF supp_fun_app])
  back
  apply (simp add: supp_fun_eqvt lt.supp supp_at_base)
oops


end



