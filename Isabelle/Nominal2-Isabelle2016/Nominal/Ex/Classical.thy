theory Classical
imports "../Nominal2"
begin


(* example from Urban's PhD *)

atom_decl name
atom_decl coname

nominal_datatype trm =
  Ax "name" "coname"
| Cut c::"coname" t1::"trm" n::"name" t2::"trm"             binds n in t1, binds c in t2  
     ("Cut <_>._ '(_')._" [100,100,100,100] 100)
| NotR n::"name" t::"trm" "coname"                            binds n in t
     ("NotR '(_')._ _" [100,100,100] 100)
| NotL c::"coname" t::"trm" "name"                            binds c in t   
     ("NotL <_>._ _" [100,100,100] 100)
| AndR c1::"coname" t1::"trm" c2::"coname" t2::"trm" "coname" binds c1 in t1, binds c2 in t2
     ("AndR <_>._ <_>._ _" [100,100,100,100,100] 100)
| AndL1 n::"name" t::"trm" "name"                             binds n in t
     ("AndL1 '(_')._ _" [100,100,100] 100)
| AndL2 n::"name" t::"trm" "name"                             binds n in t
     ("AndL2 '(_')._ _" [100,100,100] 100)
| OrR1 c::"coname" t::"trm" "coname"                          binds c in t             
     ("OrR1 <_>._ _" [100,100,100] 100)
| OrR2 c::"coname" t::"trm" "coname"                          binds c in t     
     ("OrR2 <_>._ _" [100,100,100] 100)
| OrL n1::"name" t1::"trm" n2::"name" t2::"trm" "name"        binds n1 in t1, binds n2 in t2       
     ("OrL '(_')._ '(_')._ _" [100,100,100,100,100] 100)
| ImpL c::"coname" t1::"trm" n::"name" t2::"trm" "name"       binds c in t1, binds n in t2
     ("ImpL <_>._ '(_')._ _" [100,100,100,100,100] 100)
| ImpR n::"name" c::"coname" t::"trm" "coname"                binds n c in t
     ("ImpR '(_').<_>._ _" [100,100,100,100] 100)

thm trm.distinct
thm trm.induct
thm trm.exhaust
thm trm.strong_exhaust
thm trm.strong_exhaust[simplified]
thm trm.fv_defs
thm trm.bn_defs
thm trm.perm_simps
thm trm.eq_iff
thm trm.fv_bn_eqvt
thm trm.size_eqvt
thm trm.supp
thm trm.supp[simplified]

nominal_function 
  crename :: "trm \<Rightarrow> coname \<Rightarrow> coname \<Rightarrow> trm"  ("_[_\<turnstile>c>_]" [100,100,100] 100) 
where
  "(Ax x a)[d\<turnstile>c>e] = (if a=d then Ax x e else Ax x a)" 
| "atom a \<sharp> (d, e) \<Longrightarrow> (Cut <a>.M (x).N)[d\<turnstile>c>e] = Cut <a>.(M[d\<turnstile>c>e]) (x).(N[d\<turnstile>c>e])" 
| "(NotR (x).M a)[d\<turnstile>c>e] = (if a=d then NotR (x).(M[d\<turnstile>c>e]) e else NotR (x).(M[d\<turnstile>c>e]) a)" 
| "atom a \<sharp> (d, e) \<Longrightarrow> (NotL <a>.M x)[d\<turnstile>c>e] = (NotL <a>.(M[d\<turnstile>c>e]) x)" 
| "\<lbrakk>atom a \<sharp> (d, e); atom b \<sharp> (d, e)\<rbrakk> \<Longrightarrow> (AndR <a>.M <b>.N c)[d\<turnstile>c>e] = 
          (if c=d then AndR <a>.(M[d\<turnstile>c>e]) <b>.(N[d \<turnstile>c>e]) e else AndR <a>.(M[d\<turnstile>c>e]) <b>.(N[d\<turnstile>c>e]) c)" 
| "(AndL1 (x).M y)[d\<turnstile>c>e] = AndL1 (x).(M[d\<turnstile>c>e]) y"
| "(AndL2 (x).M y)[d\<turnstile>c>e] = AndL2 (x).(M[d\<turnstile>c>e]) y"
| "atom a \<sharp> (d, e) \<Longrightarrow> (OrR1 <a>.M b)[d\<turnstile>c>e] = 
          (if b=d then OrR1 <a>.(M[d\<turnstile>c>e]) e else OrR1 <a>.(M[d\<turnstile>c>e]) b)"
| "atom a \<sharp> (d, e) \<Longrightarrow> (OrR2 <a>.M b)[d\<turnstile>c>e] = 
          (if b=d then OrR2 <a>.(M[d\<turnstile>c>e]) e else OrR2 <a>.(M[d\<turnstile>c>e]) b)"
| "(OrL (x).M (y).N z)[d\<turnstile>c>e] = OrL (x).(M[d\<turnstile>c>e]) (y).(N[d\<turnstile>c>e]) z"
| "atom a \<sharp> (d, e) \<Longrightarrow> (ImpR (x).<a>.M b)[d\<turnstile>c>e] = 
          (if b=d then ImpR (x).<a>.(M[d\<turnstile>c>e]) e else ImpR (x).<a>.(M[d\<turnstile>c>e]) b)"
| "atom a \<sharp> (d, e) \<Longrightarrow> (ImpL <a>.M (x).N y)[d\<turnstile>c>e] = ImpL <a>.(M[d\<turnstile>c>e]) (x).(N[d\<turnstile>c>e]) y"
  apply(simp only: eqvt_def)
  apply(simp only: crename_graph_aux_def)
  apply (rule, perm_simp, rule)
  apply(rule TrueI)
  -- "covered all cases"
  apply(case_tac x)
  apply(rule_tac y="a" and c="(b, c)" in trm.strong_exhaust)
  apply (simp_all add: fresh_star_def)[12]
  apply(metis)+
  -- "compatibility"
  apply(all_trivials)
  using [[simproc del: alpha_lst]]
  apply(simp_all)
  apply(rule conjI)
  apply(elim conjE)
  apply(erule_tac c="(da,ea)" in Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(clarify)
  apply(simp add: eqvt_at_def)
  apply(simp add: atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(elim conjE)
  apply(erule_tac c="(da,ea)" in Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(elim conjE)
  apply(subgoal_tac "eqvt_at crename_sumC (M, da, ea)")
  apply(subgoal_tac "eqvt_at crename_sumC (Ma, da, ea)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(elim conjE)
  apply(erule_tac c="(da,ea)" in Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(rule conjI)
  apply(elim conjE)
  apply(subgoal_tac "eqvt_at crename_sumC (M, da, ea)")
  apply(subgoal_tac "eqvt_at crename_sumC (Ma, da, ea)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(erule conjE)+
  apply(subgoal_tac "eqvt_at crename_sumC (N, da, ea)")
  apply(subgoal_tac "eqvt_at crename_sumC (Na, da, ea)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(elim conjE)
  apply(erule_tac c="(da,ea)" in Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(elim conjE)
  apply(erule_tac c="(da,ea)" in Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(elim conjE)
  apply(subgoal_tac "eqvt_at crename_sumC (M, da, ea)")
  apply(subgoal_tac "eqvt_at crename_sumC (Ma, da, ea)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(erule conjE)+
  apply(subgoal_tac "eqvt_at crename_sumC (M, da, ea)")
  apply(subgoal_tac "eqvt_at crename_sumC (Ma, da, ea)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(rule conjI)
  apply(erule conjE)+
  apply(subgoal_tac "eqvt_at crename_sumC (M, da, ea)")
  apply(subgoal_tac "eqvt_at crename_sumC (Ma, da, ea)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(erule conjE)+
  apply(subgoal_tac "eqvt_at crename_sumC (N, da, ea)")
  apply(subgoal_tac "eqvt_at crename_sumC (Na, da, ea)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  defer
  apply(erule conjE)+
  apply(rule conjI)
  apply(subgoal_tac "eqvt_at crename_sumC (M, da, ea)")
  apply(subgoal_tac "eqvt_at crename_sumC (Ma, da, ea)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)  
  apply(subgoal_tac "eqvt_at crename_sumC (N, da, ea)")
  apply(subgoal_tac "eqvt_at crename_sumC (Na, da, ea)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: eqvt_at_def)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(subgoal_tac "eqvt_at crename_sumC (M, da, ea)")
  apply(subgoal_tac "eqvt_at crename_sumC (Ma, da, ea)")
  apply(erule conjE)+
  apply(erule Abs_lst_fcb2)
  apply(simp add: Abs_fresh_star)
  apply(simp add: Abs_fresh_star)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  done

nominal_termination (eqvt)
  by lexicographic_order

nominal_function 
  nrename :: "trm \<Rightarrow> name \<Rightarrow> name \<Rightarrow> trm"      ("_[_\<turnstile>n>_]" [100,100,100] 100) 
where
  "(Ax x a)[u\<turnstile>n>v] = (if x=u then Ax v a else Ax x a)" 
| "atom x \<sharp> (u, v) \<Longrightarrow> (Cut <a>.M (x).N)[u\<turnstile>n>v] = Cut <a>.(M[u\<turnstile>n>v]) (x).(N[u\<turnstile>n>v])" 
| "atom x \<sharp> (u, v) \<Longrightarrow> (NotR (x).M a)[u\<turnstile>n>v] = NotR (x).(M[u\<turnstile>n>v]) a" 
| "(NotL <a>.M x)[u\<turnstile>n>v] = (if x=u then NotL <a>.(M[u\<turnstile>n>v]) v else NotL <a>.(M[u\<turnstile>n>v]) x)" 
| "(AndR <a>.M <b>.N c)[u\<turnstile>n>v] = AndR <a>.(M[u\<turnstile>n>v]) <b>.(N[u\<turnstile>n>v]) c" 
| "atom x \<sharp> (u, v) \<Longrightarrow> (AndL1 (x).M y)[u\<turnstile>n>v] = 
          (if y=u then AndL1 (x).(M[u\<turnstile>n>v]) v else AndL1 (x).(M[u\<turnstile>n>v]) y)"
| "atom x \<sharp> (u, v) \<Longrightarrow> (AndL2 (x).M y)[u\<turnstile>n>v] = 
          (if y=u then AndL2 (x).(M[u\<turnstile>n>v]) v else AndL2 (x).(M[u\<turnstile>n>v]) y)"
| "(OrR1 <a>.M b)[u\<turnstile>n>v] = OrR1 <a>.(M[u\<turnstile>n>v]) b"
| "(OrR2 <a>.M b)[u\<turnstile>n>v] = OrR2 <a>.(M[u\<turnstile>n>v]) b"
| "\<lbrakk>atom x \<sharp> (u, v); atom y \<sharp> (u, v)\<rbrakk> \<Longrightarrow> (OrL (x).M (y).N z)[u\<turnstile>n>v] = 
        (if z=u then OrL (x).(M[u\<turnstile>n>v]) (y).(N[u\<turnstile>n>v]) v else OrL (x).(M[u\<turnstile>n>v]) (y).(N[u\<turnstile>n>v]) z)"
| "atom x \<sharp> (u, v) \<Longrightarrow> (ImpR (x).<a>.M b)[u\<turnstile>n>v] = ImpR (x).<a>.(M[u\<turnstile>n>v]) b"
| "atom x \<sharp> (u, v) \<Longrightarrow> (ImpL <a>.M (x).N y)[u\<turnstile>n>v] = 
        (if y=u then ImpL <a>.(M[u\<turnstile>n>v]) (x).(N[u\<turnstile>n>v]) v else ImpL <a>.(M[u\<turnstile>n>v]) (x).(N[u\<turnstile>n>v]) y)"
  apply(simp only: eqvt_def)
  apply(simp only: nrename_graph_aux_def)
  apply (rule, perm_simp, rule)
  apply(rule TrueI)
  -- "covered all cases"
  apply(case_tac x)
  apply(rule_tac y="a" and c="(b, c)" in trm.strong_exhaust)
  apply (simp_all add: fresh_star_def)[12]
  apply(metis)+
  -- "compatibility"
  using [[simproc del: alpha_lst]]
  apply(simp_all)
  apply(rule conjI)
  apply(elim conjE)
  apply(erule_tac c="(ua,va)" in Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(elim conjE)
  apply(erule_tac c="(ua,va)" in Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(elim conjE)
  apply(erule_tac c="(ua,va)" in Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(elim conjE)
  apply(subgoal_tac "eqvt_at nrename_sumC (M, ua, va)")
  apply(subgoal_tac "eqvt_at nrename_sumC (Ma, ua, va)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(elim conjE)
  apply(rule conjI)
  apply(subgoal_tac "eqvt_at nrename_sumC (M, ua, va)")
  apply(subgoal_tac "eqvt_at nrename_sumC (Ma, ua, va)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(subgoal_tac "eqvt_at nrename_sumC (N, ua, va)")
  apply(subgoal_tac "eqvt_at nrename_sumC (Na, ua, va)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(elim conjE)
  apply(subgoal_tac "eqvt_at nrename_sumC (M, ua, va)")
  apply(subgoal_tac "eqvt_at nrename_sumC (Ma, ua, va)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(elim conjE)+
  apply(subgoal_tac "eqvt_at nrename_sumC (M, ua, va)")
  apply(subgoal_tac "eqvt_at nrename_sumC (Ma, ua, va)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(elim conjE)+
  apply(erule_tac c="(ua,va)" in Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(elim conjE)
  apply(erule_tac c="(ua,va)" in Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(elim conjE)
  apply(rule conjI)
  apply(subgoal_tac "eqvt_at nrename_sumC (M, ua, va)")
  apply(subgoal_tac "eqvt_at nrename_sumC (Ma, ua, va)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(subgoal_tac "eqvt_at nrename_sumC (N, ua, va)")
  apply(subgoal_tac "eqvt_at nrename_sumC (Na, ua, va)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(erule conjE)+
  apply(erule Abs_lst_fcb2)
  apply(simp add: Abs_fresh_star)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(erule conjE)+
  apply(rule conjI)
  apply(subgoal_tac "eqvt_at nrename_sumC (M, ua, va)")
  apply(subgoal_tac "eqvt_at nrename_sumC (Ma, ua, va)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  apply(subgoal_tac "eqvt_at nrename_sumC (N, ua, va)")
  apply(subgoal_tac "eqvt_at nrename_sumC (Na, ua, va)")
  apply(erule Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_at_base fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(blast)
  apply(blast)
  done

nominal_termination (eqvt)
  by lexicographic_order

thm crename.eqvt nrename.eqvt


nominal_function 
  substn :: "trm \<Rightarrow> name   \<Rightarrow> coname \<Rightarrow> trm \<Rightarrow> trm" ("_{_:=<_>._}" [100,100,100,100] 100) 
where
  "(Ax x a){y:=<c>.P} = (if x=y then Cut <c>.P (y).Ax y a else Ax x a)" 
| "\<lbrakk>atom a \<sharp> (c, P); atom x \<sharp> (y, P)\<rbrakk> \<Longrightarrow> (Cut <a>.M (x).N){y:=<c>.P} = 
    (if M=Ax y a then Cut <c>.P (x).(N{y:=<c>.P}) else Cut <a>.(M{y:=<c>.P}) (x).(N{y:=<c>.P}))" 
| "atom x\<sharp> (y, P) \<Longrightarrow> (NotR (x).M a){y:=<c>.P} = NotR (x).(M{y:=<c>.P}) a" 
| "\<lbrakk>atom a\<sharp> (c, P); atom x' \<sharp> (M, y, P)\<rbrakk> \<Longrightarrow> (NotL <a>.M x){y:=<c>.P} = 
    (if x=y then Cut <c>.P (x').NotL <a>.(M{y:=<c>.P}) x' else NotL <a>.(M{y:=<c>.P}) x)"
| "\<lbrakk>atom a \<sharp> (c, P); atom b \<sharp> (c, P)\<rbrakk> \<Longrightarrow> 
    (AndR <a>.M <b>.N d){y:=<c>.P} = AndR <a>.(M{y:=<c>.P}) <b>.(N{y:=<c>.P}) d" 
| "atom x \<sharp> (y, P) \<Longrightarrow> (AndL1 (x).M z){y:=<c>.P} = 
    (if z=y then Cut <c>.P (z').AndL1 (x).(M{y:=<c>.P}) z' else AndL1 (x).(M{y:=<c>.P}) z)"
| "atom x \<sharp> (y, P) \<Longrightarrow> (AndL2 (x).M z){y:=<c>.P} = 
    (if z=y then Cut <c>.P (z').AndL2 (x).(M{y:=<c>.P}) z' else AndL2 (x).(M{y:=<c>.P}) z)"
| "atom a \<sharp> (c, P) \<Longrightarrow> (OrR1 <a>.M b){y:=<c>.P} = OrR1 <a>.(M{y:=<c>.P}) b"
| "atom a \<sharp> (c, P) \<Longrightarrow> (OrR2 <a>.M b){y:=<c>.P} = OrR2 <a>.(M{y:=<c>.P}) b"
| "\<lbrakk>atom x \<sharp> (y, P); atom u \<sharp> (y, P)\<rbrakk> \<Longrightarrow> (OrL (x).M (u).N z){y:=<c>.P} = 
     (if z=y then Cut <c>.P (z').OrL (x).(M{y:=<c>.P}) (u).(N{y:=<c>.P}) z' 
      else OrL (x).(M{y:=<c>.P}) (u).(N{y:=<c>.P}) z)"
| "\<lbrakk>atom a \<sharp> (c, P); atom x \<sharp> (y, P)\<rbrakk> \<Longrightarrow> (ImpR (x).<a>.M b){y:=<c>.P} = ImpR (x).<a>.(M{y:=<c>.P}) b"
| "\<lbrakk>atom a \<sharp> (c, P); atom x \<sharp> (y, P)\<rbrakk> \<Longrightarrow> (ImpL <a>.M (x).N z){y:=<c>.P} = 
     (if y=z then Cut <c>.P (z').ImpL <a>.(M{y:=<c>.P}) (x).(N{y:=<c>.P}) z' 
      else ImpL <a>.(M{y:=<c>.P}) (x).(N{y:=<c>.P}) z)"
  apply(simp only: eqvt_def)
  apply(simp only: substn_graph_aux_def)
  apply (rule, perm_simp, rule)
  apply(rule TrueI)
  -- "covered all cases"
  apply(case_tac x)
  apply(rule_tac y="a" and c="(b, c, d)" in trm.strong_exhaust)
  apply (simp_all add: fresh_star_def fresh_Pair)[12]
  apply(metis)
  oops

end



