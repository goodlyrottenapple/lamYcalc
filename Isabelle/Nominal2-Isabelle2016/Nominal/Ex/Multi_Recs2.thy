theory Multi_Recs2
imports "../Nominal2"
begin

(* 
  multiple recursive binders - multiple letrecs with multiple 
  clauses for each functions

  example 8 from Peter Sewell's bestiary (originally due
  to James Cheney) 

*)

atom_decl name

nominal_datatype fun_recs: exp =
  Var name
| Unit 
| Pair exp exp
| LetRec l::lrbs e::exp binds (set) "b_lrbs l" in l e
and fnclause =
  K x::name p::pat f::exp binds (set) "b_pat p" in f
and fnclauses =
  S fnclause
| ORs fnclause fnclauses
and lrb =
  Clause fnclauses
and lrbs =
  Single lrb
| More lrb lrbs
and pat =
  PVar name
| PUnit
| PPair pat pat
binder
  b_lrbs :: "lrbs \<Rightarrow> atom set" and
  b_pat :: "pat \<Rightarrow> atom set" and
  b_fnclauses :: "fnclauses \<Rightarrow> atom set" and
  b_fnclause :: "fnclause \<Rightarrow> atom set" and
  b_lrb :: "lrb \<Rightarrow> atom set"
where
  "b_lrbs (Single l) = b_lrb l"
| "b_lrbs (More l ls) = b_lrb l \<union> b_lrbs ls"
| "b_pat (PVar x) = {atom x}"
| "b_pat (PUnit) = {}"
| "b_pat (PPair p1 p2) = b_pat p1 \<union> b_pat p2"
| "b_fnclauses (S fc) = (b_fnclause fc)"
| "b_fnclauses (ORs fc fcs) = (b_fnclause fc) \<union> (b_fnclauses fcs)"
| "b_lrb (Clause fcs) = (b_fnclauses fcs)"
| "b_fnclause (K x pat exp) = {atom x}"


thm fun_recs.permute_bn
thm fun_recs.perm_bn_alpha
thm fun_recs.perm_bn_simps
thm fun_recs.bn_finite
thm fun_recs.inducts
thm fun_recs.distinct
thm fun_recs.induct
thm fun_recs.inducts
thm fun_recs.exhaust
thm fun_recs.fv_defs
thm fun_recs.bn_defs
thm fun_recs.perm_simps
thm fun_recs.eq_iff
thm fun_recs.fv_bn_eqvt
thm fun_recs.size_eqvt
thm fun_recs.supports
thm fun_recs.fsupp
thm fun_recs.supp

thm fun_recs.distinct
thm fun_recs.induct
thm fun_recs.inducts
thm fun_recs.exhaust
thm fun_recs.fv_defs
thm fun_recs.bn_defs
thm fun_recs.perm_simps
thm fun_recs.eq_iff
thm fun_recs.fv_bn_eqvt
thm fun_recs.size_eqvt
thm fun_recs.supports
thm fun_recs.fsupp
thm fun_recs.supp

lemma
  fixes c::"'a::fs"
  assumes "\<And>name c. P1 c (Var name)"
  and "\<And>c. P1 c Unit"
  and "\<And>exp1 exp2 c. \<lbrakk>\<And>c. P1 c exp1; \<And>c. P1 c exp2\<rbrakk> \<Longrightarrow> P1 c (Multi_Recs2.Pair exp1 exp2)"
  and "\<And>lrbs exp c. \<lbrakk>b_lrbs lrbs \<sharp>* c; \<And>c. P5 c lrbs; \<And>c. P1 c exp\<rbrakk> \<Longrightarrow> P1 c (LetRec lrbs exp)"
  and "\<And>name pat exp c. \<lbrakk>b_pat pat \<sharp>* c; \<And>c. P6 c pat; \<And>c. P1 c exp\<rbrakk> \<Longrightarrow> P2 c (K name pat exp)"
  and "\<And>fnclause c. (\<And>c. P2 c fnclause) \<Longrightarrow> P3 c (S fnclause)"
  and "\<And>fnclause fnclauses c. \<lbrakk>\<And>c. P2 c fnclause; \<And>c. P3 c fnclauses\<rbrakk> \<Longrightarrow> 
    P3 c (ORs fnclause fnclauses)"
  and "\<And>fnclauses c. (\<And>c. P3 c fnclauses) \<Longrightarrow> P4 c (Clause fnclauses)"
  and "\<And>lrb c. (\<And>c. P4 c lrb) \<Longrightarrow> P5 c (Single lrb)"
  and "\<And>lrb lrbs c. \<lbrakk>\<And>c. P4 c lrb; \<And>c. P5 c lrbs\<rbrakk> \<Longrightarrow> P5 c (More lrb lrbs)"
  and "\<And>name c. P6 c (PVar name)"
  and "\<And>c. P6 c PUnit"
  and "\<And>pat1 pat2 c. \<lbrakk>\<And>c. P6 c pat1; \<And>c. P6 c pat2\<rbrakk> \<Longrightarrow> P6 c (PPair pat1 pat2)"
  shows "P1 c exp" and "P2 c fnclause" and "P3 c fnclauses" and "P4 c lrb" and "P5 c lrbs" and "P6 c pat"
  apply(raw_tactic {* Induction_Schema.induction_schema_tac @{context} @{thms assms} *})
  apply(rule_tac y="exp" and c="c" in fun_recs.strong_exhaust(1))
  apply(simp_all)[4]
  apply(rule_tac ya="fnclause" and c="c" in fun_recs.strong_exhaust(2))
  apply(blast)
  apply(rule_tac yb="fnclauses" in fun_recs.strong_exhaust(3))
  apply(blast)
  apply(blast)
  apply(rule_tac yc="lrb" in fun_recs.strong_exhaust(4))
  apply(blast)
  apply(rule_tac yd="lrbs" in fun_recs.strong_exhaust(5))
  apply(blast)
  apply(blast)
  apply(rule_tac ye="pat" in fun_recs.strong_exhaust(6))
  apply(blast)
  apply(blast)
  apply(blast)
  apply(tactic {* prove_termination_ind @{context} 1 *})
  apply(simp_all add: fun_recs.size)
  done

end



