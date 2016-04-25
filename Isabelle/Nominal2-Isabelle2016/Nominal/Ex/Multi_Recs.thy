theory Multi_Recs
imports "../Nominal2"
begin

(* 
  multiple recursive binders

  example 7 from Peter Sewell's bestiary 

*)

atom_decl name

nominal_datatype multi_recs: exp =
  Var name
| Unit
| Pair exp exp
| LetRec l::"lrbs" e::"exp"  binds (set) "bs l" in l e
and lrb =
  Assign name exp
and lrbs =
  Single lrb
| More lrb lrbs
binder
  b :: "lrb \<Rightarrow> atom set" and
  bs :: "lrbs \<Rightarrow> atom set"
where
  "b (Assign x e) = {atom x}"
| "bs (Single a) = b a"
| "bs (More a as) = (b a) \<union> (bs as)"

thm multi_recs.distinct
thm multi_recs.induct
thm multi_recs.inducts
thm multi_recs.exhaust
thm multi_recs.fv_defs
thm multi_recs.bn_defs
thm multi_recs.perm_simps
thm multi_recs.eq_iff
thm multi_recs.fv_bn_eqvt
thm multi_recs.size_eqvt
thm multi_recs.supports
thm multi_recs.fsupp
thm multi_recs.supp

thm multi_recs.bn_defs
thm multi_recs.permute_bn
thm multi_recs.perm_bn_alpha
thm multi_recs.perm_bn_simps
thm multi_recs.bn_finite

end



