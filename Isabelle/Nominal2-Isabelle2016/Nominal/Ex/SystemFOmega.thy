theory SystemFOmega
imports "../Nominal2"
begin

text {*
  System from the F-ing paper by Rossberg, Russo and 
  Dreyer, TLDI'10
*}


atom_decl var
atom_decl tvar
atom_decl label

nominal_datatype kind =
  \<Omega> 
| KFun kind kind

nominal_datatype ty =
  TVar tvar
| TFun ty ty
| TAll a::tvar kind t::ty  binds a in t
| TEx  a::tvar kind t::ty  binds a in t
| TLam a::tvar kind t::ty  binds a in t
| TApp ty ty
| TRec trec
and trec =
  TRNil
| TRCons label ty trec 

nominal_datatype trm =
  Var var
| Lam x::var ty t::trm  binds x in t
| App trm trm
| Dot trm label
| LAM a::tvar kind t::trm  binds a in t
| APP trm ty
| Pack ty trm
| Unpack a::tvar x::var trm t::trm  binds a x in t
| Rec rec 
and rec =
  RNil
| RCons label trm rec

thm ty_trec.distinct
thm ty_trec.induct
thm ty_trec.inducts
thm ty_trec.exhaust 
thm ty_trec.strong_exhaust
thm ty_trec.fv_defs
thm ty_trec.bn_defs
thm ty_trec.perm_simps
thm ty_trec.eq_iff
thm ty_trec.fv_bn_eqvt
thm ty_trec.size_eqvt
thm ty_trec.supports
thm ty_trec.fsupp
thm ty_trec.supp
thm ty_trec.fresh

thm trm_rec.distinct
thm trm_rec.induct
thm trm_rec.inducts
thm trm_rec.exhaust
thm trm_rec.strong_exhaust
thm trm_rec.fv_defs
thm trm_rec.bn_defs
thm trm_rec.perm_simps
thm trm_rec.eq_iff
thm trm_rec.fv_bn_eqvt
thm trm_rec.size_eqvt
thm trm_rec.supports
thm trm_rec.fsupp
thm trm_rec.supp
thm trm_rec.fresh

end




