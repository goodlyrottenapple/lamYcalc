theory CoreHaskell2
imports "../Nominal2"
begin

(* Core Haskell by John Matthews *)

atom_decl var
atom_decl cvar
atom_decl tvar


nominal_datatype kinds:
    Kind =
       Klifted
     | Kunlifted
     | Kopen
     | Karrow Kind Kind
     | Keq Ty Ty
and Ty =
       Tvar tvar
     | Tcon string
     | Tapp Ty Ty
     | Tforall pb::PBind ty::Ty   binds "bind_pb pb" in ty
and PBind =
  Pbind tvar Kind
binder
  bind_pb
where
  "bind_pb (Pbind tv k) = [atom tv]"

nominal_datatype expressions:
    Bind =
       Vb var Ty
     | Tb tvar Kind
and Exp =
       Var var
     | Dcon string
     | App Exp Exp
     | Appt Exp Ty
     | Lam b::Bind e::Exp binds "bind_b b" in e
binder
  bind_b
where
  "bind_b (Vb v ty) = [atom v]"
| "bind_b (Tb tv kind) = [atom tv]"

thm kinds.distinct
thm kinds.induct
thm kinds.inducts
thm kinds.exhaust
thm kinds.strong_exhaust
thm kinds.fv_defs
thm kinds.bn_defs
thm kinds.perm_simps
thm kinds.eq_iff
thm kinds.fv_bn_eqvt
thm kinds.size_eqvt
thm kinds.supports
thm kinds.fsupp
thm kinds.supp
thm kinds.fresh

thm expressions.distinct
thm expressions.induct
thm expressions.inducts
thm expressions.exhaust
thm expressions.fv_defs
thm expressions.bn_defs
thm expressions.perm_simps
thm expressions.eq_iff
thm expressions.fv_bn_eqvt
thm expressions.size_eqvt
thm expressions.supports
thm expressions.fsupp
thm expressions.supp
thm expressions.fresh

end

