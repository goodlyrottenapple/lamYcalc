
theory Datatypes
imports "../Nominal2" 
begin

(* 
  plain nominal_datatype definition without an 
  atom_decl - example by John Matthews
*)

nominal_datatype 'a::fs Maybe = 
  Nothing 
| Just 'a


thm Maybe.distinct
thm Maybe.induct
thm Maybe.exhaust
thm Maybe.strong_exhaust
thm Maybe.fv_defs
thm Maybe.bn_defs
thm Maybe.perm_simps
thm Maybe.eq_iff
thm Maybe.fv_bn_eqvt
thm Maybe.size_eqvt
thm Maybe.supp

(*
  using a datatype inside a nominal_datatype

  the datatype needs to be shown to be an instance
  of the pure class (this is usually trivial)
*)

atom_decl name

datatype foo = Foo | Bar


instantiation foo :: pure
begin

definition
  "p \<bullet> (f::foo) = f"

instance
apply(default)
apply(simp_all add:  permute_foo_def)
done

end


nominal_datatype baz =
  Baz x::name t::foo   binds x in t



thm baz.distinct
thm baz.induct
thm baz.exhaust
thm baz.strong_exhaust
thm baz.fv_defs
thm baz.bn_defs
thm baz.perm_simps
thm baz.eq_iff
thm baz.fv_bn_eqvt
thm baz.size_eqvt
thm baz.supp

(*
  a nominal datatype with a set argument of
  pure type
*)
  
nominal_datatype set_ty = 
  Set_ty "nat set"
| Fun "nat \<Rightarrow> nat"
| Var "name"
| Lam x::"name" t::"set_ty" binds x in t
thm meta_eq_to_obj_eq
thm set_ty.distinct
thm set_ty.induct
thm set_ty.exhaust
thm set_ty.strong_exhaust
thm set_ty.fv_defs
thm set_ty.bn_defs
thm set_ty.perm_simps
thm set_ty.eq_iff
thm set_ty.fv_bn_eqvt
thm set_ty.size_eqvt
thm set_ty.supp



end



