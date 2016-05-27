theory TypeVarsTest
imports "../Nominal2" 
begin

atom_decl var

ML {* trace := true *}
declare [[ML_print_depth = 1000]]

nominal_datatype exp =
          Var var
        | App exp var
        | LetA as::assn body::exp binds "bn as" in "body" "as"
        | Lam x::var body::exp binds x in body
        and assn =
          ANil | ACons var exp assn
        binder
          bn
        where "bn ANil = []" | "bn (ACons x t as) = (atom x) # (bn as)"

(* NEEDS FIXING
nominal_datatype ('ann::fs) exp2 =
  Var2 var
| App2 "'ann exp2" var
| LetA2 as::"'ann assn2" body::"'ann exp2" binds "bn2 as" in body as
| Lam2 x::var body::"'ann exp2" binds x in body
and ('ann::fs) assn2 =
  ANil2 
| ACons2 var "'ann exp2" 'ann "'ann assn2"
binder
  bn2 :: "('ann::fs) assn2 \<Rightarrow> atom list"
where 
  "bn2 ANil2 = []" 
| "bn2 (ACons2 x a t as) = (atom x) # (bn2 as)"
*)

(* a nominal datatype with type variables and sorts *)


(* the sort constraints need to be attached to the  *)
(* first occurence of the type variables on the     *)
(* right-hand side                                  *)

atom_decl name

class s1
class s2

instance nat :: s1 ..
instance int :: s2 .. 

nominal_datatype ('a::s1, 'b::s2, 'c::at) lam =
  Var3 "name"
| App3 "('a, 'b, 'c) lam" "('a, 'b, 'c) lam"
| Lam3 x::"name" l::"('a, 'b, 'c) lam"  binds x in l
| Foo3 "'a" "'b"
| Bar3 x::"'c" l::"('a, 'b, 'c) lam"  binds x in l   (* Bar binds a polymorphic atom *)

term Foo
term Bar

thm lam.supp lam.fresh
thm lam.distinct
thm lam.induct
thm lam.exhaust 
thm lam.strong_exhaust
thm lam.fv_defs
thm lam.bn_defs
thm lam.perm_simps
thm lam.eq_iff
thm lam.fv_bn_eqvt
thm lam.size_eqvt


nominal_datatype ('alpha, 'beta, 'gamma) psi =
  PsiNil
| Output "'alpha" "'alpha" "('alpha, 'beta, 'gamma) psi" 

thm psi.supp psi.fresh

nominal_datatype 'a foo = 
  Node x::"name" f::"'a foo" binds x in f
| Leaf "'a"

term "Leaf"



end



