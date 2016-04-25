theory NoneExamples
imports "../Nominal2"
begin

text {*
  These examples are not covered by our binding 
  specification.
*}

atom_decl name

text {* 
  "Weirdo" example from Peter Sewell's bestiary. 

  p2 occurs in two bodies
*}

(*
nominal_datatype weird =
  Foo_var "name"
| Foo_pair "weird" "weird" 
| Foo x::"name" y::"name" p1::"weird" p2::"weird" p3::"weird"
    binds x in p1 p2, 
    binds y in p2 p3
*)

text {* 
  This example binds bound names and therefore the 
  fv-function is not respectful - the proof just fails.
*}

(*
nominal_datatype trm =
  Var "name"
| Lam x::"name" t::"trm"         binds x in t
| Let left::"trm" right::"trm"   binds (set) "bv left" in right
binder
  bv
where
  "bv (Var n) = {}"
| "bv (Lam n t) = {atom n} \<union> bv t"
| "bv (Let l r) = bv l \<union> bv r"
*)

text {* 
  This example uses "-" in the binding function; 
  at the moment this is unsupported 
*}

(*
nominal_datatype trm' =
  Var "name"
| Lam l::"name" r::"trm'"   binds l in r
| Let l::"trm'" r::"trm'"   binds (set) "bv' l" in r
binder
  bv'
where
  "bv' (Var n) = {atom n}"
| "bv' (Lam n t) = bv' t - {atom n}"
| "bv' (Let l r) = bv' l \<union> bv' r"
*)

text {* 
  Again this example binds bound names - so is not respectful
*}

(*
nominal_datatype trm =
  Var "name"
| Lam n::"name" l::"trm" binds n in l
and bla =
  Bla f::"trm" s::"trm" binds (set) "bv f" in s
binder
  bv :: "trm \<Rightarrow> atom set"
where
  "bv (Var x) = {}"
| "bv (Lam x b) = {atom x}"
*)

text {*
  This example has mal-formed deep recursive binders.

  - Bla1: recursive deep binder used twice
  - Bla2: deep binder used recursively and non-recursively
  - Bla3: x used in recursive deep binder and somewhere else
*}

(*
nominal_datatype trm =
  Var "name"
and bla =
  App "trm" "trm"
| Bla1 f::"trm" s1::"trm" s2::"trm"  binds "bv f" in s1 f,  binds "bv f" in s2 f
| Bla2 f::"trm" s1::"trm" s2::"trm"  binds "bv f" in s1,  binds "bv f" in s2 f
| Bla3 f::"trm" s1::"trm" s2::"trm" x::"name" y::"name" binds "bv f" x in s1 f, binds y x in s2 
binder
  bv :: "trm \<Rightarrow> atom list"
where
  "bv (Var a) = [atom a]"
*)


end



