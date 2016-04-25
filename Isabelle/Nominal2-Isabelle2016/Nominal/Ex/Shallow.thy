theory Shallow
imports "../Nominal2" 
begin

(* 
  Various shallow binders
*)

atom_decl name

text {* binding lists of names *}

nominal_datatype trm1 =
  Var1 "name"
| App1 "trm1" "trm1"
| Lam1 xs::"name list" t::"trm1" binds xs in t

thm trm1.strong_exhaust


text {* binding a finite set of names *}

nominal_datatype trm2 =
  Var2 "name"
| App2 "trm2" "trm2"
| Lam2 xs::"name fset" t::"trm2" binds (set) xs in t

thm trm2.strong_exhaust

text {* restricting a finite set of names *}

nominal_datatype trm3 =
  Var3 "name"
| App3 "trm3" "trm3"
| Lam3 xs::"name fset" t::"trm3" binds (set+) xs in t

thm trm3.eq_iff

end



