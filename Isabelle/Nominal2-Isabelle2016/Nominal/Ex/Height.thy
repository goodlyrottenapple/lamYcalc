theory Height
  imports "Lambda"
begin

text {*  
  A small problem suggested by D. Wang. It shows how
  the height of a lambda-terms behaves under substitution.
*}


lemma height_ge_one: 
  shows "1 \<le> (height e)"
by (induct e rule: lam.induct) 
   (simp_all)

theorem height_subst:
  shows "height (e[x::=e']) \<le> height e - 1 + height e'"
proof (nominal_induct e avoiding: x e' rule: lam.strong_induct)
  case (Var y)
  have "1 \<le> height e'" using height_ge_one by simp
  then show "height (Var y[x::=e']) \<le> height (Var y) - 1 + height e'" by simp
next
  case (Lam y e1)
  have ih: "height (e1[x::=e']) \<le> height e1 - 1 + height e'" by fact
  moreover
  have vc: "atom y \<sharp> x" "atom y \<sharp> e'" by fact+ (* usual variable convention *)
  ultimately show "height ((Lam [y].e1)[x::=e']) \<le> height (Lam [y].e1) - 1 + height e'" by simp
next    
  case (App e1 e2)
  have ih1: "height (e1[x::=e']) \<le> (height e1) - 1 + height e'" 
  and  ih2: "height (e2[x::=e']) \<le> (height e2) - 1 + height e'" by fact+
  then show "height ((App e1 e2)[x::=e']) \<le> height (App e1 e2) - 1 + height e'" by simp  
qed

end
