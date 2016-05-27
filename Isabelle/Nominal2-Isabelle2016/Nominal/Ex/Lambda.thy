theory Lambda
imports 
  "../Nominal2"
  "~~/src/HOL/Library/Monad_Syntax"
begin

lemma perm_commute: 
  "a \<sharp> p \<Longrightarrow> a' \<sharp> p \<Longrightarrow> (a \<rightleftharpoons> a') + p = p + (a \<rightleftharpoons> a')"
apply(rule plus_perm_eq)
apply(simp add: supp_swap fresh_def)
done

atom_decl name

thm obtain_atom

ML {* trace := true *}

nominal_datatype lam =
  Var "name"
| App "lam" "lam"
| Lam x::"name" l::"lam"  binds x in l ("Lam [_]. _" [100, 100] 100)

nominal_datatype environment = 
   Ni
 | En name closure environment
and closure = 
   Clos "lam" "environment"

thm environment_closure.exhaust(1)

nominal_function 
  env_lookup :: "environment => name => closure"
where
  "env_lookup Ni x = Clos (Var x) Ni"
| "env_lookup (En v clos rest) x = (if (v = x) then clos else env_lookup rest x)"
   apply (auto)
   apply (simp add: env_lookup_graph_aux_def eqvt_def)
   by (metis environment_closure.strong_exhaust(1))


lemma 
  "Lam [x]. Var x = Lam [y]. Var y"
proof -
  obtain c::name where fresh: "atom c \<sharp> (Lam [x]. Var x, Lam [y]. Var y)"
    by (metis obtain_fresh)
  have "Lam [x]. Var x = (c \<leftrightarrow> x) \<bullet> Lam [x]. Var x"
    using fresh by (rule_tac flip_fresh_fresh[symmetric]) (simp_all add: fresh_Pair)
  also have "... = Lam [c].Var c" by simp
  also have "... = (c \<leftrightarrow> y) \<bullet> Lam [c]. Var c"
    using fresh by (rule_tac flip_fresh_fresh[symmetric]) (auto simp add: fresh_Pair)
  also have "... = Lam [y]. Var y" by simp
  finally show "Lam [x]. Var x = Lam [y]. Var y" .
qed

definition 
  Name :: "nat \<Rightarrow> name" 
where 
  "Name n = Abs_name (Atom (Sort ''name'' []) n)"

definition
   "Ident2 = Lam [Name 1].(Var (Name 1))"

definition 
   "Ident x = Lam [x].(Var x)"

lemma "Ident2 = Ident x"
unfolding Ident_def Ident2_def
by simp

lemma "Ident x = Ident y"
unfolding Ident_def
by simp


section {* Simple examples from Norrish 2004 *}

nominal_function 
  is_app :: "lam \<Rightarrow> bool"
where
  "is_app (Var x) = False"
| "is_app (App t1 t2) = True"
| "is_app (Lam [x]. t) = False"
thm is_app_graph_def is_app_graph_aux_def
apply(simp add: eqvt_def is_app_graph_aux_def)
apply(rule TrueI)
apply(rule_tac y="x" in lam.exhaust)
apply(auto)[3]
apply(all_trivials)
done

nominal_termination (eqvt) by lexicographic_order

thm is_app_def
thm is_app.eqvt

thm eqvts

nominal_function 
  rator :: "lam \<Rightarrow> lam option"
where
  "rator (Var x) = None"
| "rator (App t1 t2) = Some t1"
| "rator (Lam [x]. t) = None"
apply(simp add: eqvt_def rator_graph_aux_def)
apply(rule TrueI)
apply(rule_tac y="x" in lam.exhaust)
apply(auto)[3]
apply(simp_all)
done

nominal_termination (eqvt) by lexicographic_order

nominal_function 
  rand :: "lam \<Rightarrow> lam option"
where
  "rand (Var x) = None"
| "rand (App t1 t2) = Some t2"
| "rand (Lam [x]. t) = None"
apply(simp add: eqvt_def rand_graph_aux_def)
apply(rule TrueI)
apply(rule_tac y="x" in lam.exhaust)
apply(auto)[3]
apply(simp_all)
done

nominal_termination (eqvt) by lexicographic_order

nominal_function 
  is_eta_nf :: "lam \<Rightarrow> bool"
where
  "is_eta_nf (Var x) = True"
| "is_eta_nf (App t1 t2) = (is_eta_nf t1 \<and> is_eta_nf t2)"
| "is_eta_nf (Lam [x]. t) = (is_eta_nf t \<and> 
                             ((is_app t \<and> rand t = Some (Var x)) \<longrightarrow> atom x \<in> supp (rator t)))"
apply(simp add: eqvt_def is_eta_nf_graph_aux_def)
apply(rule TrueI)
apply(rule_tac y="x" in lam.exhaust)
apply(auto)[3]
using [[simproc del: alpha_lst]]
apply(simp_all)
apply(erule_tac c="()" in Abs_lst1_fcb2')
apply(simp_all add: pure_fresh fresh_star_def)[3]
apply(simp add: eqvt_at_def conj_eqvt)
apply(simp add: eqvt_at_def conj_eqvt)
done

nominal_termination (eqvt) by lexicographic_order

nominal_datatype path = Left | Right | In

section {* Paths to a free variables *} 

instance path :: pure
apply(default)
apply(induct_tac "x::path" rule: path.induct)
apply(simp_all)
done

nominal_function 
  var_pos :: "name \<Rightarrow> lam \<Rightarrow> (path list) set"
where
  "var_pos y (Var x) = (if y = x then {[]} else {})"
| "var_pos y (App t1 t2) = (Cons Left ` (var_pos y t1)) \<union> (Cons Right ` (var_pos y t2))"
| "atom x \<sharp> y \<Longrightarrow> var_pos y (Lam [x]. t) = (Cons In ` (var_pos y t))"
apply(simp add: eqvt_def var_pos_graph_aux_def)
apply(rule TrueI)
apply(case_tac x)
apply(rule_tac y="b" and c="a" in lam.strong_exhaust)
apply(auto simp add: fresh_star_def)[3]
using [[simproc del: alpha_lst]]
apply(simp_all)
apply(erule conjE)+
apply(erule_tac Abs_lst1_fcb2)
apply(simp add: pure_fresh)
apply(simp add: fresh_star_def)
apply(simp only: eqvt_at_def)
apply(perm_simp)
apply(simp)
apply(simp add: perm_supp_eq)
apply(simp only: eqvt_at_def)
apply(perm_simp)
apply(simp)
apply(simp add: perm_supp_eq)
done

nominal_termination (eqvt) by lexicographic_order

lemma var_pos1:
  assumes "atom y \<notin> supp t"
  shows "var_pos y t = {}"
using assms
apply(induct t rule: var_pos.induct)
apply(simp_all add: lam.supp supp_at_base fresh_at_base)
done

lemma var_pos2:
  shows "var_pos y (Lam [y].t) = {}"
apply(rule var_pos1)
apply(simp add: lam.supp)
done


text {* strange substitution operation *}

nominal_function
  subst' :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_ [_ ::== _]" [90, 90, 90] 90)
where
  "(Var x)[y ::== s] = (if x = y then s else (Var x))"
| "(App t1 t2)[y ::== s] = App (t1[y ::== s]) (t2[y ::== s])"
| "atom x \<sharp> (y, s) \<Longrightarrow> (Lam [x]. t)[y ::== s] = Lam [x].(t[y ::== (App (Var y) s)])"
  apply(simp add: eqvt_def subst'_graph_aux_def)
  apply(rule TrueI)
  apply(case_tac x)
  apply(rule_tac y="a" and c="(b, c)" in lam.strong_exhaust)
  apply(auto simp add: fresh_star_def)[3]
  using [[simproc del: alpha_lst]]
  apply(simp_all)
  apply(erule conjE)+
  apply (erule_tac c="(ya,sa)" in Abs_lst1_fcb2)
  apply(simp_all add: Abs_fresh_iff)
  apply(simp add: fresh_star_def fresh_Pair)
  apply(simp only: eqvt_at_def)
  apply(perm_simp)
  apply(simp)
  apply(simp add: fresh_star_Pair perm_supp_eq)
  apply(simp only: eqvt_at_def)
  apply(perm_simp)
  apply(simp)
  apply(simp add: fresh_star_Pair perm_supp_eq)
done

nominal_termination (eqvt) by lexicographic_order


section {* free name function *}


lemma fresh_removeAll_name:
  fixes x::"name"
    and xs:: "name list"
  shows "atom x \<sharp> (removeAll y xs) \<longleftrightarrow> (atom x \<sharp> xs \<or> x = y)"
  apply (induct xs)
  apply(auto simp add: fresh_def supp_Nil supp_Cons supp_at_base)
  done


text {* first returns an atom list *}

nominal_function 
  frees_lst :: "lam \<Rightarrow> atom list"
where
  "frees_lst (Var x) = [atom x]"
| "frees_lst (App t1 t2) = frees_lst t1 @ frees_lst t2"
| "frees_lst (Lam [x]. t) = removeAll (atom x) (frees_lst t)"
apply(simp add: eqvt_def frees_lst_graph_aux_def)
apply(rule TrueI)
apply(rule_tac y="x" in lam.exhaust)
using [[simproc del: alpha_lst]]
apply(auto)
apply (erule_tac c="()" in Abs_lst1_fcb2)
apply(simp add: supp_removeAll fresh_def)
apply(simp add: fresh_star_def fresh_Unit)
apply(simp add: eqvt_at_def removeAll_eqvt atom_eqvt)
apply(simp add: eqvt_at_def removeAll_eqvt atom_eqvt)
done

nominal_termination (eqvt) by lexicographic_order

text {* a small test lemma *}
lemma shows "supp t = set (frees_lst t)"
  by (induct t rule: frees_lst.induct) (simp_all add: lam.supp supp_at_base)

text {* second returns an atom set - therefore needs an invariant *}

nominal_function (invariant "\<lambda>x (y::atom set). finite y")
  frees_set :: "lam \<Rightarrow> atom set"
where
  "frees_set (Var x) = {atom x}"
| "frees_set (App t1 t2) = frees_set t1 \<union> frees_set t2"
| "frees_set (Lam [x]. t) = (frees_set t) - {atom x}"
  apply(simp add: eqvt_def frees_set_graph_aux_def)
  apply(erule frees_set_graph.induct)
  apply(auto)[9]
  apply(rule_tac y="x" in lam.exhaust)
  apply(auto)[3]
  using [[simproc del: alpha_lst]]
  apply(simp)
  apply(erule_tac c="()" in Abs_lst1_fcb2)
  apply(simp add: fresh_minus_atom_set)
  apply(simp add: fresh_star_def fresh_Unit)
  apply(simp add: Diff_eqvt eqvt_at_def)
  apply(simp add: Diff_eqvt eqvt_at_def)
  done

nominal_termination (eqvt) 
  by lexicographic_order

lemma "frees_set t = supp t"
  by (induct rule: frees_set.induct) (simp_all add: lam.supp supp_at_base)

section {* height function *}

nominal_function
  height :: "lam \<Rightarrow> int"
where
  "height (Var x) = 1"
| "height (App t1 t2) = max (height t1) (height t2) + 1"
| "height (Lam [x].t) = height t + 1"
  apply(simp add: eqvt_def height_graph_aux_def)
  apply(rule TrueI)
  apply(rule_tac y="x" in lam.exhaust)
  using [[simproc del: alpha_lst]]
  apply(auto)
  apply (erule_tac c="()" in Abs_lst1_fcb2)
  apply(simp_all add: fresh_def pure_supp eqvt_at_def fresh_star_def)
  done

nominal_termination (eqvt)
  by lexicographic_order
  
thm height.simps

  
section {* capture-avoiding substitution *}

nominal_function
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_ [_ ::= _]" [90, 90, 90] 90)
where
  "(Var x)[y ::= s] = (if x = y then s else (Var x))"
| "(App t1 t2)[y ::= s] = App (t1[y ::= s]) (t2[y ::= s])"
| "atom x \<sharp> (y, s) \<Longrightarrow> (Lam [x]. t)[y ::= s] = Lam [x].(t[y ::= s])"
  apply(simp add: eqvt_def subst_graph_aux_def)
  apply(rule TrueI)
  using [[simproc del: alpha_lst]]
  apply(auto)
  apply(rule_tac y="a" and c="(aa, b)" in lam.strong_exhaust)
  apply(blast)+
  using [[simproc del: alpha_lst]]
  apply(simp_all add: fresh_star_def fresh_Pair_elim)
  apply (erule_tac c="(ya,sa)" in Abs_lst1_fcb2)
  apply(simp_all add: Abs_fresh_iff)
  apply(simp add: fresh_star_def fresh_Pair)
  apply(simp only: eqvt_at_def)
  apply(perm_simp)
  apply(simp)
  apply(simp add: fresh_star_Pair perm_supp_eq)
  apply(simp only: eqvt_at_def)
  apply(perm_simp)
  apply(simp)
  apply(simp add: fresh_star_Pair perm_supp_eq)
done

nominal_termination (eqvt)
  by lexicographic_order

thm subst.eqvt

lemma forget:
  shows "atom x \<sharp> t \<Longrightarrow> t[x ::= s] = t"
  by (nominal_induct t avoiding: x s rule: lam.strong_induct)
     (auto simp add: fresh_at_base)

text {* same lemma but with subst.induction *}
lemma forget2:
  shows "atom x \<sharp> t \<Longrightarrow> t[x ::= s] = t"
  apply(induct t x s rule: subst.induct)
  using [[simproc del: alpha_lst]]
  apply(auto simp add:  flip_fresh_fresh fresh_Pair fresh_at_base)
  done

lemma fresh_fact:
  fixes z::"name"
  assumes a: "atom z \<sharp> s"
      and b: "z = y \<or> atom z \<sharp> t"
  shows "atom z \<sharp> t[y ::= s]"
  using a b
  by (nominal_induct t avoiding: z y s rule: lam.strong_induct)
      (auto simp add:  fresh_at_base)

lemma substitution_lemma:  
  assumes a: "x \<noteq> y" "atom x \<sharp> u"
  shows "t[x ::= s][y ::= u] = t[y ::= u][x ::= s[y ::= u]]"
using a 
by (nominal_induct t avoiding: x y s u rule: lam.strong_induct)
   (auto simp add: fresh_fact forget)

lemma subst_rename: 
  assumes a: "atom y \<sharp> t"
  shows "t[x ::= s] = ((y \<leftrightarrow> x) \<bullet>t)[y ::= s]"
using a 
apply (nominal_induct t avoiding: x y s rule: lam.strong_induct)
apply (auto simp add:  fresh_at_base)
done

lemma height_ge_one:
  shows "1 \<le> (height e)"
by (induct e rule: lam.induct) (simp_all)

theorem height_subst:
  shows "height (e[x::=e']) \<le> ((height e) - 1) + (height e')"
proof (nominal_induct e avoiding: x e' rule: lam.strong_induct)
  case (Var y)
  have "1 \<le> height e'" by (rule height_ge_one)
  then show "height (Var y[x::=e']) \<le> height (Var y) - 1 + height e'" by simp
next
  case (Lam y e1)
  hence ih: "height (e1[x::=e']) \<le> ((height e1) - 1) + (height e')" by simp
  moreover
  have vc: "atom y\<sharp>x" "atom y\<sharp>e'" by fact+ (* usual variable convention *)
  ultimately show "height ((Lam [y]. e1)[x::=e']) \<le> height (Lam [y]. e1) - 1 + height e'" by simp
next
  case (App e1 e2)
  hence ih1: "height (e1[x::=e']) \<le> ((height e1) - 1) + (height e')"
    and ih2: "height (e2[x::=e']) \<le> ((height e2) - 1) + (height e')" by simp_all
  then show "height ((App e1 e2)[x::=e']) \<le> height (App e1 e2) - 1 + height e'"  by simp
qed

subsection {* single-step beta-reduction *}

inductive 
  beta :: "lam \<Rightarrow> lam \<Rightarrow> bool" (" _ \<longrightarrow>b _" [80,80] 80)
where
  b1[intro]: "t1 \<longrightarrow>b t2 \<Longrightarrow> App t1 s \<longrightarrow>b App t2 s"
| b2[intro]: "s1 \<longrightarrow>b s2 \<Longrightarrow> App t s1 \<longrightarrow>b App t s2"
| b3[intro]: "t1 \<longrightarrow>b t2 \<Longrightarrow> Lam [x]. t1 \<longrightarrow>b Lam [x]. t2"
| b4[intro]: "atom x \<sharp> s \<Longrightarrow> App (Lam [x]. t) s \<longrightarrow>b t[x ::= s]"

equivariance beta

nominal_inductive beta
  avoids b4: "x"
  by (simp_all add: fresh_star_def fresh_Pair  fresh_fact)

thm beta.strong_induct

text {* One-Reduction *}

inductive 
  One :: "lam \<Rightarrow> lam \<Rightarrow> bool" (" _ \<longrightarrow>1 _" [80,80] 80)
where
  o1[intro]: "Var x \<longrightarrow>1 Var x"
| o2[intro]: "\<lbrakk>t1 \<longrightarrow>1 t2; s1 \<longrightarrow>1 s2\<rbrakk> \<Longrightarrow> App t1 s1 \<longrightarrow>1 App t2 s2"
| o3[intro]: "t1 \<longrightarrow>1 t2 \<Longrightarrow> Lam [x].t1 \<longrightarrow>1 Lam [x].t2"
| o4[intro]: "\<lbrakk>atom x \<sharp> (s1, s2); t1 \<longrightarrow>1 t2; s1 \<longrightarrow>1 s2\<rbrakk> \<Longrightarrow> App (Lam [x].t1) s1 \<longrightarrow>1 t2[x ::= s2]"

equivariance One

nominal_inductive One 
  avoids o3: "x"
      |  o4: "x"
  by (simp_all add: fresh_star_def fresh_Pair  fresh_fact)

lemma One_refl:
  shows "t \<longrightarrow>1 t"
by (nominal_induct t rule: lam.strong_induct) (auto)

lemma One_subst: 
  assumes a: "t1 \<longrightarrow>1 t2" "s1 \<longrightarrow>1 s2"
  shows "t1[x ::= s1] \<longrightarrow>1 t2[x ::= s2]" 
using a 
apply(nominal_induct t1 t2 avoiding: s1 s2 x rule: One.strong_induct)
apply(auto simp add: substitution_lemma fresh_at_base fresh_fact fresh_Pair)
done

lemma better_o4_intro:
  assumes a: "t1 \<longrightarrow>1 t2" "s1 \<longrightarrow>1 s2"
  shows "App (Lam [x]. t1) s1 \<longrightarrow>1 t2[ x ::= s2]"
proof -
  obtain y::"name" where fs: "atom y \<sharp> (x, t1, s1, t2, s2)" by (rule obtain_fresh)
  have "App (Lam [x]. t1) s1 = App (Lam [y]. ((y \<leftrightarrow> x) \<bullet> t1)) s1" using fs
    by (auto simp add: Abs1_eq_iff' flip_def fresh_Pair fresh_at_base)
  also have "\<dots> \<longrightarrow>1 ((y \<leftrightarrow> x) \<bullet> t2)[y ::= s2]" using fs a by (auto simp add: One.eqvt)
  also have "\<dots> = t2[x ::= s2]" using fs by (simp add: subst_rename[symmetric])
  finally show "App (Lam [x].t1) s1 \<longrightarrow>1 t2[x ::= s2]" by simp
qed

section {* Locally Nameless Terms *}

nominal_datatype ln = 
  LNBnd nat
| LNVar name
| LNApp ln ln
| LNLam ln

fun
  lookup :: "name list \<Rightarrow> nat \<Rightarrow> name \<Rightarrow> ln" 
where
  "lookup [] n x = LNVar x"
| "lookup (y # ys) n x = (if x = y then LNBnd n else (lookup ys (n + 1) x))"

lemma supp_lookup:
  shows "supp (lookup xs n x) \<subseteq> {atom x}"
  apply(induct arbitrary: n rule: lookup.induct)
  apply(simp add: ln.supp supp_at_base)
  apply(simp add: ln.supp pure_supp)
  done

lemma supp_lookup_in:
  shows "x \<in> set xs \<Longrightarrow> supp (lookup xs n x) = {}"
  by (induct arbitrary: n rule: lookup.induct)(auto simp add: ln.supp pure_supp)

lemma supp_lookup_notin:
  shows "x \<notin> set xs \<Longrightarrow> supp (lookup xs n x) = {atom x}"
  by (induct arbitrary: n rule: lookup.induct) (auto simp add: ln.supp pure_supp supp_at_base)

lemma supp_lookup_fresh:
  shows "atom ` set xs \<sharp>* lookup xs n x"
  by (case_tac "x \<in> set xs") (auto simp add: fresh_star_def fresh_def supp_lookup_in supp_lookup_notin)

lemma lookup_eqvt[eqvt]:
  shows "(p \<bullet> lookup xs n x) = lookup (p \<bullet> xs) (p \<bullet> n) (p \<bullet> x)"
  by (induct xs arbitrary: n) (simp_all add: permute_pure)

text {* Function that translates lambda-terms into locally nameless terms *}

nominal_function (invariant "\<lambda>(_, xs) y. atom ` set xs \<sharp>* y")
  trans :: "lam \<Rightarrow> name list \<Rightarrow> ln"
where
  "trans (Var x) xs = lookup xs 0 x"
| "trans (App t1 t2) xs = LNApp (trans t1 xs) (trans t2 xs)"
| "atom x \<sharp> xs \<Longrightarrow> trans (Lam [x]. t) xs = LNLam (trans t (x # xs))"
  apply (simp add: eqvt_def trans_graph_aux_def)
  apply (erule trans_graph.induct)
  apply (auto simp add: ln.fresh)[3]
  apply (simp add: supp_lookup_fresh)
  apply (simp add: fresh_star_def ln.fresh)
  apply (simp add: ln.fresh fresh_star_def)
  apply(auto)[1]
  apply (rule_tac y="a" and c="b" in lam.strong_exhaust)
  apply (auto simp add: fresh_star_def)[3]
  using [[simproc del: alpha_lst]]
  apply(simp_all)
  apply(erule conjE)+
  apply (erule_tac c="xsa" in Abs_lst1_fcb2')
  apply (simp add: fresh_star_def)
  apply (simp add: fresh_star_def)
  apply(simp only: eqvt_at_def)
  apply(perm_simp)
  apply(simp add: fresh_star_Pair perm_supp_eq)
  apply(simp only: eqvt_at_def)
  apply(perm_simp)
  apply(simp add: fresh_star_Pair perm_supp_eq)
  done

nominal_termination (eqvt)
  by lexicographic_order


text {* count the occurences of lambdas in a term *}

nominal_function
  cntlams :: "lam  \<Rightarrow> nat"
where
  "cntlams (Var x) = 0"
| "cntlams (App t1 t2) = (cntlams t1) + (cntlams t2)"
| "cntlams (Lam [x]. t) = Suc (cntlams t)"
  apply(simp add: eqvt_def cntlams_graph_aux_def)
  apply(rule TrueI)
  apply(rule_tac y="x" in lam.exhaust)
  apply(auto)[3]
  apply(all_trivials)
  apply(simp)
  using [[simproc del: alpha_lst]]
  apply(simp)
  apply(erule_tac c="()" in Abs_lst1_fcb2')
  apply(simp add: pure_fresh)
  apply(simp add: fresh_star_def pure_fresh)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  done

nominal_termination (eqvt)
  by lexicographic_order


text {* count the bound-variable occurences in a lambda-term *}

nominal_function
  cntbvs :: "lam \<Rightarrow> name list \<Rightarrow> nat"
where
  "cntbvs (Var x) xs = (if x \<in> set xs then 1 else 0)"
| "cntbvs (App t1 t2) xs = (cntbvs t1 xs) + (cntbvs t2 xs)"
| "atom x \<sharp> xs \<Longrightarrow> cntbvs (Lam [x]. t) xs = cntbvs t (x # xs)"
  apply(simp add: eqvt_def cntbvs_graph_aux_def)
  apply(rule TrueI)
  apply(case_tac x)
  apply(rule_tac y="a" and c="b" in lam.strong_exhaust)
  apply(auto simp add: fresh_star_def)[3]
  apply(all_trivials)
  apply(simp)
  apply(simp)
  using [[simproc del: alpha_lst]]
  apply(simp)
  apply(erule conjE)
  apply(erule Abs_lst1_fcb2')
  apply(simp add: pure_fresh fresh_star_def)
  apply(simp add: fresh_star_def)
  apply(simp only: eqvt_at_def)
  apply(perm_simp)
  apply(simp add: fresh_star_Pair perm_supp_eq)
  apply(simp only: eqvt_at_def)
  apply(perm_simp)
  apply(simp add: fresh_star_Pair perm_supp_eq)
  done

nominal_termination (eqvt)
  by lexicographic_order

section {* De Bruijn Terms *}

nominal_datatype db = 
  DBVar nat
| DBApp db db
| DBLam db

instance db :: pure
  apply default
  apply (induct_tac x rule: db.induct)
  apply (simp_all add: permute_pure)
  done

lemma fresh_at_list: "atom x \<sharp> xs \<longleftrightarrow> x \<notin> set xs"
  unfolding fresh_def supp_set[symmetric]
  by (induct xs) (auto simp add: supp_of_finite_insert supp_at_base supp_set_empty)

fun
  vindex :: "name list \<Rightarrow> name \<Rightarrow> nat \<Rightarrow> db option" 
where
  "vindex [] v n = None"
| "vindex (h # t) v n = (if v = h then (Some (DBVar n)) else (vindex t v (Suc n)))"

lemma vindex_eqvt[eqvt]:
  "(p \<bullet> vindex l v n) = vindex (p \<bullet> l) (p \<bullet> v) (p \<bullet> n)"
  by (induct l arbitrary: n) (simp_all add: permute_pure)

nominal_function
  transdb :: "lam \<Rightarrow> name list \<Rightarrow> db option"
where
  "transdb (Var x) l = vindex l x 0"
| "transdb (App t1 t2) xs = 
      Option.bind (transdb t1 xs) (\<lambda>d1. Option.bind (transdb t2 xs) (\<lambda>d2. Some (DBApp d1 d2)))"
| "x \<notin> set xs \<Longrightarrow> transdb (Lam [x].t) xs = Option.map_option DBLam (transdb t (x # xs))"
  apply(simp add: eqvt_def transdb_graph_aux_def)
  apply(rule TrueI)
  apply (case_tac x)
  apply (rule_tac y="a" and c="b" in lam.strong_exhaust)
  apply (auto simp add: fresh_star_def fresh_at_list)[3]
  using [[simproc del: alpha_lst]]
  apply(simp_all)
  apply(elim conjE)
  apply (erule_tac c="xsa" in Abs_lst1_fcb2')
  apply (simp add: pure_fresh)
  apply(simp add: fresh_star_def fresh_at_list)
  apply(simp only: eqvt_at_def)
  apply(perm_simp)
  apply(simp)
  apply(simp add: fresh_star_Pair perm_supp_eq)
  apply(simp only: eqvt_at_def)
  apply(perm_simp)
  apply(simp)
  apply(simp add: fresh_star_Pair perm_supp_eq)
  done

nominal_termination (eqvt)
  by lexicographic_order

lemma transdb_eqvt[eqvt]:
  "p \<bullet> transdb t l = transdb (p \<bullet>t) (p \<bullet>l)"
  apply (nominal_induct t avoiding: l rule: lam.strong_induct)
  apply (simp add: vindex_eqvt)
  apply (simp_all add: permute_pure)
  apply (simp add: fresh_at_list)
  apply (subst transdb.simps)
  apply (simp add: fresh_at_list[symmetric])
  apply (drule_tac x="name # l" in meta_spec)
  apply auto
  done

lemma db_trans_test:
  assumes a: "y \<noteq> x"
  shows "transdb (Lam [x]. Lam [y]. App (Var x) (Var y)) [] = 
  Some (DBLam (DBLam (DBApp (DBVar 1) (DBVar 0))))"
  using a by simp

lemma supp_subst:
  shows "supp (t[x ::= s]) \<subseteq> (supp t - {atom x}) \<union> supp s"
  by (induct t x s rule: subst.induct) (auto simp add: lam.supp supp_at_base)

lemma var_fresh_subst:
  "atom x \<sharp> s \<Longrightarrow> atom x \<sharp> (t[x ::= s])"
  by (induct t x s rule: subst.induct) (auto simp add: lam.supp  fresh_at_base)

(* function that evaluates a lambda term *)
nominal_function
   eval :: "lam \<Rightarrow> lam" and
   apply_subst :: "lam \<Rightarrow> lam \<Rightarrow> lam"
where
  "eval (Var x) = Var x"
| "eval (Lam [x].t) = Lam [x].(eval t)"
| "eval (App t1 t2) = apply_subst (eval t1) (eval t2)"
| "apply_subst (Var x) t2 = App (Var x) t2"
| "apply_subst (App t0 t1) t2 = App (App t0 t1) t2"
| "atom x \<sharp> t2 \<Longrightarrow> apply_subst (Lam [x].t1) t2 = eval (t1[x::= t2])"
  apply(simp add: eval_apply_subst_graph_aux_def eqvt_def)
  apply(rule TrueI)
  apply (case_tac x)
  apply (case_tac a rule: lam.exhaust)
  using [[simproc del: alpha_lst]]
  apply simp_all[3]
  apply (case_tac b)
  apply (rule_tac y="a" and c="ba" in lam.strong_exhaust)
  apply simp_all[3]
  apply (simp add: Abs1_eq_iff fresh_star_def)
  using [[simproc del: alpha_lst]]
  apply(simp_all)
  apply(erule_tac c="()" in Abs_lst1_fcb2)
  apply (simp add: Abs_fresh_iff)
  apply(simp add: fresh_star_def fresh_Unit)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(erule conjE)
  apply(erule_tac c="t2a" in Abs_lst1_fcb2')
  apply (erule fresh_eqvt_at)
  apply (simp add: finite_supp)
  apply (simp add: fresh_Inl var_fresh_subst)
  apply(simp add: fresh_star_def)
  apply(simp only: eqvt_at_def)
  apply(perm_simp)
  apply(simp add: fresh_star_Pair perm_supp_eq)
  apply(simp only: eqvt_at_def)
  apply(perm_simp)
  apply(simp add: fresh_star_Pair perm_supp_eq)
done


(* a small test
nominal_termination (eqvt) sorry

lemma 
  assumes "x \<noteq> y"
  shows "eval (App (Lam [x].App (Var x) (Var x)) (Var y)) = App (Var y) (Var y)"
using assms
apply(simp add: lam.supp fresh_def supp_at_base)
done
*)


text {* TODO: eqvt_at for the other side *}
nominal_function q where
  "atom c \<sharp> (x, M) \<Longrightarrow> q (Lam [x]. M) (N :: lam) = Lam [x]. (Lam [c]. (App M (q (Var c) N)))"
| "q (Var x) N = Var x"
| "q (App l r) N = App l r"
apply(simp add: eqvt_def q_graph_aux_def)
apply (rule TrueI)
apply (case_tac x)
apply (rule_tac y="a" in lam.exhaust)
using [[simproc del: alpha_lst]]
apply simp_all
apply (rule_tac x="(name, lam)" and ?'a="name" in obtain_fresh)
apply blast
apply clarify
apply (rule_tac x="(x, xa, M, Ma, c, ca, Na)" and ?'a="name" in obtain_fresh)
apply (subgoal_tac "eqvt_at q_sumC (Var ca, Na)") --"Could come from nominal_function?"
apply (subgoal_tac "Lam [c]. App M (q_sumC (Var c, Na)) = Lam [a]. App M (q_sumC (Var a, Na))")
apply (subgoal_tac "Lam [ca]. App Ma (q_sumC (Var ca, Na)) = Lam [a]. App Ma (q_sumC (Var a, Na))")
apply (simp only:)
apply (erule Abs_lst1_fcb)
oops

text {* Working Examples *}

nominal_function
  map_term :: "(lam \<Rightarrow> lam) \<Rightarrow> lam \<Rightarrow> lam"
where
  "eqvt f \<Longrightarrow> map_term f (Var x) = f (Var x)"
| "eqvt f \<Longrightarrow> map_term f (App t1 t2) = App (f t1) (f t2)"
| "eqvt f \<Longrightarrow> map_term f (Lam [x].t) = Lam [x].(f t)"
| "\<not>eqvt f \<Longrightarrow> map_term f t = t"
  apply (simp add: eqvt_def map_term_graph_aux_def)
  apply(rule TrueI)
  apply (case_tac x, case_tac "eqvt a", case_tac b rule: lam.exhaust)
  using [[simproc del: alpha_lst]]
  apply auto
  apply (erule Abs_lst1_fcb)
  apply (simp_all add: Abs_fresh_iff fresh_fun_eqvt_app)
  apply (simp add: eqvt_def permute_fun_app_eq)
  done

nominal_termination (eqvt)
  by lexicographic_order


(*
abbreviation
  mbind :: "'a option => ('a => 'b option) => 'b option"  ("_ \<guillemotright>= _" [65,65] 65) 
where  
  "c \<guillemotright>= f \<equiv> case c of None => None | (Some v) => f v"

lemma mbind_eqvt:
  fixes c::"'a::pt option"
  shows "(p \<bullet> (c \<guillemotright>= f)) = ((p \<bullet> c) \<guillemotright>= (p \<bullet> f))"
apply(cases c)
apply(simp_all)
apply(perm_simp)
apply(rule refl)
done

lemma mbind_eqvt_raw[eqvt_raw]:
  shows "(p \<bullet> option_case) \<equiv> option_case"
apply(rule eq_reflection)
apply(rule ext)+
apply(case_tac xb)
apply(simp_all)
apply(rule_tac p="-p" in permute_boolE)
apply(perm_simp add: permute_minus_cancel)
apply(simp)
apply(rule_tac p="-p" in permute_boolE)
apply(perm_simp add: permute_minus_cancel)
apply(simp)
done

fun
  index :: "atom list \<Rightarrow> nat \<Rightarrow> atom \<Rightarrow> nat option" 
where
  "index [] n x = None"
| "index (y # ys) n x = (if x = y then (Some n) else (index ys (n + 1) x))"

lemma [eqvt]:
  shows "(p \<bullet> index xs n x) = index (p \<bullet> xs) (p \<bullet> n) (p \<bullet> x)"
apply(induct xs arbitrary: n)
apply(simp_all add: permute_pure)
done
*)

(*
nominal_function
  trans2 :: "lam \<Rightarrow> atom list \<Rightarrow> db option"
where
  "trans2 (Var x) xs = (index xs 0 (atom x) \<guillemotright>= (\<lambda>n::nat. Some (DBVar n)))"
| "trans2 (App t1 t2) xs = 
     ((trans2 t1 xs) \<guillemotright>= (\<lambda>db1::db. (trans2 t2 xs) \<guillemotright>= (\<lambda>db2::db. Some (DBApp db1 db2))))"
| "trans2 (Lam [x].t) xs = (trans2 t (atom x # xs) \<guillemotright>= (\<lambda>db::db. Some (DBLam db)))"
oops
*)

nominal_function
  CPS :: "lam \<Rightarrow> (lam \<Rightarrow> lam) \<Rightarrow> lam"
where
  "CPS (Var x) k = Var x"
| "CPS (App M N) k = CPS M (\<lambda>m. CPS N (\<lambda>n. n))"
oops

consts b :: name
nominal_function
  Z :: "lam \<Rightarrow> (lam \<Rightarrow> lam) \<Rightarrow> lam"
where
  "Z (App M N) k = Z M (%m. (Z N (%n.(App m n))))"
| "Z (App M N) k = Z M (%m. (Z N (%n.(App (App m n) (Abs b (k (Var b)))))))"
apply(simp add: eqvt_def Z_graph_aux_def)
apply (rule, perm_simp, rule)
oops

lemma test:
  assumes "t = s"
  and "supp p \<sharp>* t" "supp p \<sharp>* x"
  and "(p \<bullet> t) = s \<Longrightarrow> (p \<bullet> x) = y"
  shows "x = y"
using assms by (simp add: perm_supp_eq)

lemma test2:
  assumes "cs \<subseteq> as \<union> bs"
  and "as \<sharp>* x" "bs \<sharp>* x"
  shows "cs \<sharp>* x"
using assms
by (auto simp add: fresh_star_def) 

lemma test3:
  assumes "cs \<subseteq> as"
  and "as \<sharp>* x"
  shows "cs \<sharp>* x"
using assms
by (auto simp add: fresh_star_def) 



nominal_function  (invariant "\<lambda>(_, _, xs) y. atom ` fst ` set xs \<sharp>* y \<and> atom ` snd ` set xs \<sharp>* y")
  aux :: "lam \<Rightarrow> lam \<Rightarrow> (name \<times> name) list \<Rightarrow> bool"
where
  "aux (Var x) (Var y) xs = ((x, y) \<in> set xs)"
| "aux (App t1 t2) (App s1 s2) xs = (aux t1 s1 xs \<and> aux t2 s2 xs)"
| "aux (Var x) (App t1 t2) xs = False"
| "aux (Var x) (Lam [y].t) xs = False"
| "aux (App t1 t2) (Var x) xs = False"
| "aux (App t1 t2) (Lam [x].t) xs = False"
| "aux (Lam [x].t) (Var y) xs = False"
| "aux (Lam [x].t) (App t1 t2) xs = False"
| "\<lbrakk>{atom x} \<sharp>* (s, xs); {atom y} \<sharp>* (t, xs); x \<noteq> y\<rbrakk> \<Longrightarrow> 
       aux (Lam [x].t) (Lam [y].s) xs = aux t s ((x, y) # xs)"
  apply (simp add: eqvt_def aux_graph_aux_def)
  apply(erule aux_graph.induct)
  apply(simp_all add: fresh_star_def pure_fresh)[9]
  apply(case_tac x)
  apply(simp)
  apply(rule_tac y="a" and c="(b, c)" in lam.strong_exhaust)
  apply(simp)
  apply(rule_tac y="b" and c="c" in lam.strong_exhaust)
  apply(metis)+
  apply(simp)
  apply(rule_tac y="b" and c="c" in lam.strong_exhaust)
  apply(metis)+
  apply(simp)
  apply(rule_tac y="b" and c="(lam, c, name)" in lam.strong_exhaust)
  apply(metis)+
  apply(simp)
  apply(drule_tac x="name" in meta_spec)
  apply(drule_tac x="lama" in meta_spec)
  apply(drule_tac x="c" in meta_spec)
  apply(drule_tac x="namea" in meta_spec)
  apply(drule_tac x="lam" in meta_spec)
  apply(simp add: fresh_star_Pair)
  apply(simp add: fresh_star_def fresh_at_base )
  apply(auto)[1]
  apply(simp_all)[44]
  apply(simp del: Product_Type.prod.inject)  
  oops

lemma abs_same_binder:
  fixes t ta s sa :: "_ :: fs"
  and x y::"'a::at"
  shows "[[atom x]]lst. t = [[atom y]]lst. ta \<and> [[atom x]]lst. s = [[atom y]]lst. sa
     \<longleftrightarrow> [[atom x]]lst. (t, s) = [[atom y]]lst. (ta, sa)"
  by (cases "atom x = atom y") (auto simp add: Abs1_eq_iff assms fresh_Pair)

nominal_function
  aux2 :: "lam \<Rightarrow> lam \<Rightarrow> bool"
where
  "aux2 (Var x) (Var y) = (x = y)"
| "aux2 (App t1 t2) (App s1 s2) = (aux2 t1 s1 \<and> aux2 t2 s2)"
| "aux2 (Var x) (App t1 t2) = False"
| "aux2 (Var x) (Lam [y].t) = False"
| "aux2 (App t1 t2) (Var x) = False"
| "aux2 (App t1 t2) (Lam [x].t) = False"
| "aux2 (Lam [x].t) (Var y) = False"
| "aux2 (Lam [x].t) (App t1 t2) = False"
| "x = y \<Longrightarrow> aux2 (Lam [x].t) (Lam [y].s) = aux2 t s"
  apply(simp add: eqvt_def aux2_graph_aux_def)
  apply(rule TrueI)
  apply(case_tac x)
  apply(rule_tac y="a" and c="b" in lam.strong_exhaust)
  apply(rule_tac y="b" in lam.exhaust)
  apply(auto)[3]
  apply(rule_tac y="b" in lam.exhaust)
  apply(auto)[3]
  apply(rule_tac y="b" and c="(name, lam)" in lam.strong_exhaust)
  using [[simproc del: alpha_lst]]
  apply(auto)[3]
  apply(drule_tac x="name" in meta_spec)
  apply(drule_tac x="name" in meta_spec)
  apply(drule_tac x="lam" in meta_spec)
  apply(drule_tac x="(name \<leftrightarrow> namea) \<bullet> lama" in meta_spec)
  using [[simproc del: alpha_lst]]
  apply(simp add: Abs1_eq_iff fresh_star_def fresh_Pair_elim fresh_at_base flip_def)
  apply (metis Nominal2_Base.swap_commute fresh_permute_iff sort_of_atom_eq swap_atom_simps(2))
  using [[simproc del: alpha_lst]]
  apply simp_all
  apply (simp add: abs_same_binder)
  apply (erule_tac c="()" in Abs_lst1_fcb2)
  apply (simp_all add: pure_fresh fresh_star_def eqvt_at_def)
  done

text {* tests of functions containing if and case *}

(*
nominal_function  
  A :: "lam => lam"
where  
  "A (App M N) = (if (True \<or> P M) then (A M) else (A N))"
| "A (Var x) = (Var x)" 
| "A (App M N) = (if True then M else A N)"
oops

nominal_function  
  C :: "lam => lam"
where  
  "C (App M N) = (case (True \<or> P M) of True \<Rightarrow> (A M) | False \<Rightarrow> (A N))"
| "C (Var x) = (Var x)" 
| "C (App M N) = (if True then M else C N)"
oops

nominal_function  
  A :: "lam => lam"
where  
  "A (Lam [x].M) = (Lam [x].M)"
| "A (Var x) = (Var x)"
| "A (App M N) = (if True then M else A N)"
oops

nominal_function  
  B :: "lam => lam"
where  
  "B (Lam [x].M) = (Lam [x].M)"
| "B (Var x) = (Var x)"
| "B (App M N) = (if True then M else (B N))"
unfolding eqvt_def
unfolding B_graph_def
apply(perm_simp)
apply(rule allI)
apply(rule refl)
oops
*)
end



