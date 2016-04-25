theory Weakening
imports "../Nominal2" 
begin

section {* The Weakening property in the simply-typed lambda-calculus *}

atom_decl name

nominal_datatype lam =
  Var "name"
| App "lam" "lam"
| Lam x::"name" l::"lam" binds x in l ("Lam [_]. _" [100,100] 100)

text {* Typing *}

nominal_datatype ty =
  TVar string
| TFun ty ty ("_ \<rightarrow> _" [100,100] 100) 

lemma fresh_ty:
  fixes x::"name"
  and   T::"ty"
  shows "atom x \<sharp> T"
  by (nominal_induct T rule: ty.strong_induct)
     (simp_all add: ty.fresh pure_fresh)

text {* Valid typing contexts *}

inductive
  valid :: "(name \<times> ty) list \<Rightarrow> bool"
where
  v_Nil[intro]: "valid []"
| v_Cons[intro]: "\<lbrakk>atom x \<sharp> Gamma; valid Gamma\<rbrakk> \<Longrightarrow> valid ((x, T) # Gamma)"

equivariance valid

text {* Typing judgements *}

inductive
  typing :: "(name \<times> ty) list \<Rightarrow> lam \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ : _" [60,60,60] 60) 
where
    t_Var[intro]: "\<lbrakk>valid \<Gamma>; (x, T) \<in> set \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x : T"
  | t_App[intro]: "\<lbrakk>\<Gamma> \<turnstile> t1 : T1 \<rightarrow> T2; \<Gamma> \<turnstile> t2 : T1\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App t1 t2 : T2"
  | t_Lam[intro]: "\<lbrakk>atom x \<sharp> \<Gamma>; (x, T1) # \<Gamma> \<turnstile> t : T2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x]. t : T1 \<rightarrow> T2"

equivariance typing

text {* Strong induction principle for typing judgements *}

nominal_inductive typing
  avoids t_Lam: "x"
  by (simp_all add: fresh_star_def fresh_ty)


abbreviation
  "sub_context" :: "(name \<times> ty) list \<Rightarrow> (name \<times> ty) list \<Rightarrow> bool" (infixr "\<subseteq>" 60) 
where
  "\<Gamma>1 \<subseteq> \<Gamma>2 \<equiv> \<forall>x T. (x, T) \<in> set \<Gamma>1 \<longrightarrow> (x, T) \<in> set \<Gamma>2"


text {* The proof *}

lemma weakening_version1: 
  fixes \<Gamma>1 \<Gamma>2::"(name \<times> ty) list"
  and   t ::"lam"
  and   \<tau> ::"ty"
  assumes a: "\<Gamma>1 \<turnstile> t : T"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<subseteq> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t : T"
using a b c
proof (nominal_induct \<Gamma>1 t T avoiding: \<Gamma>2 rule: typing.strong_induct)
  case (t_Var \<Gamma>1 x T)  (* variable case *)
  have "\<Gamma>1 \<subseteq> \<Gamma>2" by fact 
  moreover  
  have "valid \<Gamma>2" by fact 
  moreover 
  have "(x, T) \<in> set \<Gamma>1" by fact
  ultimately show "\<Gamma>2 \<turnstile> Var x : T" by auto
next
  case (t_Lam x \<Gamma>1 T1 t T2) (* lambda case *)
  have vc: "atom x \<sharp> \<Gamma>2" by fact   (* variable convention *)
  have ih: "\<lbrakk>valid ((x, T1) # \<Gamma>2); (x, T1) # \<Gamma>1 \<subseteq> (x, T1) # \<Gamma>2\<rbrakk> \<Longrightarrow> (x, T1) # \<Gamma>2 \<turnstile> t : T2" by fact
  have "\<Gamma>1 \<subseteq> \<Gamma>2" by fact
  then have "(x, T1) # \<Gamma>1 \<subseteq> (x, T1) # \<Gamma>2" by simp
  moreover
  have "valid \<Gamma>2" by fact
  then have "valid ((x, T1) # \<Gamma>2)" using vc by auto
  ultimately have "(x, T1) # \<Gamma>2 \<turnstile> t : T2" using ih by simp
  with vc show "\<Gamma>2 \<turnstile> Lam [x]. t : T1 \<rightarrow> T2" by auto
qed (auto) (* app case *)

lemma weakening_version2: 
  fixes \<Gamma>1 \<Gamma>2::"(name \<times> ty) list"
  assumes a: "\<Gamma>1 \<turnstile> t : T" 
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<subseteq> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t : T"
using a b c
by (nominal_induct \<Gamma>1 t T avoiding: \<Gamma>2 rule: typing.strong_induct)
   (auto | atomize)+


text {* A version with finite sets as typing contexts *}

inductive
  valid2 :: "(name \<times> ty) fset \<Rightarrow> bool"
where
  v2_Empty[intro]: "valid2 {||}"
| v2_Insert[intro]: "\<lbrakk>(x, T) |\<notin>| Gamma; valid2 Gamma\<rbrakk> \<Longrightarrow> valid2 (insert_fset (x, T) Gamma)"

equivariance valid2

inductive
  typing2 :: "(name \<times> ty) fset \<Rightarrow> lam \<Rightarrow> ty \<Rightarrow> bool" ("_ 2\<turnstile> _ : _" [60,60,60] 60) 
where
    t2_Var[intro]: "\<lbrakk>valid2 \<Gamma>; (x, T) |\<in>| \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> 2\<turnstile> Var x : T"
  | t2_App[intro]: "\<lbrakk>\<Gamma> 2\<turnstile> t1 : T1 \<rightarrow> T2; \<Gamma> 2\<turnstile> t2 : T1\<rbrakk> \<Longrightarrow> \<Gamma> 2\<turnstile> App t1 t2 : T2"
  | t2_Lam[intro]: "\<lbrakk>atom x \<sharp> \<Gamma>; insert_fset (x, T1) \<Gamma> 2\<turnstile> t : T2\<rbrakk> \<Longrightarrow> \<Gamma> 2\<turnstile> Lam [x]. t : T1 \<rightarrow> T2"

equivariance typing2

nominal_inductive typing2
  avoids t2_Lam: "x"
  by (simp_all add: fresh_star_def fresh_ty)

lemma weakening_version3: 
  fixes \<Gamma>::"(name \<times> ty) fset"
  assumes a: "\<Gamma> 2\<turnstile> t : T" 
  and     b: "(x, T') |\<notin>| \<Gamma>"
  shows "{|(x, T')|} |\<union>| \<Gamma> 2\<turnstile> t : T"
using a b
apply(nominal_induct \<Gamma> t T avoiding: x rule: typing2.strong_induct)
apply(auto)[2]
apply(rule t2_Lam)
apply(simp add: fresh_insert_fset fresh_ty)
apply(simp)
apply(drule_tac x="xa" in meta_spec)
apply(drule meta_mp)
apply(simp add: fresh_at_base)
apply(simp add: insert_fset_left_comm)
done

lemma weakening_version4: 
  fixes \<Gamma>::"(name \<times> ty) fset"
  assumes a: "\<Gamma> 2\<turnstile> t : T" 
  and     b: "(x, T') |\<notin>| \<Gamma>"
  shows "{|(x, T')|} |\<union>| \<Gamma> 2\<turnstile> t : T"
using a b
apply(induct \<Gamma> t T arbitrary: x T')
apply(auto)[2]
apply(blast)
apply(simp)
apply(rule_tac ?'a="name" and x="(x, xa, t, T', \<Gamma>)" in obtain_fresh)
apply(rule_tac t= "Lam [x]. t" and s="Lam [a]. ((a \<leftrightarrow> x) \<bullet> t)" in subst)
defer
apply(rule t2_Lam)
apply(simp add: fresh_insert_fset)
oops



end



