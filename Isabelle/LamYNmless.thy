theory LamYNmless
imports Main begin

typedecl atom
axiomatization where
  atom_inf: "infinite (UNIV :: atom set)"

typedecl TV

datatype type = Typ TV | Arr type type ("_ \<rightarrow> _")
datatype ptrm = FVar atom | BVar nat | App ptrm ptrm | Lam ptrm | Y type
type_synonym ctxt = "(atom \<times> type) list"

fun opn :: "nat \<Rightarrow> ptrm \<Rightarrow> ptrm \<Rightarrow> ptrm" ("{_ \<rightarrow> _} _")  where
"{k \<rightarrow> u} (FVar x) = FVar x" |
"{k \<rightarrow> u} (BVar i) = (if i = k then u else BVar i)" |
"{k \<rightarrow> u} (App t1 t2) = App ({k \<rightarrow> u} t1)({k \<rightarrow> u} t2)" |
"{k \<rightarrow> u} (Lam t) = Lam ({(k+1) \<rightarrow> u} t)" |
"{k \<rightarrow> u} (Y \<sigma>) = Y \<sigma>"

definition opn':: "ptrm \<Rightarrow> ptrm \<Rightarrow> ptrm" ("_^_") where
"opn' t u \<equiv> {0 \<rightarrow> u} t"

lemma bvar_0_open_any:"BVar 0^M = M" by (simp add: opn'_def)
lemma bvar_Suc_n_open_any:"(BVar (Suc n))^M = BVar (Suc n)" by (simp add: opn'_def)


fun FV :: "ptrm \<Rightarrow> atom set"  where
"FV (FVar x) = {x}" |
"FV (BVar i) = {}" |
"FV (App t1 t2) = (FV t1) \<union> (FV t2)" |
"FV (Lam t) = FV t" |
"FV (Y \<sigma>) = {}"


inductive trm :: "ptrm \<Rightarrow> bool" where
var: "trm (FVar x)" |
app: "\<lbrakk> trm t1 ; trm t2 \<rbrakk> \<Longrightarrow> trm (App t1 t2)" |
lam: "\<lbrakk> finite L ; (\<And>x. x \<notin> L \<Longrightarrow> trm (t^(FVar x))) \<rbrakk> \<Longrightarrow> trm (Lam t)" |
Y: "trm (Y \<sigma>)"
thm trm.simps

lemma bvar_not_trm: "trm (BVar n) \<Longrightarrow> False"
using trm.cases by auto

lemma x_Ex: "\<And>L:: atom set. finite L \<Longrightarrow> \<exists>x. x \<notin> L" by (simp add: ex_new_if_finite atom_inf)
lemma FV_finite: "finite (FV u)"
by (induct u, auto)

lemma test: "\<not>(trm (Lam (BVar 2)))"
apply rule
apply (drule_tac subst[OF trm.simps])
apply simp
proof goal_cases
  case 1
  then have "(\<exists>L. finite L \<and> (\<forall>x. x \<notin> L \<longrightarrow> trm (BVar 2)^FVar x))" by simp
  then obtain x L where "(\<forall>x. x \<notin> L \<longrightarrow> trm (BVar 2)^FVar x)" and "x \<notin> L" "finite L" using x_Ex by metis
  then have "trm (BVar 2)^FVar x" by simp
  thus ?case using bvar_Suc_n_open_any bvar_not_trm numeral_2_eq_2 by auto
qed


inductive wf_ctxt :: "ctxt \<Rightarrow> bool" where
nil: "wf_ctxt []" |
cons: "\<lbrakk> x \<notin> fst`set C ; wf_ctxt C \<rbrakk> \<Longrightarrow> wf_ctxt ((x, \<sigma>)#C)"


inductive wt_trm :: "ctxt \<Rightarrow> ptrm \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ : _") where
var: "\<lbrakk> wf_ctxt \<Gamma> ; (x,\<sigma>) \<in> set \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> FVar x : \<sigma>" |
app: "\<lbrakk> \<Gamma> \<turnstile> t1 : \<tau> \<rightarrow> \<sigma> ; \<Gamma> \<turnstile> t2 : \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App t1 t2 : \<sigma>" |
abs: "\<lbrakk> finite L ; (\<And>x. x \<notin> L \<Longrightarrow> ((x,\<sigma>)#\<Gamma>) \<turnstile> (t^(FVar x)) : \<tau>) \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam t : \<sigma> \<rightarrow> \<tau>" |
Y: "\<lbrakk> wf_ctxt \<Gamma> \<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile> Y \<sigma> : (\<sigma> \<rightarrow> \<sigma>) \<rightarrow> \<sigma>"



inductive beta_Y :: "ptrm \<Rightarrow> ptrm \<Rightarrow> bool" (infix "\<Rightarrow>" 300)
where
  red_L[intro]: "\<lbrakk> trm N ; M \<Rightarrow> M' \<rbrakk> \<Longrightarrow> App M N \<Rightarrow> App M' N"
| red_R[intro]: "\<lbrakk> trm M ; N \<Rightarrow> N' \<rbrakk> \<Longrightarrow> App M N \<Rightarrow> App M N'"
| abs[intro]: "\<lbrakk> finite L ; (\<And>x. x \<notin> L \<Longrightarrow> M^(FVar x) \<Rightarrow> M'^(FVar x)) \<rbrakk> \<Longrightarrow> Lam M \<Rightarrow> Lam M'"
| beta[intro]: "\<lbrakk> trm (Lam M) ; trm N \<rbrakk> \<Longrightarrow> App (Lam M) N \<Rightarrow> M^N"
| Y[intro]: "App (Y \<sigma>) M \<Rightarrow> App M (App (Y \<sigma>) M)"

lemma test2: "Lam (App (Lam (BVar 0)) (FVar x)) \<Rightarrow> Lam (FVar x)"
apply (rule_tac L="{}" in abs, simp, thin_tac "xa \<notin> {}")
unfolding opn'_def
unfolding opn.simps
apply simp
apply (rule_tac s="BVar 0^FVar x" in subst)
(*is there a nicer way to do this? i.e. subst for the second occurence of FVar x only?*)
apply (subst opn'_def)
apply simp
apply (subst bvar_0_open_any)
apply(rule beta)
apply (rule_tac L="{}" in trm.lam, simp)
apply (subst bvar_0_open_any)
by (rule_tac trm.var)+





primrec subst :: "ptrm \<Rightarrow> atom \<Rightarrow> ptrm \<Rightarrow> ptrm" ("_ [_ ::= _]" [90, 90, 90] 90) where
"(FVar x)[z ::= u] = (if x = z then u else FVar x)" |
"(BVar x)[z ::= u] = BVar x" |
"(App t1 t2)[z ::= u] = App (t1[z ::= u]) (t2[z ::= u])" |
"(Lam t)[z ::= u] = Lam (t[z ::= u])" |
"(Y \<sigma>)[z ::= u] = (Y \<sigma>)"

lemma subst_fresh: "x \<notin> FV t \<Longrightarrow> t[x ::= u] = t"
by (induct t, auto)

lemma subst_fresh2: "x \<notin> FV t \<Longrightarrow> t = t[x ::= u]"
by (induct t, auto)

lemma opn_trm_core: "i \<noteq> j \<Longrightarrow> {j \<rightarrow> v} e = {i \<rightarrow> u}({j \<rightarrow> v} e) \<Longrightarrow> e = {i \<rightarrow> u} e"
apply (induct e arbitrary: i j)
apply auto
by blast

lemma opn_trm: "trm e \<Longrightarrow> e = {k \<rightarrow> t}e"
apply (induct arbitrary: k t rule:trm.induct)
apply simp+
defer
apply simp
proof goal_cases
case (1 L e k t)
  then obtain y where 2: "y \<notin> (L \<union> FV e)" using FV_finite x_Ex by (meson finite_UnI)
  show ?case
  apply (rule_tac j = 0 and v= "FVar y" in opn_trm_core)
  using "1"(3) "2" opn'_def by auto
qed



lemma subst_open: "trm u \<Longrightarrow> ({n \<rightarrow> w}t)[x ::= u] = {n \<rightarrow> w [x ::= u]} (t [x ::= u])"
apply (induct t arbitrary:n)
by (auto simp add:opn_trm)

lemma subst_open2: "trm u \<Longrightarrow> {n \<rightarrow> w [x ::= u]} (t [x ::= u]) = ({n \<rightarrow> w}t)[x ::= u]"
by (simp add:subst_open)

lemma fvar_subst_simp: "x \<noteq> y \<Longrightarrow> FVar y = FVar y[x ::= u]" by simp
lemma fvar_subst_simp2: "u = FVar x[x ::= u]" by simp

lemma subst_open_var: "trm u \<Longrightarrow> x \<noteq> y \<Longrightarrow> (t^FVar y)[x ::= u] = (t [x ::= u])^FVar y"
unfolding opn'_def
using subst_open
apply (subst(2) fvar_subst_simp)
apply simp
apply (rule_tac subst_open)
by simp

lemma subst_intro: "trm u \<Longrightarrow> x \<notin> FV t \<Longrightarrow> (t^FVar x)[x::=u] = t^u"
unfolding opn'_def
apply (subst(6) fvar_subst_simp2[where x=x])
apply (subst(10) subst_fresh2[where x=x and u=u])
defer
apply (rule subst_open)
by auto


inductive 
  pbeta :: "ptrm \<Rightarrow> ptrm \<Rightarrow> bool" ("_ \<Rightarrow>\<parallel> _" [80,80] 80)
where
  refl[intro]: "(FVar x) \<Rightarrow>\<parallel> (FVar x)"
| reflY[intro]: "Y \<sigma> \<Rightarrow>\<parallel> Y \<sigma>"
| app[intro]: "\<lbrakk> M \<Rightarrow>\<parallel> M' ; N \<Rightarrow>\<parallel> N' \<rbrakk> \<Longrightarrow> App M N \<Rightarrow>\<parallel> App M' N'"
| abs[intro]: "\<lbrakk> finite L ; (\<And>x. x \<notin> L \<Longrightarrow> M^(FVar x) \<Rightarrow>\<parallel> M'^(FVar x)) \<rbrakk> \<Longrightarrow> Lam M \<Rightarrow>\<parallel> Lam M'"
| beta[intro]: "\<lbrakk> M \<Rightarrow>\<parallel> M' ; N \<Rightarrow>\<parallel> N' \<rbrakk> \<Longrightarrow> App (Lam M) N \<Rightarrow>\<parallel> M'^N'"
| Y[intro]: "\<lbrakk> M \<Rightarrow>\<parallel> M' \<rbrakk> \<Longrightarrow> App (Y \<sigma>) M \<Rightarrow>\<parallel> App M' (App (Y \<sigma>) M')"


primrec 
  not_abst :: "ptrm \<Rightarrow> bool"
where
  "not_abst (FVar x) = True"
| "not_abst (BVar x) = True"
| "not_abst (App t1 t2) = True"
| "not_abst (Lam t) = False"
| "not_abst (Y t) = True"


fun 
  not_Y :: "ptrm \<Rightarrow> bool"
where
  "not_Y (FVar x) = True"
| "not_Y (BVar x) = True"
| "not_Y (App t1 t2) = True"
| "not_Y (Lam t) = True"
| "not_Y (Y t) = False"


inductive 
  pbeta_max :: "ptrm \<Rightarrow> ptrm \<Rightarrow> bool" ("_ >>> _" [80,80] 80)
where
  refl[intro]: "(FVar x) >>> (FVar x)"
| reflY[intro]: "Y \<sigma> >>> Y \<sigma>"
| app[intro]: "\<lbrakk> not_abst M ; not_Y M ;  M >>> M' ; N >>> N' \<rbrakk> \<Longrightarrow> App M N >>> App M' N'"
| abs[intro]: "\<lbrakk> finite L ; (\<And>x. x \<notin> L \<Longrightarrow> M^(FVar x) >>> M'^(FVar x)) \<rbrakk> \<Longrightarrow> Lam M >>>  Lam M'"
| beta[intro]: "\<lbrakk> M >>> M' ; N >>> N' \<rbrakk> \<Longrightarrow> App (Lam M) N >>> M'^N'"
| Y[intro]: "\<lbrakk> M >>> M' \<rbrakk> \<Longrightarrow> App (Y \<sigma>) M >>> App M' (App (Y \<sigma>) M')"

lemma Lem2_5_1:
  assumes "s \<Rightarrow>\<parallel> s'"
      and "t \<Rightarrow>\<parallel> t'"
      shows "(s[x ::= t]) \<Rightarrow>\<parallel> (s'[x ::= t'])"
using assms proof (induct s s' rule:pbeta.induct)
case (refl s)
  then show ?case by auto
next
case (reflY s)
  then show ?case by auto
next
case app
  show ?case 
  unfolding subst.simps
  apply (rule pbeta.app)
  using app
  by simp+
next
case (abs L M M') 
  show ?case 
  unfolding subst.simps
  apply (rule_tac L="L \<union> {x}" in pbeta.abs)
  using abs apply simp 
unfolding opn'_def
  apply (subst subst_fresh2[where x=x and u=t])
  apply auto[1]
  apply (subst(8) subst_fresh2[where x=x and u=t'])
  apply auto[1]
  apply (subst subst_open2)
  defer
  apply (subst subst_open2)
  defer
  using abs(2,3) apply (simp add: UnI1 abs.prems opn'_def)
  sorry (*prove M \<Rightarrow>\<parallel> M' \<Longrightarrow> trm M \<and> trm M'" *)
next
case (beta M M' N N')
  show ?case sorry
next
case Y thus ?case by auto
qed

lemma not_Y_ex: "\<not>(not_Y M) \<Longrightarrow> \<exists>\<sigma>. M = Y \<sigma>"
apply (cases M rule:not_Y.cases)
by auto

lemma pbeta_max_ex:
  fixes a
  assumes "trm a"
  shows "\<exists>d. a >>> d"
using assms apply (induct a rule:trm.induct)
apply auto
apply (case_tac "not_abst t1")
apply (case_tac "not_Y t1")
apply auto[1]
proof goal_cases
case (1 trm1 trm2 d da)
  then obtain \<sigma> where 2: "trm1 = Y \<sigma>" using not_Y_ex by auto
  have "App (Y \<sigma>) trm2 >>> App da (App (Y \<sigma>) da)"
  apply (rule_tac pbeta_max.Y)
  by (rule 1(4))
  thus ?case unfolding 2 by auto
next
case (2 trm1 trm2 d da)
  from 2(3,3,4) show ?case
  apply (induct trm1 d rule:pbeta_max.induct)
  apply auto
apply fastforce+
defer
apply fastforce+
sorry
qed


end