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
apply (subst(2) fvar_subst_simp)
apply simp
apply (rule_tac subst_open)
by simp

lemma subst_open_var2: "trm u \<Longrightarrow> x \<noteq> y \<Longrightarrow> (t [x ::= u])^FVar y = (t^FVar y)[x ::= u]" using subst_open_var by simp


lemma subst_intro: "trm u \<Longrightarrow> x \<notin> FV t \<Longrightarrow> (t^FVar x)[x::=u] = t^u"
unfolding opn'_def
apply (subst(6) fvar_subst_simp2[where x=x])
apply (subst(10) subst_fresh2[where x=x and u=u])
defer
apply (rule subst_open)
by auto

lemma subst_intro2: "trm u \<Longrightarrow> x \<notin> FV t \<Longrightarrow> t^u = (t^FVar x)[x::=u]" using subst_intro by simp


inductive 
  pbeta :: "ptrm \<Rightarrow> ptrm \<Rightarrow> bool" ("_ \<Rightarrow>\<parallel> _" [80,80] 80)
where
  refl[intro]: "(FVar x) \<Rightarrow>\<parallel> (FVar x)"
| reflY[intro]: "Y \<sigma> \<Rightarrow>\<parallel> Y \<sigma>"
| app[intro]: "\<lbrakk> M \<Rightarrow>\<parallel> M' ; N \<Rightarrow>\<parallel> N' \<rbrakk> \<Longrightarrow> App M N \<Rightarrow>\<parallel> App M' N'"
| abs[intro]: "\<lbrakk> finite L ; (\<And>x. x \<notin> L \<Longrightarrow> M^(FVar x) \<Rightarrow>\<parallel> M'^(FVar x)) \<rbrakk> \<Longrightarrow> Lam M \<Rightarrow>\<parallel> Lam M'"
| beta[intro]: "\<lbrakk> finite L ; (\<And>x. x \<notin> L \<Longrightarrow> M^(FVar x) \<Rightarrow>\<parallel> M'^(FVar x)) ; N \<Rightarrow>\<parallel> N' \<rbrakk> \<Longrightarrow> App (Lam M) N \<Rightarrow>\<parallel> M'^N'"
| Y[intro]: "\<lbrakk> M \<Rightarrow>\<parallel> M' \<rbrakk> \<Longrightarrow> App (Y \<sigma>) M \<Rightarrow>\<parallel> App M' (App (Y \<sigma>) M')"


lemma subst_trm: "trm e \<Longrightarrow> trm u \<Longrightarrow> trm(e[x::=u])"
proof (induct rule:trm.induct)
case var thus ?case by (simp add:trm.var)
next
case app thus ?case by (simp add:trm.app)
next
case Y thus ?case by (simp add:trm.Y)
next
case (lam L t) 
  show ?case
  unfolding subst.simps
  apply (rule trm.lam[where L="L \<union> {x}"])
  using lam apply auto[1]
  apply (subst subst_open_var2)
  using lam by auto
qed

lemma trm_opn: "trm (Lam M) \<and> trm N \<Longrightarrow> trm M^N"
apply (frule conjE[where R="trm (Lam M)"])
apply simp
apply (drule conjE[where R="trm N"])
apply simp
apply (cases rule:trm.cases)
apply auto
proof goal_cases
case (1 L) 
  then obtain x where 2: "x \<notin> L \<union> FV M" by (meson FV_finite finite_UnI x_Ex)
  with 1 have 3: "trm M^FVar x" by simp
  
  show ?case
  apply(subst subst_intro2)
  using 1 apply simp
  using 2 apply auto[1]
  apply (subst subst_trm)
  using 1 3 by auto
qed

lemma trm_pbeta_simp1: "M \<Rightarrow>\<parallel> M' \<Longrightarrow> trm M \<and> trm M'"
apply rule
apply (induct M M' rule:pbeta.induct)
apply (subst trm.simps, simp)+
apply auto[1]
apply (simp add: lam trm.app)
apply (simp add: trm.Y trm.app)
apply (induct M M' rule:pbeta.induct)
apply (subst trm.simps, simp)+
apply auto[1]
apply (rule trm_opn)
apply (simp add: lam)
apply (simp add: trm.Y trm.app)
done


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
| beta[intro]: "\<lbrakk> finite L ; (\<And>x. x \<notin> L \<Longrightarrow> M^(FVar x) >>> M'^(FVar x)) ; N >>> N' \<rbrakk> \<Longrightarrow> App (Lam M) N >>> M'^N'"
| Y[intro]: "\<lbrakk> M >>> M' \<rbrakk> \<Longrightarrow> App (Y \<sigma>) M >>> App M' (App (Y \<sigma>) M')"


lemma trm_pbeta_max_simp1: "M >>> M' \<Longrightarrow> trm M \<and> trm M'"
apply rule
apply (induct M M' rule:pbeta_max.induct)
apply (subst trm.simps, simp)+
apply auto[1]
apply (simp add: lam trm.app)
apply (simp add: trm.Y trm.app)
apply (induct M M' rule:pbeta_max.induct)
apply (subst trm.simps, simp)+
apply auto[1]
apply (rule trm_opn)
apply (simp add: lam)
apply (simp add: trm.Y trm.app)
done



lemma pbeta_beta': "finite L \<Longrightarrow> (\<And>x. x \<notin> L \<Longrightarrow> M^(FVar x) \<Rightarrow>\<parallel> M'^(FVar x)) \<Longrightarrow> N \<Rightarrow>\<parallel> N' \<Longrightarrow> App (Lam M) N \<Rightarrow>\<parallel> {0 \<rightarrow> N'} M'" using pbeta.beta opn'_def by simp


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
  using trm_pbeta_simp1 abs.prems by auto
 next
case (beta L M M' N N')
  show ?case unfolding subst.simps opn'_def
  apply (subst subst_open)
  defer
  apply (rule_tac L="L \<union> {x}" in pbeta_beta')
  using beta apply simp
  apply (subst subst_open_var2)
  using beta trm_pbeta_simp1 apply simp
  apply auto[1]
  apply (subst subst_open_var2)
  using beta trm_pbeta_simp1 apply simp
  apply auto[1]
  using beta trm_pbeta_simp1 by auto
next
case Y thus ?case by auto
qed


lemma Lem2_5_1opn:
  assumes "\<And>x. x \<notin> L \<Longrightarrow> s^FVar x \<Rightarrow>\<parallel> s'^FVar x" and "finite L"
      and "t \<Rightarrow>\<parallel> t'"
      shows "s^t \<Rightarrow>\<parallel> s'^t'"
proof -
  from assms(2) obtain x where 1: "x \<notin> L \<union> FV s \<union> FV s'" by (meson FV_finite infinite_Un x_Ex)
  show ?thesis
  apply (subst subst_intro2[where x=x])
  using assms(3) apply (simp add: trm_pbeta_simp1)
  using 1 apply simp
  apply (subst (2) subst_intro2[where x=x])
  using assms(3) apply (simp add: trm_pbeta_simp1)
  using 1 apply simp
  apply(rule Lem2_5_1)
  using assms 1 by auto
qed


lemma not_Y_ex: "\<not>(not_Y M) \<Longrightarrow> \<exists>\<sigma>. M = Y \<sigma>"
apply (cases M rule:not_Y.cases)
by auto


fun cls :: "nat \<Rightarrow> atom \<Rightarrow> ptrm \<Rightarrow> ptrm" ("{_ <- _} _")  where
"{k <- x} (FVar y) = (if x = y then BVar k else FVar y)" |
"{k <- x} (BVar i) = BVar i" |
"{k <- x} (App t1 t2) = App ({k <- x} t1)({k <- x} t2)" |
"{k <- x} (Lam t) = Lam ({(k+1) <- x} t)" |
"{k <- x} (Y \<sigma>) = Y \<sigma>"

definition cls':: "atom \<Rightarrow> ptrm \<Rightarrow> ptrm" ("\\_^_") where
"cls' x t \<equiv> {0 <- x} t"

lemma not_abst_simp: "not_abst M \<Longrightarrow> not_abst {k \<rightarrow> FVar y} {k <- x} M"
apply (cases M)
unfolding opn'_def opn.simps
by auto

lemma not_Y_simp: "not_Y M \<Longrightarrow> not_Y {k \<rightarrow> FVar y} {k <- x} M"
apply (cases M)
unfolding opn'_def opn.simps
by auto


(*lemma cls_pbeta_max: "{k \<rightarrow> FVar x}M >>> d \<Longrightarrow> x \<notin> FV M \<Longrightarrow> \<exists>L. finite L \<and> (\<forall>y. y \<notin> L \<longrightarrow> {k \<rightarrow> FVar y}M >>> {k \<rightarrow> FVar y}({k <- x}d))"
proof (induct "{k \<rightarrow> FVar x}M" d arbitrary:M x k rule:pbeta_max.induct)
case (refl x')
  (*show ?case 
  proof (cases "x=x'")
  case False
    with refl have 1: "M = FVar x'" unfolding opn'_def apply (cases M) apply auto using not_gr0 by fastforce
    show ?thesis unfolding 1 opn'_def cls'_def opn.simps cls.simps
    using False by auto
  next
  case True
    with refl show ?thesis
    apply (cases "M")
    unfolding opn'_def apply simp_all
    using cls'_def by fastforce
  qed*)
next
case (reflY \<sigma>) 
  from reflY(1) have 1:"M = Y \<sigma>" unfolding opn'_def 
  apply (cases M) 
  apply simp_all 
  using gr0I by fastforce
  show ?case unfolding 1 opn'_def cls'_def opn.simps cls.simps by auto
next
case (app M' M'' N' N'')
  from app(7) obtain MM' NN' where 1: "M = App MM' NN'" 
  apply (cases M) 
  unfolding opn'_def apply auto
  by (meson ptrm.distinct(4) ptrm.simps(15))
  from app have 2: "M' = {k \<rightarrow> FVar x}MM'" "N' = {k \<rightarrow> FVar x}NN'" by (simp add: "1" opn'_def)+
  with app have 3:"x \<notin> FV MM'" "x \<notin> FV NN'" 
  unfolding 1 2 opn'_def cls'_def opn.simps cls.simps FV.simps
  by simp+
  with app have 4:  "\<exists>L. finite L \<and> (\<forall>y. y \<notin> L \<longrightarrow> {k \<rightarrow> FVar y} MM' >>> {k \<rightarrow> FVar y} {k <- x} M'')"
                    "\<exists>L. finite L \<and> (\<forall>y. y \<notin> L \<longrightarrow> {k \<rightarrow> FVar y} NN' >>> {k \<rightarrow> FVar y} {k <- x} N'')"
  unfolding 1 2 opn'_def cls'_def opn.simps cls.simps FV.simps
  by simp+
  then obtain LM LN where 5: "finite LM" "(\<forall>y. y \<notin> LM \<longrightarrow> {k \<rightarrow> FVar y} MM' >>> {k \<rightarrow> FVar y} {k <- x} M'')"
                             "finite LN" "(\<forall>y. y \<notin> LN \<longrightarrow> {k \<rightarrow> FVar y} NN' >>> {k \<rightarrow> FVar y} {k <- x} N'')" by auto

  show ?case unfolding 1 opn'_def cls'_def opn.simps cls.simps
  apply (rule_tac exI[where x="LM \<union> LN"])
  apply rule
  using 5 apply simp
  apply rule
  apply rule
  apply rule
  using app not_abst_simp unfolding 1 apply simp
  using app not_Y_simp unfolding 1 apply simp
  using 5 by simp+
next
case (abs L N N')
  from abs(4) obtain M' where 1: "M = Lam M'" 
  apply (cases M) 
  unfolding opn'_def apply auto
  by (metis ptrm.distinct(5) ptrm.simps(17))
  
  obtain x' where 2: "x' \<notin> L \<union> FV M \<union> {x}" by (metis FV.simps(1) FV_finite abs.hyps(1) finite_UnI x_Ex)
  from abs have 3: "N = {0 + 1 \<rightarrow> FVar x} M'" unfolding 1 opn'_def opn.simps by simp
  from abs have 4: "N^FVar x' = ({0 + 1 \<rightarrow> FVar x} M')^FVar x'" unfolding 1 3 opn'_def opn.simps by simp
  from 2 have "x' \<notin> FV ({0 + 1 \<rightarrow> FVar x} M')" using FV_simp by (simp add: "1" UnI1 UnI2 singletonI)

  with 2 4 abs(3) have "\<exists>L. finite L \<and> (\<forall>y. y \<notin> L \<longrightarrow> ({0 + 1 \<rightarrow> FVar x} M')^(FVar y) >>> (\\x'^(N'^FVar x'))^FVar y)" by simp
  then obtain L' where 5: "finite L'" "(\<forall>y. y \<notin> L' \<longrightarrow> ({0 + 1 \<rightarrow> FVar x} M')^(FVar y) >>> (\\x'^(N'^FVar x'))^FVar y)" by auto

  show ?case unfolding 1
  apply (rule_tac exI[where x="L \<union> L'"])
  apply rule
  using abs 5 apply simp
 
  apply rule
  apply rule
  unfolding opn'_def opn.simps cls'_def cls.simps
  apply (rule_tac L=L' in pbeta_max.abs)
  using 5 apply simp

  using 5   unfolding opn'_def opn.simps cls'_def cls.simps

apply auto[1]

defer
using abs  
sorry
next
case beta show ?case sorry
next
case (Y M' M'' \<sigma>) show ?case sorry
qed*)


lemma FV_simp: "\<lbrakk> x \<notin> FV M ; x \<noteq> y \<rbrakk> \<Longrightarrow> x \<notin> FV {k \<rightarrow> FVar y} M"
apply (induct M arbitrary:k)
by auto

lemma FV_simp2: "x \<notin> FV M \<union> FV N \<Longrightarrow> x \<notin> FV {k \<rightarrow> N}M"
apply (induct M arbitrary:k)
by auto


lemma FV_simp3: "x \<notin> FV {k \<rightarrow> N}M \<Longrightarrow> x \<notin> FV M"
apply (induct M arbitrary:k)
by auto


lemma fv_opn_cls_id: "x \<notin> FV t \<Longrightarrow> {k <- x}{k \<rightarrow> FVar x}t = t"
apply (induct t arbitrary:k)
by auto

lemma fv_opn_cls_id2: "x \<notin> FV t \<Longrightarrow> t = {k <- x}{k \<rightarrow> FVar x}t" using fv_opn_cls_id by simp


(*lemma fv_cls_id: "x \<notin> FV t \<Longrightarrow> {k <- x} t = t"
apply (induct t arbitrary:k)
by auto

lemma fv_cls_id2: "x \<notin> FV t \<Longrightarrow> t = {k <- x} t" using fv_cls_id by simp
*)

lemma opn_cls_swap: "k \<noteq> m \<Longrightarrow> x \<noteq> y \<Longrightarrow> {k <- x}{m \<rightarrow> FVar y}M = {m \<rightarrow> FVar y}{k <- x}M"
apply (induct M arbitrary:k m)
by auto

lemma opn_cls_swap2: "k \<noteq> m \<Longrightarrow> x \<noteq> y \<Longrightarrow> {m \<rightarrow> FVar y}{k <- x}M = {k <- x}{m \<rightarrow> FVar y}M" using opn_cls_swap by simp


lemma opn_opn_swap: "k \<noteq> m \<Longrightarrow> x \<noteq> y \<Longrightarrow> {k \<rightarrow> FVar x}{m \<rightarrow> FVar y}M = {m \<rightarrow> FVar y}{k \<rightarrow> FVar x}M"
apply (induct M arbitrary:k m)
by auto

lemma opn_swap: "M = M' \<Longrightarrow> {k \<rightarrow> y} M = {k \<rightarrow> y} M'" by simp

(*lemma opn_cls_opn_swap: "{0 \<rightarrow> FVar y}{0 <- x}{0 \<rightarrow> N}M = {0 \<rightarrow> {0 \<rightarrow> FVar y}{0 <- x}N}M"
unfolding opn'_def
apply (induct M)
apply auto
proof (induct M arbitrary:k)
case FVar thus ?case by simp
next
case (BVar x') 
  show ?case
 apply auto sorry
next
case App thus ?case by simp
next
case Lam thus ?case sorry
next
case Y thus ?case by simp
qed*)


lemma pbeta_max_cls: "t >>> d \<Longrightarrow> y \<notin> FV t \<union> FV d \<Longrightarrow> {k \<rightarrow> FVar y}{k <- x}t >>> {k \<rightarrow> FVar y}{k <- x}d"
proof (induct t d arbitrary:k rule:pbeta_max.induct)
case refl thus ?case by auto
next
case reflY thus ?case by auto
next
case (app M M' N N') 
  show ?case 
  unfolding cls.simps opn.simps apply rule
  using not_abst_simp not_Y_simp app by auto 
next
case (abs L M M')
  from abs(3) have ih: "\<And>xa k. xa \<notin> L \<union> {x,y} \<Longrightarrow> k > 0 \<Longrightarrow> (y \<notin> FV (M^(FVar xa)) \<union> FV (M'^(FVar xa))) \<Longrightarrow> (({k \<rightarrow> FVar y}{k <- x}M)^(FVar xa) >>> ({k \<rightarrow> FVar y}{k <- x}M')^(FVar xa))"
  unfolding opn'_def
  apply (subst opn_opn_swap)
  apply (simp,simp)
  apply (subst(2) opn_opn_swap)
  apply (simp,simp)
  apply (subst opn_cls_swap2)
  apply simp
  apply auto[1]
  apply (subst (2) opn_cls_swap2)
  apply simp
  apply auto[1]
  using abs unfolding opn'_def by simp

  from abs have 1: "\<And>x. x \<notin> L \<union> {y} \<Longrightarrow> y \<notin> FV M^FVar x \<union> FV M'^FVar x" unfolding opn'_def using FV.simps(4) FV_simp Un_iff opn'_def singletonI by auto

  show ?case 
  unfolding cls.simps opn.simps 
  apply (rule_tac L="L \<union> {x,y}" in pbeta_max.abs)
  apply (simp add: abs.hyps(1))
  using ih 1 by simp
next
case (beta L M M' N N')
  from beta have 1:"y \<notin> FV M" by simp
  from beta(6) have "y \<notin> FV M'" unfolding opn'_def using FV_simp3 by auto
  then have 2: "\<And>x. x \<noteq> y \<Longrightarrow> y \<notin> FV M^FVar x \<union> FV M'^FVar x" using 1 unfolding opn'_def using FV_simp by simp
  (*from beta(6) have "y \<notin> FV N \<union> FV N'" unfolding FV.simps opn'_def using FV_simp2 *)
  show ?case
  unfolding cls.simps opn.simps opn'_def

(*  apply (subst opn_cls_opn_swap)
defer
apply (rule_tac L="L \<union> {x,y}" in pbeta_max.beta)
using beta apply simp
unfolding opn'_def
  apply (subst opn_opn_swap)
  apply (simp,simp)
  apply (subst (2) opn_opn_swap)
  apply (simp,simp)
  apply (subst opn_cls_swap2)
  apply simp
  apply auto[1]
  apply (subst (2) opn_cls_swap2)
  apply simp
  apply auto[1]
using beta(3) 2 unfolding opn'_def apply simp
using beta(5) unfolding opn'_def



using beta apply auto[1]

  using pbeta_max.beta*)
  sorry
next
case Y show ?case unfolding opn'_def cls.simps opn.simps apply rule using Y by simp
qed

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
  from 2(3,4,5,1,2) show ?case
  apply (induct trm1 d rule:pbeta_max.induct)
  by auto
next
case (3 L t)
  then obtain x where 4:"x \<notin> L \<union> FV t" by (meson FV_finite finite_UnI x_Ex)
  with 3 obtain d where 5: "t^FVar x >>> d" by auto
  have 6: "\<forall>y. y \<notin> FV d \<union> FV t \<union> {x} \<longrightarrow> t^FVar y >>> (\\x^d)^FVar y"
  unfolding opn'_def cls'_def 
  apply (subst(5) fv_opn_cls_id2)
  defer
  apply rule
  apply rule
  apply (rule_tac pbeta_max_cls)
  using 5 opn'_def apply auto[1]
  apply (simp add: FV_simp)
  using 4 by simp

  show ?case
  apply rule
  apply (rule_tac L="FV d \<union> FV t \<union> {x}" in pbeta_max.abs)
  apply (simp add: FV_finite)
  using 6 by auto
qed

lemma pbeta_max_closes_pbeta:
  fixes a b d
  assumes "a >>> d"
  and "a \<Rightarrow>\<parallel> b"
  shows "b \<Rightarrow>\<parallel> d"
using assms proof (induct arbitrary: b rule:pbeta_max.induct)
case (refl a)  
  show ?case using refl pbeta.cases by fastforce
next
case (reflY a) then have 1: "b = Y a" apply (cases rule: pbeta.cases) by simp
  show ?case unfolding 1 by auto
next
case (beta L al ald ar ard)
  from beta(6) show ?case
  apply (cases rule: pbeta.cases)
  proof goal_cases
  case (2 L' alb arb)
    with beta have ih: "arb \<Rightarrow>\<parallel> ard" "\<And>x. x \<notin> L \<union> L' \<Longrightarrow> alb^FVar x \<Rightarrow>\<parallel> ald^FVar x"  by simp+
    show ?case unfolding 2 apply (rule_tac L="L \<union> L'" in Lem2_5_1opn)
    defer using beta(1) 2(2) apply simp
    using ih by auto
  next
  case (1 alb arb)
    with beta have ih:  "arb \<Rightarrow>\<parallel> ard" by simp
    show ?case unfolding 1 
    using 1(2) apply (cases rule:pbeta.cases)
    apply simp
    proof goal_cases
    case (1 L' alb')
      with beta have ih2: "\<And>x. x \<notin> L \<union> L' \<Longrightarrow> alb'^FVar x \<Rightarrow>\<parallel> ald^FVar x" by simp
      show ?case
      apply (rule_tac L="L \<union> L'" in pbeta.beta)
      using 1 beta ih ih2 by auto
    qed
  qed
next
case (app al ald ar ard) 
  from app(7,1,2) show ?case
  apply (cases "App al ar" b rule:pbeta.cases)
  using app apply auto[1]
  apply simp
  by simp
next
case (abs L al ald) 
  from abs(4) show ?case 
  apply (cases rule:pbeta.cases) 
  apply simp
  proof goal_cases
  case (1 L' alb)
    with abs have ih: "\<And>x. x \<notin> L \<union> L' \<Longrightarrow> alb^FVar x \<Rightarrow>\<parallel> ald^FVar x" by simp
    show ?case
    apply (rule_tac L="L \<union> L'" in pbeta.abs)
    using 1 abs ih by auto
  qed
next
case (Y M M' \<sigma>) 
  from Y(3) show ?case
  apply (cases rule:pbeta.cases)
  proof goal_cases
  case (1 M'' N'')
    from 1(2) have 2: "M'' = Y \<sigma>" by (cases rule:pbeta.cases, simp)
    show ?case unfolding 1 2
    apply (rule pbeta.Y)
    using 1 Y by simp
  next
  case (2 M'') show ?case unfolding 2
    apply (rule pbeta.app)
    using Y 2 apply simp
    apply (rule pbeta.app)
    apply (rule pbeta.reflY)
    using Y 2 by simp
  qed
qed

lemma Lem2_5_2: 
  assumes "a \<Rightarrow>\<parallel> b"
      and "a \<Rightarrow>\<parallel> c"
    shows "\<exists>d. b \<Rightarrow>\<parallel> d \<and> c \<Rightarrow>\<parallel> d"
proof -
  obtain d where 1: "a >>> d" using pbeta_max_ex assms(2) trm_pbeta_simp1 by blast
  have "b \<Rightarrow>\<parallel> d \<and> c \<Rightarrow>\<parallel> d" 
  apply rule 
  apply (rule_tac pbeta_max_closes_pbeta)
  using 1 assms apply simp+
  apply (rule_tac pbeta_max_closes_pbeta)
  using 1 assms apply simp+
  done
  thus ?thesis by auto
qed

end