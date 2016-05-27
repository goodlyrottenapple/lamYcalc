theory Test
imports Main begin

datatype lam = Var nat ("X _") | App lam lam ("[_ $ _]") | Lam nat lam ("\\_.[_]")
datatype dB = Var nat ("X' _") | App dB dB ("{_ $ _}") | Lam dB ("\\{_}")

fun dB_to_lam' :: "nat \<Rightarrow> dB \<Rightarrow> lam" where
"dB_to_lam' k (dB.Var m) = (if m \<ge> k then lam.Var (m-k) else lam.Var(k-m))" |
"dB_to_lam' k (dB.App u v) = lam.App (dB_to_lam' k u) (dB_to_lam' k v)" |
"dB_to_lam' k (dB.Lam u) = lam.Lam k (dB_to_lam' (k+1) u)"

value "dB_to_lam' 0 (\\{\\{\\{{{X' 2 $ X' 0} $ X' 3}}}})"

fun find' :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat option" ("_ {{ _ }}") where
"find' l n = (case find (\<lambda>x. fst x = n) l of Some r \<Rightarrow> Some (snd r) | None \<Rightarrow> None)"


value "[(1,2),(2,3),(3,10)] {{2}}"

fun oplus :: "(nat \<times> nat) list \<Rightarrow> (nat \<times> nat) \<Rightarrow> (nat \<times> nat) list" (infix "\<oplus>" 100) where
"oplus l (f,s) = (case l{{f}} of None \<Rightarrow> (f,s)#l | Some _ \<Rightarrow> map (\<lambda>x. (if fst x = f then (f,s) else x)) l)"

value "([(1,2),(2,3),(3,10)] ){{4}}"


fun lam_to_dB' :: "nat \<Rightarrow> lam \<Rightarrow> dB" where
"lam_to_dB' k (lam.Var m) = (if m \<ge> k then dB.Var m else dB.Var (k-m-1))" |
"lam_to_dB' k (lam.App u v) = dB.App (lam_to_dB' k u) (lam_to_dB' k v)" |
"lam_to_dB' k (lam.Lam m u) = dB.Lam (lam_to_dB' (k+1) u)"


fun lam_to_dB'' :: "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> lam \<Rightarrow> dB" where
"lam_to_dB'' k m (lam.Var n) = dB.Var (case m{{n}} of Some n' \<Rightarrow> k-n'-1 | None \<Rightarrow> k+n)" |
"lam_to_dB'' k m (lam.App u v) = dB.App (lam_to_dB'' k m u) (lam_to_dB'' k m v)" |
"lam_to_dB'' k m (lam.Lam x u) = dB.Lam (lam_to_dB'' (k+1) (m \<oplus> (x, k)) u)"



fun dB_to_lam'' :: "nat \<Rightarrow> nat \<Rightarrow> dB \<Rightarrow> lam" where
"dB_to_lam'' b k (dB.Var n) = (if n \<ge> k then lam.Var (n-k) else lam.Var(k-n-1+b))" |
"dB_to_lam'' b k (dB.App u v) = lam.App (dB_to_lam'' b k u) (dB_to_lam'' b k v)" |
"dB_to_lam'' b k (dB.Lam u) = lam.Lam (k+b) (dB_to_lam'' b (k+1) u)"

fun max_free :: "nat \<Rightarrow> dB \<Rightarrow> nat" where
"max_free k (dB.Var n) = (if n \<ge> k then n-k else 0)" |
"max_free k (dB.App u v) = max (max_free k u) (max_free k v)" |
"max_free k (dB.Lam u) = (max_free (k+1) u)"


value "(\<lambda>y x. lam_to_dB'' y [] (dB_to_lam'' (Suc (max_free y x)) y x))0  (X' 9)"



value "lam_to_dB'' 0 [] ( (\<lambda>x. dB_to_lam'' ((max_free 0 x) + 1) 0 x)({ (\\{ \\{X' 4} }) $ X' 2 }) )"


lemma 1: 
fixes x ::dB
assumes "b < (max_free 0 x)"
shows "lam_to_dB'' k [] (dB_to_lam'' b k x) = x"
using assms 
thm dB_to_lam''.induct
apply (induct x)

apply auto
unfolding dB_to_lam''.simps
apply (case_tac "k \<le> n")
apply simp
apply simp
unfolding lam_to_dB''.simps
apply simp

value "lam_to_dB'' 0 [] (\\11.[\\10.[X 11]])"






value "dB_to_lam' 0 (\\{\\{\\{ { { X' 2 $ X' 1} $ X' 8} } } })"


value "lam_to_dB'' 1 [] (\\0.[\\1.[\\2.[[[X 0 $ X 2] $ X 3]]]])"
value "lam_to_dB'' 1 [] (\\4.[\\2.[\\2.[[[X 4 $ X 2] $ X 3]]]])"

value "dB_to_lam' 1 (\\{\\{\\{ { {X' 3 $ X' 1} $ X' 7} } } })"


value "find"

fun canonical' :: "nat \<Rightarrow> lam \<Rightarrow> bool" where
"canonical' k (X x) = True" |
"canonical' k ([u $ v]) = ((canonical' k u) \<and> (canonical' k v))" |
"canonical' k (\\x.[u]) = (if x \<noteq> k then False else canonical' (k+1) u)"

value "canonical' 0 (\\0.[\\Suc 0.[\\Suc (Suc 0).[[[X 0 $ X Suc (Suc 0)] $ X Suc (Suc (Suc 0))]]]])"

lemma db_lam_db_id': "((lam_to_dB'' k []) \<circ> (dB_to_lam'' k)) x = x"
unfolding comp_apply
apply (induct x arbitrary:k)
apply auto


lemma lam_db_lam_id': "canonical' k x \<Longrightarrow> ((dB_to_lam' k) \<circ> (lam_to_dB' k)) x = x"
proof (induct x arbitrary:k)
case Var thus ?case by auto
next
case App thus ?case by auto
next
case (Lam x u) 
  thus ?case unfolding comp_def lam_to_dB'.simps dB_to_lam'.simps
  by (metis Lam.hyps canonical'.simps(3) comp_eq_dest_lhs)
qed

definition lam_to_dB where "lam_to_dB l \<equiv> lam_to_dB' 0 l"
definition dB_to_lam where "dB_to_lam l \<equiv> dB_to_lam' 0 l"
definition canonical where "canonical l \<equiv> canonical' 0 l"


lemma db_lam_db_id: "(lam_to_dB \<circ> dB_to_lam) = id"
using lam_to_dB_def dB_to_lam_def db_lam_db_id' by auto

lemma lam_db_lam_id: "canonical x \<Longrightarrow> (dB_to_lam \<circ> lam_to_dB) x = x"
using lam_to_dB_def dB_to_lam_def canonical_def lam_db_lam_id' by simp


end