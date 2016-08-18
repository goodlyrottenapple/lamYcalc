#Nominal vs. Locally nameless {#comp-isa}
\label{chap:compIsa}

This chapter looks at the two different mechanizations of the $\lamy$ calculus, introduced in the previous chapter, namely an implementation of the calculus using nominal sets and a locally nameless (LN) mechanization. Having presented the two approaches to formalizing binders in \cref{binders}, this chapter explores the consequences of choosing either mechanization, especially in terms of technology transparency and overheads introduced as a result of the chosen mechanization.

Whilst we found that the nominal version of the definitions and proofs turned out to be more transparent than the locally nameless mechanization, there were some large overheads associated with the implementation of certain features in the $\lamy$ calculus. The LN mechanization, on the other hand, carried a small but consistent level of overhead throughout the formalization, proving that it was indeed a good compromise between implementation overheads and transparency.

##Overview

We chose the length of the implemented theory files as a simple measure of implementation overheads. As expected, the Locally nameless version of the calculus (1143 lines) was about 50% longer than the Nominal encoding (723 lines). However, this measure is not always ideal (due to the reasons outlined in \cref{mechOverheads}), and we therefore also present the comparison between the two versions in terms of the individual definitions and lemmas that correspond to each other in the two mechanizations and the informal definitions/lemmas:

\newcommand{\lem}[1]{\bf{lemma}\ \it{#1}}
\newcommand{\fun}[1]{\bf{fun}\ \it{#1}}
\newcommand{\nfun}[1]{\bf{nominal\_function}\ \it{#1}}
\newcommand{\dat}[1]{\bf{datatype}\ \it{#1}}
\newcommand{\ndat}[1]{\bf{nominal\_datatype}\ \it{#1}}
\newcommand{\induct}[1]{\bf{inductive}\ \it{#1}}


| Informal              | Nominal                               | Locally nameless                      |
|-----------------------|---------------------------------------|---------------------------------------|
| Definition of terms | \ndat{trm} | \dat{ptrm} \newline \induct{trm} |
| Definition of substitution | \nfun{subst} | \fun{opn} \newline \fun{cls} \newline \fun{subst} |
| \cref{Lemma:maxEx} ($\forall M.\ \exists M'.\ M \ggg M'$) | \lem{pbeta\_max\_ex} | \lem{pbeta\_max\_ex} \newline \lem{fv\_opn\_cls\_id2} \newline \lem{pbeta\_max\_cls} |
| \cref{Lemma:maxClose} ($\forall M, M', M''.\ M \ggg M'' \land M \gg M' \implies M' \gg M''$) | \lem{pbeta\_max\_closes\_pbeta} \newline \lem{pbeta\_cases\_2} \newline \lem{Lem2\_5\_1} \newline \lem{pbeta\_lam\_case\_ex} | \lem{pbeta\_max\_closes\_pbeta} \newline \lem{Lem2\_5\_1opn} |
| \cref{Theorem:subRedSimp} (Subject reduction for $\red^*$) | \lem{beta\_Y\_typ} \newline \lem{subst\_typ} \newline \lem{wt\_terms\_impl\_wf\_ctxt} \newline \lem{wt\_terms\_cases\_2} | \lem{beta\_Y\_typ} \newline \lem{opn\_typ} \newline \lem{wt\_terms\_impl\_wf\_ctxt} |

The table above lists the major lemmas discussed throughout this thesis, along with the names of these lemmas in the concrete implementations (these can be found in the Appendix), as well as the additional lemmas the proofs of these depend on. For example, the lemma _pbeta_max_ex_ depends on _fv_opn_cls_id2_ and _pbeta_max_cls_ (which may themselves depend on other smaller lemmas).
Overall, the mechanization using nominal sets includes 33 lemmas, whereas the locally nameless has 71 individual lemmas. The fact that whilst the LN mechanization includes more than twice as many lemmas as the nominal formalization, its only roughly 50% longer, meaning that many of these lemmas are short simple proofs, which supports our assertion that using the locally nameless representation of binders carries larger overhead, but keeps the difficulty of proving these additional lemmas low.   

The rest of this chapter provides an overview of some of the technical points of the $\lamy$ calculus mechanization which highlight the differences between the two mechanizations. However, we conclude that on the whole, neither mechanization proved to be significantly better than the other.   
This is especially true when it comes to proofs in both mechanizations. As the code printout in the Appendix clearly shows, both mechanizations have the same structure and largely the same syntax and formulation of lemmas.   
Additionally, when taking a finer grained look at the length of code by section, rather than as a whole, the lengths of the main lemmas in both mechanizations are much closer, as the overheads of the locally nameless encoding occur mainly in the definitions of terms and substitution/open/close operations:

| $\ $ | Nominal | Locally nameless |
|-------------------------------------------|:---------:|:---------:|
| Definition of $\lamy$ terms               | 15  | 11  |
| Definition of well formed terms           | -   | 15  |
| Definition of the open operation          | -   | 18  |
| Definition of substitution                | 56  | 124 |
| Definition of the close operation         | -   | 86  |
| $\beta Y$-reduction                       | 17  | 25  |
| Parallel $\beta Y$-reduction              | 17  | 27  |
| Maximal parallel $\beta Y$-reduction      | 49  | 60  |
| \cref{Lemma:maxEx}                        | 24  | 107 |
| \cref{Lemma:maxClose}                     | 156 | 145 |
| Proof of $\dip(\gg)$                      | 18  | 18  |
| Reflexive-transitive closure of $\beta Y$ | 116 | 231 |
| Simple-typing relation $\vdash$           | 238 | 258 |
| Church Rosser Theorem                     | 12  | 12  |


Whilst the LN mechanization proved to have significantly higher "obvious" mechanization overheads in terms of code length, the implementation using the nominal library proved to be more difficult to use at certain points, due to the more complex nominal sets theory that implicitly underpinned the mechanization. The LN mechanization proved to be much more simple in practice, even without any library support and the automation, which comes with using Nominal Isabelle.   
<!--Continuing with the next round of comparison between the two theorem provers, Isabelle and Agda, this point was the main reason to chose LN over nominal sets, as implementing the LN version of the calculus requires a lot less "background" theory, which was especially important in Agda, where nominal set support is a lot less mature than in Isabelle.-->


##Definitions

We give a brief overview of the basic definitions of well-typed terms and $\beta$-reduction, specific to both mechanizations. Unsurprisingly, the main differences in these definitions involve $\lambda$-binders.

###Nominal sets representation

As was shown already in \cref{binders}, nominal set representation of terms is largely identical with the informal definition, which is the main reason why this representation was chosen. This section will examine the implementation of $\lamy$ calculus in Isabelle, using the Nominal package.   

The declaration of the terms and types in Nominal Isabelle is handled using the reserved keywords **`atom\_decl`** and **`nominal\_datatype`**, which are special versions of the **`typedecl`** and **`datatype`** primitives, used in the usual Isabelle/HOL session:

~~~{.isabelle}
atom_decl name

nominal_datatype type = O | Arr type type ("_ → _")

nominal_datatype trm =
  Var name
| App trm trm
| Lam x::name t::trm  binds x in t ("Lam [_]. _" [100, 100] 100)
| Y type
~~~

The special **`binds \_ in \_`** syntax in the `Lam` constructor declares `x` to be bound in the body `t`, telling Nominal Isabelle that `Lam` terms should be identified up to $\alpha$-equivalence, where a term $\lambda x. x$ and $\lambda y. y$ are considered identical/equal, because both $x$ and $y$ are bound in the two respective terms, and can both be $\alpha$-converted to the same term, for example $\lambda z. z$. In fact, proving such a lemma in Nominal Isabelle is trivial:

~~~{.isabelle}
lemma "Lam [x]. Var x = Lam [y]. Var y" by simp
~~~

The special **`nominal\_datatype`** declaration also generates definitions of free variables/freshness and other simplification rules. (Note: These can be inspected in Isabelle, using the **`print\_theorems`** command.)

Other definitions, such as $\beta$-reduction and the notion of substitution are also unchanged with regards to the usual definition (except for the addition of the $Y$ case, which is trivial):

<div class="Definition" head="Capture-avoiding substitution">
\begin{center}
$\begin{aligned}
x[S/y] &= \begin{cases}
S & \text{if }x \equiv y\\
x & otherwise
\end{cases}\\
(MN)[S/y] &= (M[S/y])(N[S/y])\\
x\ \sharp\ y , S \implies (\lambda x.M)[S/y] &= \lambda x.(M[S/y])\\
(Y_\sigma)[S/y] &= Y_\sigma
\end{aligned}$
\end{center}
</div>

The side-condition $x\ \sharp\ y , S$ in the definition above can be read as "$x$ is fresh in $N$", namely, the atom $x$ is not the same as $y$ and does not appear in $S$, i.e. for a $\lambda$-term $M$, we have $x\ \sharp\ M$ iff $x \not\in \fv(M)$.

Whilst on paper, all this definition is unchanged from the informal presentation, there are a few caveats when it comes to actually implementing these definitions in Isabelle, using the Nominal package. Since this definition of substitution includes the freshness condition, it cannot be defined using the usual structural recursion via the **`primrec`** or **`fun`** keywords, generally used for this purpose.
Instead we have to define capture avoiding substitution using a **`nominal\_function`** declaration:

~~~{.isabelle}
nominal_function
  subst :: "trm ⇒ name ⇒ trm ⇒ trm"  ("_ [_ ::= _]" [90, 90, 90] 90)
where
  "(Var x)[y ::= s] = (if x = y then s else (Var x))"
| "(App t1 t2)[y ::= s] = App (t1[y ::= s]) (t2[y ::= s])"
| "atom x ♯ (y, s) ⟹ (Lam [x]. t)[y ::= s] = Lam [x].(t[y ::= s])"
| "(Y t)[y ::= s] = Y t"
~~~

Unlike using the usual **`fun`** declaration of a recursive function in Isabelle, where Isabelle automatically checks the definition for pattern completeness (for the term being pattern matched on) and overlap. The **`fun`** definition also automatically checks/proves termination of such recursive functions and generates simplification rules, which can be used for equational reasoning involving the function.   
Unfortunately, this isn't the case for the **`nominal\_function`** declaration, where there are several goals (13 in the case of the `subst` definition) which the user has to manually prove about the function definition, including proving termination, and pattern disjointness and completeness. This turned out to be a bit problematic, as the goals involved proving properties like:

~~~{.idris}
⋀x t xa ya sa ta.
  eqvt_at subst_sumC (t, ya, sa) ⟹
  eqvt_at subst_sumC (ta, ya, sa) ⟹
  atom x ♯ (ya, sa) ⟹ atom xa ♯ (ya, sa) ⟹ 
  [[atom x]]lst. t = [[atom xa]]lst. ta ⟹ 
  [[atom x]]lst. subst_sumC (t, ya, sa) = 
  	[[atom xa]]lst. subst_sumC (ta, ya, sa)
~~~

<!--**do i need to explain what this property is? or is it ok for illustrative purposes?**-->

Whilst most of the goals were trivial, proving cases involving $\lambda$-terms involved a substantial understanding of the internal workings of Isabelle and the Nominal package early on into the mechanization and as a novice to using Nominal Isabelle, understanding and proving these properties proved challenging.    
Whilst our formalization required only a handful of other recursive function definitions, in a different theory with significantly more function definitions, proving such goals from scratch would prove a challenge to a Nominal Isabelle newcomer as well as a tedious implementation overhead.

###Locally nameless representation

As we have seen, on paper at least, the definitions of terms and capture-avoiding substitution, using nominal sets, are unchanged from the usual informal definitions. The situation is somewhat different for the locally nameless mechanization. Since the LN approach combines the named and de Bruijn representations, there are two different constructors for free and bound variables:

####Pre-terms
<div class="Definition" head="LN pre-terms">
\label{Definition:pterms}
\begin{center}
$M::= x\ |\ n\ |\ MM\ |\ \lambda M\ |\ Y_\sigma \text{ where }x \in Var \text{ and } n \in \mathbb{N}$
\end{center}
</div>

Similarly to the de Bruijn presentation of binders, the $\lambda$-term no longer includes a bound variable, so a named representation term $\lambda x.x$ becomes $\lambda 0$ in LN. As was mentioned in \cref{binders}, the set of pre-terms, defined in \cref{Definition:pterms}, is a superset of $\lamy$ terms and includes terms which are not well formed $\lamy$ terms. 

<div class="Example">The pre-term $\lambda 3$ is not a well-formed $\lamy$ term, since the bound variable index is out of scope. In other words, there is no corresponding (named) $\lamy$ term to $\lambda 3$.
</div>

Since we don't want to work with terms that do not correspond to $\lamy$ terms, we have to introduce the notion of a _well-formed term_, which restricts the set of pre-terms to only those that correspond to $\lamy$ terms (i.e. this inductive definition ensures that there are no "out of bounds" indices in a given pre-term):

<div class="Definition" head="Well-formed terms">
\begin{center}
    \AxiomC{}
    \LeftLabel{$(fvar)$}
    \UnaryInfC{$\trm (x)$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{}
    \LeftLabel{$(Y)$}
    \UnaryInfC{$\trm (Y_\sigma)$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{$x \not\in FV(M)$}
    \AxiomC{$\trm (M^x)$}
    \LeftLabel{$(lam)$}
    \BinaryInfC{$\trm (\lambda M)$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\trm (M)$}
    \AxiomC{$\trm (M)$}
    \LeftLabel{$(app)$}
    \BinaryInfC{$\trm (MN)$}
    \DisplayProof
    \vskip 1.5em
\end{center}
</div>

Already, we see that this formalization introduces some overheads with respect to the informal/nominal encoding of the $\lamy$ calculus.    
The upside of this definition of $\lamy$ terms becomes apparent when we start thinking about $\alpha$-equivalence and capture-avoiding substitution. Since the LN terms use de Bruijn levels for bound variables, there is only one way to write the term $\lambda x.x$ or $\lambda y.y$ as a LN term, namely $\lambda 0$. As the $\alpha$-equivalence classes of named $\lamy$ terms collapse into a singleton $\alpha$-equivalence class in a LN representation, the notion of $\alpha$-equivalence becomes trivial.

As a result of using LN representation of binders, the notion of substitution is split into two distinct operations. One operation is the substitution of bound variables, called _opening_. The other is substitution, defined only for free variables.

<div class="Definition" head="Opening and substitution">We will usually assume that $S$ is a well-formed LN term when proving properties about substitution and opening. The abbreviation $M^N \equiv \{0 \to N\}M$ is used throughout this chapter.

i)	Opening:
\begin{center}
$\begin{aligned}
\{k \to S\}x &= x\\
\{k \to S\}n &= \begin{cases}
S & \text{if }k \equiv n\\
n & otherwise
\end{cases}\\
\{k \to S\}(MN) &= (\{k \to S\}M)(\{k \to S\}N)\\
\{k \to S\}(\lambda M) &= \lambda (\{k+1 \to S\}M)\\
\{k \to S\}Y_\sigma &= Y_\sigma
\end{aligned}$
\end{center}

ii)	Substitution:
\begin{center}
$\begin{aligned}
x[S/y] &= \begin{cases}
S & \text{if }x \equiv y\\
x & otherwise
\end{cases}\\
n[S/y] &= n \\
(MN)[S/y] &= (M[S/y])(N[S/y])\\
(\lambda M)[S/y] &= \lambda. (M[S/y])\\
Y_\sigma[S/y] &= Y_\sigma
\end{aligned}$
\end{center}
</div>

Having defined the _open_ operation, we turn back to the definition of well formed terms, specifically to the $(lam)$ rule, which has the precondition $\trm (M^x)$. Intuitively, for the given term $\lambda M$, the term $M^x$ is obtained by replacing all indices bound to the outermost $\lambda$ by $x$. Then, if $M^x$ is well formed, so is $\lambda M$.

<div class="Example">For example, taking the term $\lambda\lambda 0(z\ 1)$, we can construct the following proof-tree, showing that the term is well formed: 

\begin{center}
    \vskip 1.5em
	\AxiomC{}
    \LeftLabel{$(fvar)$}
	\UnaryInfC{$\trm (y)$}

	\AxiomC{}
    \LeftLabel{$(fvar)$}
	\UnaryInfC{$\trm (z)$}
	\AxiomC{}
    \LeftLabel{$(fvar)$}
	\UnaryInfC{$\trm (x)$}

    \LeftLabel{$(app)$}
	\BinaryInfC{$\trm (z\ x)$}
    \LeftLabel{$(app)$}
	\BinaryInfC{$\trm ((0(z\ x))^y)$}
    \LeftLabel{$(lam)$}
    \UnaryInfC{$\trm ((\lambda 0(z\ 1))^x)$}
    \LeftLabel{$(lam)$}
    \UnaryInfC{$\trm (\lambda\lambda 0(z\ 1))$}
    \DisplayProof
    \vskip 1.5em
\end{center}

We assumed that $x \not\equiv y \not\equiv z$ in the proof tree above and thus omitted the $x \not\in \fv \hdots$ branches, as they are not important for this example.<!--, i.e. it is always possible to find a fresh free variable that doesn't appear in a $\lamy$ term, as the set of atoms/free variables is countably-infinite and every $\lamy$ terms is finite.-->   
If on the other hand, we try construct a similar tree for a term which is obviously not well formed, such as $\lambda \lambda 2(z\ 1)$, we get a proof tree with a branch which cannot be closed ($\trm (2)$):
\newpage
$\ $
\begin{center}
	\AxiomC{$\trm (2)$}

	\AxiomC{}
    \LeftLabel{$(fvar)$}
	\UnaryInfC{$\trm (z)$}
	\AxiomC{}
    \LeftLabel{$(fvar)$}
	\UnaryInfC{$\trm (x)$}

    \LeftLabel{$(app)$}
	\BinaryInfC{$\trm (z\ x)$}
    \LeftLabel{$(app)$}
	\BinaryInfC{$\trm ((2(z\ x))^y)$}
    \LeftLabel{$(lam)$}
    \UnaryInfC{$\trm ((\lambda 2(z\ 1))^x)$}
    \LeftLabel{$(lam)$}
    \UnaryInfC{$\trm (\lambda\lambda 2(z\ 1))$}
    \DisplayProof
\end{center}
</div>

####$\beta$-reduction for LN terms
Finally, we examine the formulation of $\beta$-reduction in the LN presentation of the $\lamy$ calculus. Since we only want to perform $\beta$-reduction on valid $\lamy$ terms, the inductive definition of $\beta$-reduction in the LN mechanization now includes the precondition that the terms appearing in the reduction are well formed:$\\$

<div class="Definition" head="$\beta$-reduction (LN)">
\begin{center}
    \AxiomC{$M \red M'$}
    \AxiomC{$\trm (N)$}
    \LeftLabel{$(red_L)$}
    \BinaryInfC{$MN \red M'N$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\trm (M)$}
    \AxiomC{$N \red N'$}
    \LeftLabel{$(red_R)$}
    \BinaryInfC{$MN \red M'N$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{$ x \not\in \fv(M) \cup \fv(M')$}
    \AxiomC{$M^x \red (M')^x$}
    \LeftLabel{$(abs)$}
    \BinaryInfC{$\lambda M \red \lambda M'$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\trm (\lambda M)$}
    \AxiomC{$\trm (N)$}
    \LeftLabel{$(\beta)$}
    \BinaryInfC{$(\lambda M)N \red M^N$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\trm (M)$}
    \LeftLabel{$(Y)$}
    \UnaryInfC{$Y_\sigma M \red M (Y_\sigma M)$}
    \DisplayProof
    \vskip 1.5em
\end{center}
</div>

As expected, the _open_ operation is now used instead of substitution in the $(\beta)$ rule.    
The $(abs)$ rule is also slightly different, also using the _open_ in its precondition. Intuitively, the usual formulation of the $(abs)$ rule states that in order to prove that $\lambda x. M$ reduces to $\lambda x. M'$, we can simply "un-bind" $x$ in both $M$ and $M'$ and show that $M$ reduces to $M'$ (reasoning bottom-up from the conclusion to the premises). Since in the usual formulation of the $\lambda$-calculus, there is no distinction between free and bound variables, this change (where $x$ becomes free) is implicit. In the LN presentation, however, this operation is made explicit by opening both $M$ and $M'$ with some free variable $x$ (not appearing in either $M$ nor $M'$), which replaces the bound variables/indices (bound to the outermost $\lambda$) with $x$.   
While this definition is equivalent to the usual/informal definition, the induction principle this definition yields may not always be sufficient, especially in situations where we want to open up a term with a free variable which is not only fresh in $M$ and $M'$, but possibly in a wider context. We therefore followed the approach of @aydemir08 and re-defined the $(abs)$ rule (and other definitions involving the choice of fresh/free variables) using _cofinite quantification_:

\begin{center}
	\vskip 1.5em
    \AxiomC{$\forall x \not\in L.\ M^x \red M'^x$}
    \LeftLabel{$(abs)$}
    \UnaryInfC{$\lambda M \red \lambda M'$}
    \DisplayProof
    \vskip 1.5em
\end{center}

For an example, where this formulation using _cofinite quantification_ was necessary, see \cref{Lemma:opnClsSubst}).

##Proofs

Having described the implementations of the two binder representations along with the definitions of capture-avoiding substitution using nominal sets and the corresponding _subsitution_ and _open_ operations in the LN mechanization, we come the the main part of the comparison, namely the proof of the Church Rosser theorem. This section examines specific instances of some of the major lemmas which form parts of this bigger result. The general outline of the proof has been described in \cref{cr-def}.

###\cref{Lemma:maxEx}

The first major result in both implementations is \cref{Lemma:maxEx}, which states that for every $\lamy$ term $M$, there is a term $M'$, s.t. $M \ggg M'$.    
$\ $
<div class="Remark">
This result is trivial for $\gg$, as we can easily prove the derived rule $(refl^*)$, but not for $\ggg$:

<div class="Lemma" head="$\gg$ admits $(refl^*)$"> The following rule is admissible in the deduction system $\gg$:
\label{Lemma:reflM}

\begin{center}
  \AxiomC{}
  \LeftLabel{$(refl^*)$}
  \UnaryInfC{$M \gg M$}
  \DisplayProof
 \end{center}
<div class="proof">By induction on $M$.</div>
</div>
</div>

Since $\ggg$ restricts the use of the $(app)$ rule to terms which do not contain a $\lambda$ or $Y$ as its left-most sub term, \cref{Lemma:reflM} does not hold in $\ggg$ for terms like $(\lambda x.x)y$, namely, $(\lambda x.x)y \ggg (\lambda x.x)y$ is not a valid reduction (see \cref{Example:ggVsGgg}). It is, however, not difficult to see that such terms can simply be $\beta$-reduced until all the redexes have been contracted, so that we have $(\lambda x.x)y \ggg y$ for the term above.   
Seen as a weaker version of \cref{Lemma:reflM}, the proof of \cref{Lemma:maxEx}, at least in theory, should then only differ in the case of an application, where we have do a case analysis on the left sub-term of any given $M$.

This is indeed the case when using the nominal mechanization, where the proof looks like this:

~~~{.isabelle xleftmargin=1em linenos=true escapeinside=||}
lemma pbeta_max_ex:
  fixes M
  shows "∃M'. M >>> M'"
apply (induct M rule:trm.induct)
apply auto
apply (case_tac "not_abst S")
apply (case_tac "not_Y S")
apply auto[1]
proof goal_cases
case (1 P Q P' Q')
  then obtain |σ| where 2: "P = Y σ" using not_Y_ex by auto
  have "App (Y σ) Q >>> App Q' (App (Y σ) Q')"
  apply (rule_tac pbeta_max.Y)
  by (rule 1(2))
  thus ?case unfolding 2 by auto
next
case (2 P Q P' Q')
  thus ?case
  apply (nominal_induct P P' avoiding: Q Q' rule:pbeta_max.strong_induct)
  by auto
qed
~~~

After applying induction and calling `auto`, which is Isabelle's automatic prover that does simple term rewriting and basic proof search, we can inspect the remaining goals at line 5, to see that the only goal that remains is the case of $M$ being an application, naley we have to prove the following:

\begin{center}
$\forall S\ T\ U\ V.\ S \ggg U \implies T \ggg V \implies \exists M'.\ ST \ggg M'$
\end{center}

<!--
goal (1 subgoal):
 1. ⋀trm1 trm2 M' M'a.
       trm1 >>> M' ⟹ trm2 >>> M'a ⟹ ∃M'. App trm1 trm2 >>> M'
-->

Lines 6 and 7 in the proof script then correspond to doing a case analysis on $S$ (where $M = ST$). We end up with 3 goals, corresponding to $S$ either being a $\lambda$-term, $Y$-term or neither (shown below in reverse order):

~~~{.idris}
 1. ... not_abst S ⟹ not_Y S ⟹ ∃M'. App S T >>> M'
 2. ... not_abst S ⟹ ¬ not_Y S ⟹ ∃M'. App S T >>> M'
 3. ... ¬ not_abst S ⟹ ∃M'. App S T >>> M'
~~~

The first goal is discharged by calling `auto` again (line 8), since we can simply apply the $(app)$ rule in this instance.
The two remaining cases are discharged with the additional information that $S$ is either a $\lambda$-term or a $Y$-term.

So far, we have looked at the version of the proof using nominal Isabelle and this is especially apparent in line 19, where we use the stronger `nominal\_induct` rule, with the extra parameter `avoiding: Q Q'`, which ensures that any new bound variables will be sufficiently fresh with regards to `Q` and `Q'`, in that the fresh variables won't appear in either of the terms.    
Since bound variables are distinct in the LN representation, the equivalent proof simply uses the usual induction rule (line 19):

~~~{.isabelle xleftmargin=1em linenos=true escapeinside=||}
lemma pbeta_max_ex:
  fixes M assumes "trm M"
  shows "∃M'. M >>> M'"
using assms apply (induct M rule:trm.induct)
apply auto
apply (case_tac "not_abst t1")
apply (case_tac "not_Y t1")
apply auto[1]
proof goal_cases
case (1 P Q P' Q')
  then obtain |σ| where 2: "P = Y σ" using not_Y_ex by auto
  have "App (Y σ) Q >>> App Q' (App (Y σ) Q')"
  apply (rule_tac pbeta_max.Y)
  by (rule 1(4))
  thus ?case unfolding 2 by auto
next
case (2 P Q P' Q')
  from 2(3,4,5,1,2) show ?case
  apply (induct P P' rule:pbeta_max.induct)
  by auto
next
case (3 L M)
  then obtain x where 4:"x ∉ L ∪ FV M" by (meson FV_finite finite_UnI x_Ex)
  with 3 obtain M' where 5: "M^FVar x >>> M'" by auto

  have 6: "⋀y. y ∉ FV M' ∪ FV M ∪ {x} ⟹ M^FVar y >>> (\\x^M')^FVar y"
  unfolding opn'_def cls'_def 
  apply (subst(3) fv_opn_cls_id2[where x=x])
  using 4 apply simp
  apply (rule_tac pbeta_max_cls)
  using 5 opn'_def by (auto simp add: FV_simp)

  show ?case
  apply rule
  apply (rule_tac L="FV M' ∪ FV M ∪ {x}" in pbeta_max.abs)
  using 6 by (auto simp add: FV_finite)
qed
~~~

As one can immediately see, this proof proceeds exactly in the same fashion, as the nominal one, up to line 20. However, unlike in the nominal version of the proof, in the LN proof, the `auto` call at line 8 could not automatically prove the case where $M$ is a $\lambda$-term.    
This is perhaps not too surprising, since the LN encoding is a lot more "bare bones", and thus there is little that would aid Isabelle's automation. The nominal package, on the other hand, was designed to make reasoning with binders as painless as possible, which definitely shows in this example.

When we compare the two goals for the $\lambda$ case in both versions of the proof, we clearly see the differences in the treatment of binders:

\begin{center}
$\begin{aligned}
\textbf{Nominal:}\ \ &\forall x\ M.\ \exists M'.\ M \ggg M' \implies \exists M'. \lambda x. M \ggg M'\\
\textbf{Locally nameless:}\ \ &\forall L\ M.\ \textbf{fin}\ L \implies \trm(\lambda.M) \implies (\forall x \not\in L.\ \exists M''.\ M^x \ggg M'')\\
&\implies \exists M'.\ \lambda.M \ggg M'
\end{aligned}$
\end{center}

<!--
**Nominal:**

⋀x M. ∃M'. M >>> M' ⟹ ∃M'. Lam [x]. M >>> M'

**Locally nameless:**

⋀L M. finite L ⟹
       (⋀x. x ∉ L ⟹ trm M^FVar x) ⟹
       (⋀x. x ∉ L ⟹ ∃M''. M^FVar x >>> M'') ⟹ ∃M'. Lam M >>> M'
-->

Unlike in the nominal proof, where from $M \ggg M'$ we get $\lambda x.M \ggg \lambda x.M'$ by $(abs)$ immediately, the proof of $\exists M'.\ \lambda.M \ggg M'$ in the LN mechanization is not as trivial.    
The difficulty arises with the precondition $\forall x \not\in L.\ M^x \ggg (M')^x$ in the LN version of the $(abs)$ rule:

\begin{center}
	\vskip 1.5em
    \AxiomC{$\exists M'.\ \forall x \not\in L.\ M^x \ggg (M')^x$}
    \LeftLabel{$(abs)$}
    \UnaryInfC{$\exists M'.\ \lambda M \ggg \lambda M'\footnotemark$}
    \DisplayProof
    \vskip 1.5em

\footnotetext{ 
While the original goal is $\exists M'.\ \lambda.M \ggg M'$, since there is only one possible ``shape'' for the right-hands side term, namely $M'$ must be a \(\lambda\)-term, we can easily rewrite this goal as $\exists M'.\ \lambda.M \ggg \lambda.M'$.
}
\end{center}

This version of the rule with the existential quantification shows the subtle difference between the inductive hypothesis $\forall x \not\in L.\ \exists M'.\ M^x \ggg (M')^x$ [^5] we have, and the premise $\exists M'.\ \forall x \not\in L.\ M^x \ggg (M')^x$ that we want to show. In order to prove the latter, we assume that there is some $M'$ for a specific $x \not\in L$ s.t. $M^x \ggg (M')^x$. 

[^5]: It can easily be shown that any pre-term $M$ can be written using another pre-term $N$ s.t. $M \equiv N^x$ for some $x$.

At this point, we cannot proceed without re-examining the definition of _opening_, especially in that this operation lacks an inverse. Whereas in a named representation, where bound variables are bound via context only, LN terms have specific constructors for free and bound variables together with an operation for turning bound variables into free variables, namely the _open_ function. In this proof, however, we need the inverse operation, wherein we turn a free variable into a bound one. We call this the _close_ operation:

<div class="Definition" head="Close operation">This definition was adapted from the @aydemir08 paper. We adopt the following convention, writing $\cls M \equiv \{0 \leftarrow x\}M$.
\begin{center}
$\begin{aligned}
\{k \leftarrow x\}y &= \begin{cases}
k & \text{if }x \equiv y\\
y & otherwise
\end{cases}\\
\{k \leftarrow S\}n &= n\\
\{k \leftarrow S\}(MN) &= (\{k \leftarrow S\}M)(\{k \leftarrow S\}N)\\
\{k \leftarrow S\}(\lambda M) &= \lambda (\{k+1 \leftarrow S\}M)\\
\{k \leftarrow S\}Y_\sigma &= Y_\sigma
\end{aligned}$
\end{center}
</div>

<div class="Example">To demonstrate the close operation, take the term $\lambda xy$. Applying the close operation with the free variable $x$, we get $\cls (\lambda xy) = \lambda 1y$. Whilst the original term might have been well formed, the closed term, as is the case here, may not be.</div>

Intuitively, it is easy to see that closing a well formed term and then opening it with the same free variable produces the original term, namely $(\cls M)^x \equiv M$. This can be made even more general with the following lemma about the relationship between the open, close and substitution operations:

<div class="Lemma">$\trm(M) \implies \{k \to y\}\{k \leftarrow x\} M = M[y/x]$
\label{Lemma:opnClsSubst}
<div class="proof">
By induction on the relation $\trm(M)$. The rough outline of the $(lam)$ case, which is the only non-trivial case, is shown below:

By _IH_, we have $\forall z \not\in L.\ \{k+1 \to y\} \{k+1 \leftarrow x\} M^z = (M^z)[y/x]$. Then:
\begin{align}
\{k \to y\} \{k \leftarrow x\} (\lambda M) = (\lambda M)[y/x] &\iff\\
\lambda(\{k+1 \to y\} \{k+1 \leftarrow x\} M) = \lambda (M[y/x])&\iff\\
\{k+1 \to y\} \{k+1 \leftarrow x\} M = M[y/x]&\iff\\
\{0 \to z\} \{k+1 \to y\} \{k+1 \leftarrow x\} M = \{0 \to z\} (M[y/x])&\iff\\
\{k+1 \to y\} \{k+1 \leftarrow x\} \{0 \to z\} M = \{0 \to z\} (M[y/x])&\iff\\
\{k+1 \to y\} \{k+1 \leftarrow x\} \{0 \to z\} M = (\{0 \to z\} M)[y/x]&
\end{align}

Starting from the goal (4.1), we expand the definitions of _open_, _close_ and substitution for the $\lambda$ case in (4.2). (4.3) holds by injectivity of $\lambda$. Then, by choosing a sufficiently fresh $z$ that does not appear in the given context $L$ as well as in neither $\fv(M)$ nor $\{x, y\}$, we have (4.4). We can reorder the open and close operations in (4.5) because it can never be the case that $k+1 = 0$ and $z$ is different from both $x$ and $y$. Finally, (4.6) follows from the fact that we have chosen a $z$ that does not appear in $M$ and is different from $y$.   
We can now see that $\{k+1 \to y\} \{k+1 \leftarrow x\} \{0 \to z\} M = (\{0 \to z\} M)[y/x]$ is in fact the _IH_ $\{k+1 \to y\} \{k+1 \leftarrow x\} M^z = (M^z)[y/x]$.
</div></div>

Having defined the _close_ operation and shown that it satisfies certain properties with respect to the _open_ operation and substitution, we can now "close" the term $M'$, with respect to the $x$ we fixed earlier and thus show that $\forall y \not\in L.\ M^y \ggg (\cls M')^y$.

<!--**Should I go into more detail here or just wrap it up by saying how much more code was necessary over the nominal version??**-->

###\cref{Lemma:maxClose}

While it may seem that the nominal mechanization was universally more concise and easier to work in than the locally nameless implementation, there were a few instances where using the nominal library turned out to be more difficult to understand and use. One such instance, namely defining a **`nominal\_function`**, was already discussed. Another example can be found in the implmentation of \cref{Lemma:maxClose}, which is stated as:

\begin{center}
$\forall M, M', M_{max}.\ M \ggg M_{max} \land M \gg M' \implies M' \gg M_{max}$
\end{center}

The proof of this lemma proceeds by induction on the relation $\ggg$. Here we will focus on the $(\beta)$ case, i.e. when we have $M \ggg M_{max}$ by the application of $(\beta)$, first giving an informal proof and then focusing on the implementation specifics in both mechanizations:

####$(\beta)$ case

We have $M \equiv (\lambda x. P) Q$ and $M_{max} \equiv P_{max}[Q_{max}/x]$, and therefore $(\lambda x. P) Q \ggg P_{max}[Q_{max}/x]$ and $(\lambda x. P) Q \gg M'$.    
By performing case analysis on the reduction $(\lambda x. P) Q \gg M'$, we know that $M' \equiv (\lambda x. P') Q'$ or $M' \equiv P'[Q'/x]$ for some $P', Q'$, since only these two trees are valid:

\begin{center}
	\AxiomC{$\vdots$}
	\UnaryInfC{$P \gg P'$}
	\LeftLabel{$(abs)$}
	\UnaryInfC{$\lambda x. P \gg \lambda x. P'$}
	\AxiomC{$\vdots$}
	\UnaryInfC{$Q \gg Q'$}
	\LeftLabel{$(app)$}
	\BinaryInfC{$(\lambda x. P) Q \gg (\lambda x. P') Q'$}
	\DisplayProof
	\ \ \ \ \ \ or\ \ \ \ \ \ 
	\AxiomC{$\vdots$}
	\UnaryInfC{$P \gg P'$}
	\AxiomC{$\vdots$}
	\UnaryInfC{$Q \gg Q'$}
	\LeftLabel{$(\beta)$}
	\BinaryInfC{$(\lambda x. P) Q \gg P'[Q'/x]$}
	\DisplayProof
	\vskip 1.5em
\end{center}
</div>

For the first case, where $M' \equiv (\lambda x. P') Q'$, by _IH_, we have $P' \gg P_{max}$ and $Q' \gg Q_{max}$. Thus, we can prove that $M' \gg P_{max}[Q_{max}/x]$:

\begin{center}
	\vskip 1.5em
	\AxiomC{}
	\LeftLabel{$(IH)$}
	\UnaryInfC{$P' \gg P_{max}$}
	\AxiomC{}
	\LeftLabel{$(IH)$}
	\UnaryInfC{$Q' \gg Q_{max}$}
	\LeftLabel{$(\beta)$}
	\BinaryInfC{$(\lambda x. P') Q' \gg P_{max}[Q_{max}/x]$}
	\DisplayProof
	\vskip 1.5em
\end{center}

In the case where $M' \equiv P'[Q'/x]$, we also have $P' \gg P_{max}$ and $Q' \gg Q_{max}$ by _IH_. The result $M' \gg P_{max}[Q_{max}/x]$ follows from the following auxiliary lemma:

<div class="Lemma" head="Parallel substitution">
\label{Lemma:parRed}The following rule is admissible in $\gg$:

\begin{center}
	\vskip 1.5em
	\AxiomC{$M \gg M'$}
	\AxiomC{$N \gg N'$}
	\LeftLabel{$(||_{subst})$}
	\BinaryInfC{$M[N/x] \gg M'[N'/x]$}
	\DisplayProof
	\vskip 1.5em
\end{center}
</div>

####Nominal implementation

The code below shows the proof of the $(\beta)$ case, described above:

~~~{.isabelle xleftmargin=1em linenos=true}
case (beta x Q Qmax P Pmax)
  from beta(1,7) show ?case
  apply (rule_tac pbeta_cases_2)
  apply (simp, simp)
  proof -
  case (goal2 Q' P')
    with beta have "P' ≫ Pmax" "Q' ≫ Qmax" by simp+
    thus ?case unfolding goal2 apply (rule_tac Lem2_5_1) by simp+
  next
  case (goal1 P' Q')
    with beta have ih: "P' ≫ Pmax" "Q' ≫ Qmax" by simp+
    show ?case unfolding goal1 
    apply (rule_tac pbeta.beta) using goal1 beta ih
    by simp_all
  qed
~~~

There were a few quirks when implementing this proof in the nominal mechanization, specifically in line 3, where the case analysis on the shape of $M'$ needed to be performed. Applying the automatically generated `pbeta.cases` rule yielded the following goal for the case where $M' \equiv P'[Q'/x]$:

~~~{.idris}
 2. ⋀xa Q' R P'.
       [[atom x]]lst. P = [[atom xa]]lst. R ⟹
       M' = P' [xa ::= Q'] ⟹
       atom xa ♯ Q ⟹ atom xa ♯ Q' ⟹ R ≫ P' ⟹ Q ≫ Q' ⟹ 
       M' ≫ Pmax [x ::= Qmax]
~~~

<!-- 2. ⋀xa N' M M'. [[atom x]]lst. P = [[atom xa]]lst. M ⟹ b = M' [xa ::= N'] ⟹ atom xa ♯ Q ⟹ atom xa ♯ N' ⟹ M ≫ M' ⟹ Q ≫ N' ⟹ b ≫ Pmax [x ::= Qmax]-->

Obviously, this is not the desired shape of the goal, because we obtained a weaker premise, where we have some $R$, such that $\lambda x. P \equiv_\alpha \lambda xa. R$ (this is essentially what `[[atom x]]lst. P = [[atom xa]]lst. R` states) and therefore we get a $P'$ where $M' \equiv P'[Q'/xa]$. What we actually want is a term $P'$ s.t. $M' \equiv P'[Q'/x]$, i.e. $x = xa$. In order to "force" $x$ and $xa$ to actually be the same atom, we had to prove the following "cases" lemma: 

~~~{.isabelle escapeinside=||}
lemma pbeta_cases_2:
  shows "atom x ♯ t ⟹ App (Lam [x]. s) t ≫ a2 ⟹ 
    (⋀s' t'. a2 = App (Lam [x]. s') t' ⟹ atom x ♯ t' ⟹ 
    	s ≫ s' ⟹ t ≫ t' ⟹ P) ⟹
    (⋀t' s'. a2 = s' [x ::= t'] ⟹ atom x ♯ t ⟹ atom x ♯ t' ⟹ 
    	s ≫ s' ⟹ t ≫ t' ⟹ P) ⟹ P"
|$\texttt{\vdots}$|
~~~

In the lemma above, `(⋀t' s'. a2 = s' [x ::= t'] ⟹ atom x ♯ t ⟹ atom x ♯ t' ⟹ s ≫ s' ⟹ t ≫ t' ⟹ P) ⟹ P` corresponds to the case with the premises we want to have, instead of the ones we get from the "cases" lemma generated as part of the definition of $\gg$.    

The proof of this lemma required proving another lemma shown below, which required descending into nominal set theory that was previously mostly hidden away from the mechanization (the proofs of the `have` lemmas were omitted for brevity):

~~~{.isabelle}
lemma "(Lam [x]. s) ≫ s' ⟹ ∃t. s' = Lam [x]. t ∧ s ≫ t"
proof (cases "(Lam [x]. s)" s' rule:pbeta.cases, simp)
  case (goal1 _ _ x')
    then have 1: "s ≫ ((x' ↔ x) ∙ M')" ...
    from goal1 have 2: "(x' ↔ x) ∙ s' = Lam [x]. ((x' ↔ x) ∙ M')" ...
    from goal1 have "atom x ♯ (Lam [x']. M')"  using fresh_in_pbeta ...
    with 2 have "s' = Lam [x]. ((x' ↔ x) ∙ M')" ...
    with 1 show ?case by auto
qed
~~~

Clearly, the custom "cases" lemma was necessary from a purely technical view, as it would be deemed too trivial to bother proving in an informal setting. The need for such a lemma also demonstrates that whilst the nominal package package tries to hide away the details of the theory, every once in a while, the user has to descent into nominal set theory, to prove certain properties about binders, not handled by the automation.    
For us, the nominal package thus proved to be a double edged sword, as it initially provided a fairly low cost of entry (there was practically no need to understand any nominal set theory to get started), but proved to be much more challenging to understand in certain places, such as when proving `pbeta\_cases\_2`.    
Whilst the finial `pbeta\_cases\_2` proof turned out to be fairly short thanks to automation of the nominal set theory, it took some time to work out the proof outline in such a ways as to leverage Isabelle's automation to a high degree.    
The LN mechanization, whilst having bigger overheads in terms of extra definitions and lemmas that had to be proven "by hand", was in fact a lot more transparent as a result, as the degree of difficulty after the initial cost of entry did not rise significantly with more complicated lemmas.

####LN implementation

The troublesome case analysis in the Nominal version of the proof was much more straight forward in the LN proof. In fact, there was no need to prove a separate lemma similar to `pbeta\_cases\_2`, since the auto-generated `pbeta.cases` was sufficient. The only overhead in this version of the lemma came from the use of \cref{Lemma:parRed}, in that the lemma was first proved in it's classical formulation using substitution, but due to the way substitution of bound terms is handled in the LN mechanization (using the _open function_), a "helper" lemma was proved to convert this result to one using _open_:

<div class="Lemma" head="Parallel open">
\label{Lemma:parOpn}The following rule is admissible in the LN version of $\gg$:
\begin{center}
	\vskip 1.5em
	\AxiomC{$\forall x \not\in L.\ M^x \gg M'^x$}
	\AxiomC{$N \gg N'$}
	\LeftLabel{$(||_{open})$}
	\BinaryInfC{$M^N \gg M'^{N'}$}
	\DisplayProof
	\vskip 1.5em
\end{center}
</div>

The reason why \cref{Lemma:parOpn} wasn't proved directly is partially due to the order of implementation of the two mechanizations of the $\lamy$ calculus. Since the nominal version, along with all the proofs was carried out first, the LN version of the calculus ended up being more of a port of the nominal theory into a locally nameless setting.    
The LN mechanization, being a port of the nominal theory, has both advantages and disadvantages. On the one hand, it ensures a greater consistency between the two theories and easier direct comparison of lemmas, but on the other hand, it meant that certain lemmas could have been made shorter and more "tailored" to the LN mechanization.
