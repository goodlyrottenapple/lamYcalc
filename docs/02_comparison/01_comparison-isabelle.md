#Nominal vs. Locally nameless {#comp-isa}


This chapter looks at the two different mechanizations of the $\lamy$ calculus, introduced in the previous chapter, namely an implementation of the calculus using nominal sets and a locally nameless (LN) mechanization. Having presented the two approaches to formalizing binders in [Chapter 2](#binders), this chapters explores the consequences of choosing either mechanization, especially in terms of technology transparency and overheads introduced as a result of the chosen mechanization.

##Capture-avoiding substitution and $\beta$-reduction

We give a brief overview of the basic definitions of well-typed terms and $\beta$-reduction, specific to both mechanizations. Unsurprisingly, the only real differences in these definitions appear in terms involving $\lambda$-binders.

###Nominal sets representation

As was shown already, nominal set representation of terms is largely identical with the informal definitions, which is the main reason why this representation was chosen. This section will examine the implementation of $\lamy$ calculus in Isabelle, using the Nominal package.   
We start, by examining the definition of untyped $\beta$-reduction, defined for the $\lamy$ calculus:

<div class="Definition" head="$\beta$-reduction">
\label{beta-red-nom}
$\\$
\begin{center}
    \AxiomC{$M \Rightarrow M'$}
    \LeftLabel{$(red_L)$}
    \UnaryInfC{$MN \Rightarrow M'N$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$N \Rightarrow N'$}
    \LeftLabel{$(red_R)$}
    \UnaryInfC{$MN \Rightarrow M'N$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{$M \Rightarrow M'$}
    \LeftLabel{$(abs)$}
    \UnaryInfC{$\lambda x. M \Rightarrow \lambda x. M'$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{}
    \LeftLabel{$(\beta)$}
    \RightLabel{$(x\ \sharp\ N)$}
    \UnaryInfC{$(\lambda x. M)N \Rightarrow M[N/x]$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{}
    \LeftLabel{$(Y)$}
    \UnaryInfC{$Y_\sigma M \Rightarrow M (Y_\sigma M)$}
    \DisplayProof
	\vskip 1.5em
\end{center}
</div>

This definition, with the exception of the added $(Y)$ rule is the standard definition of the untyped $\beta$-reduction found in literature (**link?**). The $\sharp$ symbol is used to denote the _freshness_ relation in nominal set theory. The side-condition $x\ \sharp\ N$ in the $(\beta)$ rule can thus be read as "$x$ is fresh in $N$", namely, the atom $x$ does not appear in $N$. For a $\lambda$-term $M$, we have $x\ \sharp\ M$ iff $x \not\in \fv(M)$, where we take the usual definition of \fv:

<div class="Definition" >The inductively defined $\fv$ is the set of _free variables_ of a $\lambda$-term $M$.
\begin{align*} 
\fv(x) &= \{ x \}\\
\fv(MN) &= \fv(M) \cup \fv(N)\\
\fv(\lambda x. M) &= \fv(M) \setminus \{ x \}\\
\fv(Y_\sigma) &= \emptyset
\end{align*}
</div>

The definition of substitution, used in the $(\beta)$ rule is also unchanged with regards to the usual definition (except for the addition of the $Y$ case, which is trivial):

<div class="Definition" head="Capture-avoiding substitution">
\begin{align*} 
x[S/y] &= \begin{cases}
S & \text{if }x \equiv y\\
x & otherwise
\end{cases}\\
(MN)[S/y] &= (M[S/y])(N[S/y])\\
x\ \sharp\ y , S \implies (\lambda x.M)[S/y] &= \lambda x.(M[S/y])\\
(Y_\sigma)[S/y] &= Y_\sigma
\end{align*}
</div>

####Nominal Isabelle implementation
Whilst on paper, all these definitions are unchanged from the usual presentation, there are a few caveats when it comes to actually implementing these definitions in Isabelle, using the Nominal package. The declaration of the terms and types is handled using the reserved keywords **`atom\_decl`** and **`nominal\_datatype`**, which are special versions of the **`typedecl`** and **`datatype`** primitives, used in the usual Isabelle/HOL session:

~~~{.isabelle}
atom_decl name

nominal_datatype type = O | Arr type type ("_ → _")

nominal_datatype trm =
  Var name
| App trm trm
| Lam x::name l::trm  binds x in l ("Lam [_]. _" [100, 100] 100)
| Y type
~~~

The special **`binds \_ in \_`** syntax in the `Lam` constructor declares `x` to be bound in the body `l`, telling Nominal Isabelle that `Lam` terms should be **?equated up to $\alpha$-equivalence?**, where a term $\lambda x. x$ and $\lambda y. y$ are considered equal, because both $x$ and $y$ are bound in the two respective terms, and can both be $\alpha$-converted to the same term, for example $\lambda z .z$. In fact, proving such a lemma is trivial:

~~~{.isabelle}
lemma "Lam [x]. Var x = Lam [y]. Var y" by simp
~~~

The specialized **`nominal\_datatype`** declaration also generates definitions of free variables/freshness and other simplification rules. (Note: These can be inspected in Isabelle, using the **`print\_theorems`** command.)

Next, we define capture avoiding substitution, using a **`nominal\_function`** declaration:

~~~{.isabelle}
nominal_function
  subst :: "trm ⇒ name ⇒ trm ⇒ trm"  ("_ [_ ::= _]" [90, 90, 90] 90)
where
  "(Var x)[y ::= s] = (if x = y then s else (Var x))"
| "(App t1 t2)[y ::= s] = App (t1[y ::= s]) (t2[y ::= s])"
| "atom x ♯ (y, s) ⟹ (Lam [x]. t)[y ::= s] = Lam [x].(t[y ::= s])"
| "(Y t)[y ::= s] = Y t"
~~~

Whilst using **`nominal\_datatype`** is automatic and requires no user input, the declaration of a function in Nominal Isabelle is less straightforward. Unlike using the usual "**`fun`**" declaration of a recursive function in Isabelle, where the theorem prover can automatically prove properties like termination or pattern exhaustiveness, there are several goals (13 in the case of the `subst` definition) which the user has to manually prove for any function using recursive nominal data types, such as the $\lamy$ terms. This turned out to be a bit problematic, as the goals involved proving properties like:

~~~{.idris}
⋀x t xa ya sa ta.
  eqvt_at subst_sumC (t, ya, sa) ⟹
  eqvt_at subst_sumC (ta, ya, sa) ⟹
  atom x ♯ (ya, sa) ⟹ atom xa ♯ (ya, sa) ⟹ 
  [[atom x]]lst. t = [[atom xa]]lst. ta ⟹ 
  [[atom x]]lst. subst_sumC (t, ya, sa) = 
  	[[atom xa]]lst. subst_sumC (ta, ya, sa)
~~~

**do i need to explain what this property is? or is it ok for illustrative purposes?**

Whilst most of the goals were trivial, proving cases involving $\lambda$-terms involved a substantial understanding of the internal workings of Isabelle and the Nominal package and as a novice to using Nominal Isabelle, understanding and proving these properties proved challenging. The proof script for the definition of substitution was actually **lifted/copied?** from the sample document, found in the Nominal package documentation, which had a definition of substitution for the untyped $\lambda$-calculus similar enough to be adaptable for the $\lamy$ calculus.    
Whilst this formalization required only a handful of other recursive function definitions, most of which could be copied from the sample document, in a different theory with significantly more function definitions, proving such goals from scratch would prove a challenge to a Nominal Isabelle newcomer as well as a significant implementation overhead.

###Locally nameless representation

As we have seen, on paper at least, the definitions of terms and capture-avoiding substitution, using nominal sets, are unchanged from the usual informal definitions. The situation is somewhat different for the locally nameless mechanization. Since the LN approach combines the named and de Bruijn representations, there are two different constructors for free and bound variables:

####Pre-terms
<div class="Definition" head="LN pre-terms">
\label{pterms}
$$M::= x\ |\ n\ |\ MM\ |\ \lambda M\ |\ Y_\sigma \text{ where }x \in Var \text{ and } n \in Nat$$
</div>

Similarly to the de Bruijn presentation of binders, the $\lambda$-term no longer includes a bound variable, so a named representation term $\lambda x.x$ becomes $\lambda 0$ in LN. As was mentioned in [Chapter 2](#binders), the set of terms, defined in \ref{pterms}, is a superset of $\lamy$ terms and includes terms which are not well formed $\lamy$ terms. For example, the term $\lambda 3$ is not a well-formed term, since the bound variable index is out of scope. Since we don't want to work with terms that do not correspond to $\lamy$ terms, we have to introduce the notion of a _well-formed term_, which restricts the set of pre-terms to only those that correspond to $\lamy$ terms (i.e. this inductive definition ensures that there are no "out of bounds" indices in a given pre-term):

<div class="Definition" head="Well-formed terms">
We assume that $L$ is a finite set in the following definition. $\\$
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

As a result of using LN representation of binders, the notion of substitution is split into two distinct operations. One operations is the substitution of bound variables, called _opening_. The other substitution is defined for free variables.

<div class="Definition" head="Opening and substitution">We will usually assume that $S$ is a well-formed LN term when proving properties about substitution and opening. The abbreviation $M^N \equiv \{0 \to N\}M$ is used throughout this chapter.

i)	Opening:
\begin{align*}
\{k \to S\}x &= x\\
\{k \to S\}n &= \begin{cases}
S & \text{if }k \equiv n\\
n & otherwise
\end{cases}\\
\{k \to S\}(MN) &= (\{k \to S\}M)(\{k \to S\}N)\\
\{k \to S\}(\lambda M) &= \lambda (\{k+1 \to S\}M)\\
\{k \to S\}Y_\sigma &= Y_\sigma
\end{align*}

ii)	Substitution:

\begin{align*} 
x[S/y] &= \begin{cases}
S & \text{if }x \equiv y\\
x & otherwise
\end{cases}\\
n[S/y] &= n \\
(MN)[S/y] &= (M[S/y])(N[S/y])\\
(\lambda M)[S/y] &= \lambda. (M[S/y])\\
Y_\sigma[S/y] &= Y_\sigma
\end{align*}
</div>

Having defined the _open_ operation, we turn back to the definition of well formed terms, specifically to the $(lam)$ rule, which has the precondition $\trm (M^x)$. Intuitively, for the given term $\lambda M$, the term $M^x$ is obtained by replacing all indices bound to the outermost $\lambda$ by $x$. Then, if $M^x$ is well formed, so is $\lambda M$.   
For example, taking the term $\lambda\lambda 0(z\ 1)$, we can construct the following proof-tree, showing that the term is well-typed: 

\begin{center}
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
\end{center}

We assumed that $x \not\equiv y \not\equiv z$ in the proof tree above and thus omitted the $x \not\in \fv \hdots$ branches, as they are not important for this example.<!--, i.e. it is always possible to find a fresh free variable that doesn't appear in a $\lamy$ term, as the set of atoms/free variables is countably-infinite and every $\lamy$ terms is finite.-->   
If on the other hand, we try construct a similar tree for a term which is obviously not well formed, such as $\lambda \lambda 2(z\ 1)$, we get a proof tree with a branch which cannot be closed (i.e. $\trm (2)$):

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
    \vskip 1.5em
\end{center}

####$\beta$-reduction for LN terms
Finally, we examine the formulation of $\beta$-reduction in the LN presentation of the $\lamy$ calculus. Since we only want to perform $\beta$-reduction on valid $\lamy$ terms, the inductive definition of $\beta$-reduction in the LN mechanization now includes the precondition that the terms appearing in the reduction are well formed:

<div class="Definition" head="$\beta$-reduction (LN)">$L$ is a finite set of atoms in the following definition:
$\\$
\begin{center}
    \AxiomC{$M \Rightarrow M'$}
    \AxiomC{$\trm (N)$}
    \LeftLabel{$(red_L)$}
    \BinaryInfC{$MN \Rightarrow M'N$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\trm (M)$}
    \AxiomC{$N \Rightarrow N'$}
    \LeftLabel{$(red_R)$}
    \BinaryInfC{$MN \Rightarrow M'N$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{$ x \not\in \fv(M) \cup \fv(M')$}
    \AxiomC{$M^x \Rightarrow M'^x$}
    \LeftLabel{$(abs)$}
    \BinaryInfC{$\lambda M \Rightarrow \lambda M'$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\trm (\lambda M)$}
    \AxiomC{$\trm (N)$}
    \LeftLabel{$(\beta)$}
    \BinaryInfC{$(\lambda M)N \Rightarrow M^N$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\trm (M)$}
    \LeftLabel{$(Y)$}
    \UnaryInfC{$Y_\sigma M \Rightarrow M (Y_\sigma M)$}
    \DisplayProof
    \vskip 1.5em
\end{center}
</div>

As expected, the _open_ operation is now used instead of substitution in the $(\beta)$ rule.    
The $(abs)$ rule is also slightly different, also using the _open_ in its precondition. Intuitively, the usual formulation of the $(abs)$ rule states that in order to prove that $\lambda x. M$ reduces to $\lambda x. M'$, we can simply "un-bind" $x$ in both $M$ and $M'$ and show that $M$ reduces to $M'$. Since in the usual formulation of the $\lambda$-calculus, there is no distinction between free and bound variables, this change (where $x$ becomes free) is implicit. In the LN presentation, however, this operation is made explicit by opening both $M$ and $M'$ with some free variable $x$ (not appearing in either $M$ nor $M'$), which replaces the bound variables/indices (bound to the outermost $\lambda$) with $x$.
While this definition is equivalent to Definition \ref{beta-red-nom}, the induction principle this definition yields may not always be sufficient, especially in situations where we want to open up a term with a free variable which is not only fresh in $M$ and $M'$, but possibly in a wider context (**refer to lem 2.5.1 abs case**). We therefore followed the approach of @aydemir08 and re-defined the $(abs)$ rule (and other definitions involving picking fresh free variables) using _cofinite quantification_:

\begin{center}
	\vskip 1.5em
    \AxiomC{$\forall x \not\in L.\ M^x \Rightarrow M'^x$}
    \LeftLabel{$(abs)$}
    \UnaryInfC{$\lambda M \Rightarrow \lambda M'$}
    \DisplayProof
    \vskip 1.5em
\end{center}

####Implementation details

Unlike using the nominal package, the implementation of all the definitions and functions listed for the LN representation is very straightforward. To demonstrate this, we present the definition of the $\beta$-reduction in the LN mechanization:

~~~{.isabelle}
inductive beta_Y :: "ptrm ⇒ ptrm ⇒ bool" (infix "⇒β" 300)
where
  red_L[intro]: "⟦ trm N ; M ⇒β M' ⟧ ⟹ App M N ⇒β App M' N"
| red_R[intro]: "⟦ trm M ; N ⇒β N' ⟧ ⟹ App M N ⇒β App M N'"
| abs[intro]: "⟦ finite L ; (⋀x. x ∉ L ⟹ M^(FVar x) ⇒β M'^(FVar x)) ⟧ ⟹ 
    Lam M ⇒β Lam M'"
| beta[intro]: "⟦ trm (Lam M) ; trm N ⟧ ⟹ App (Lam M) N ⇒β M^N"
| Y[intro]: "trm M ⟹ App (Y σ) M ⇒β App M (App (Y σ) M)"
~~~

##Untyped Church Rosser Theorem

Having described the implementations of the two binder representations along with some basic definitions, such as capture-avoiding substitution, we come the the main part of the comparison, namely the proof of the Church Rosser theorem. This section examines specific instances of some of the major lemmas which are part of the bigger result. The general outline of the proof has been outlined in [Chapter 2](#cr-def).

###Typed vs. untyped proofs {#typ-utyp}

As mentioned previously, when talking about the terms of the $\lamy$ calculus, we generally refer to simply typed terms, such as $\Gamma \vdash \lambda x. Y_\sigma : \tau \to (\sigma \to \sigma) \to \sigma$. However, the definitions of reduction seen so far and the consecutive proofs using these definitions don't use simply typed $\lamy$ terms, operating instead on untyped terms. The simplest reason why this is the case is one of convenience and simplicity. As is the case in most proofs of the Church Rosser Theorem, the result is usually proved for untyped terms of the $\lambda$-calculus and then extended to simply typed terms by simply restricting the terms we want to reason about. The theorem holds due to subject reduction, which says that if a term $M$ can be given a simple type $\sigma$ and $\beta$-reduces to another term $M'$, the new term can still be typed with the same type $\sigma$. Further details about the proofs of subject reduction for the simply typed $\lamy$ calculus can be found in the next section of this chapter.    
Another reason, besides convention is convenience, specifically succinctness of code, or the lack thereof, when including simple types in the definition of $\beta$-reduction and all the subsequent lemmas and theorems. Indeed, the choice of excluding typing information wherever possible has also been an engineering choice to a large degree, as it is not good practice (in general) to keep and pass around variables/objects where not needed in classical programming. The same applies to functional programming and theorem proving especially, where notation can often be bloated and cumbersome. Whilst it is true that the implementation of the proofs of Church Rosser theorem might be shorter, if the typing information was included directly in the definition of $\beta$-reduction, the downside would be an increased complexity of proofs, resulting in potentially less understandable and maintainable code.


