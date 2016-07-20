#Isabelle vs. Isabelle {#comp-isa}


This chapter looks at the two different mechanizations of the $\lamy$ calculus, introduced in the previous chapter, namely an implementation of the calculus using nominal sets and a locally nameless (LN) mechanization. Having presented the two approaches to formalizing binders in [Chapter 2](#binders), this chapters explores the consequences of choosing either mechanization, especially in terms of technology transparency and overheads introduced as a result of the chosen mechanization.

##Capture-avoiding substitution

We give a brief overview of the basic definitions of well-typed terms and $\beta$-reduction, specific to both mechanizations. Unsurprisingly, the only real differences in these definitions appear in terms involving $\lambda$-binders.

###Nominal set mechanization
We first examine the definition of untyped $\beta$-reduction, defined for the mechanization using nominal sets:

<div class="Definition" head="$\beta$-reduction">
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

This definition, with the exception of the added $(Y)$ rule is the standard definition of the untyped $\beta$-reduction found in literature (**link?**). The $\sharp$ symbol is used to denote the _freshness_ relation in nominal set theory. The side-condition $x\ \sharp\ N$ in the $(\beta)$ rule can thus be read as "$x$ is fresh in $N$", namely, the atom $x$ does not appear in $N$. For a $\lambda$-term $M$, $x\ \sharp\ M$ iff $x \not\in FV(M)$, where we take the usual definition of $FV$:

<div class="Definition" >The inductively defined $FV$ is the set of _free variables_ of a $\lambda$-term $M$.
\begin{align*} 
FV(x) &= \{ x \}\\
FV(MN) &= FV(M) \cup FV(N)\\
FV(\lambda x. M) &= FV(M) \setminus \{ x \}\\
FV(Y_\sigma) &= \emptyset
\end{align*}
</div>

The definition of substitution, used in the $(\beta)$ rule is unchanged with regards to the usual definition:

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


###Locally nameless mechanization

On paper at least, the definitions using nominal sets are unchanged from the usual informal definitions. The situation is somewhat different for the locally nameless mechanization. Since the LN approach combines the named and de Bruijn representations, there are two different constructors for free and bound variables:

<div class="Definition" head="LN pre-terms">
\label{pterms}
$$M::= x\ |\ n\ |\ MM\ |\ \lambda M\ |\ Y_\sigma \text{ where }x \in Var \text{ and } n \in Nat$$
</div>

Similarly to the de Bruijn presentation of binders, the $\lambda$-term no longer includes a bound variable, so a named representation term $\lambda x.x$ becomes $\lambda 0$ in LN. As was mentioned in [Chapter 2](#binders), the set of terms, defined in \ref{pterms}, is a superset of $\lamy$ terms and includes terms which are not well formed $\lamy$ terms. For example, the term $\lambda 3$ is not a well-formed term, since the bound variable index is out of scope. Since we don't want to work with terms that do not correspond to $\lamy$ terms, we have to introduce the notion of a _well-formed term_, which restricts the set of pre-terms to only those that correspond to $\lamy$ terms:

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
    \AxiomC{$\forall x \not\in L.\ \trm (M^x) $}
    \LeftLabel{$(lam)$}
    \UnaryInfC{$\trm (\lambda M)$}
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



<!--

**Syntax (locally nameless)**

Types: 
$$\sigma ::= a\ |\ \sigma \to \sigma \text{ where }a \in \mathcal{TV}$$

Pre-terms:
$$M::= x\ |\ n\ |\ MM\ |\ \lambda M\ |\ Y_\sigma \text{ where }x \in Var \text{ and } n \in Nat$$

**Open (locally nameless)**

$M^N \equiv \{0 \to N\}M\\$

\begin{math}
\{k \to U\}(x) = x\\
\{k \to U\}(n) = \text{if }k = n \text{ then } U \text{ else } n\\
\{k \to U\}(MN) = (\{k \to U\}M)(\{k \to U\}N)\\
\{k \to U\}(\lambda M) = \lambda (\{k+1 \to U\}M)\\
\{k \to U\}(Y \sigma) = Y \sigma
\end{math}


**Closed terms (locally nameless, cofinite)**

\begin{center}
    \AxiomC{}
    \LeftLabel{$(fvar)$}
    \UnaryInfC{term$(x)$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{}
    \LeftLabel{$(Y)$}
    \UnaryInfC{term$(Y_\sigma)$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{$\forall x \not\in L.\ \text{term}(M^x) $}
    \LeftLabel{$(lam)$}
    \RightLabel{(finite $L$)}
    \UnaryInfC{term$(\lambda M)$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{term$(M)$}
    \AxiomC{term$(M)$}
    \LeftLabel{$(app)$}
    \BinaryInfC{term$(MN)$}
    \DisplayProof
\end{center}


**$\beta Y$-Reduction(locally nameless, cofinite, untyped)**

\begin{center}
    \AxiomC{$M \Rightarrow M'$}
    \AxiomC{term$(N)$}
    \LeftLabel{$(red_L)$}
    \BinaryInfC{$MN \Rightarrow M'N$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{term$(M)$}
    \AxiomC{$N \Rightarrow N'$}
    \LeftLabel{$(red_R)$}
    \BinaryInfC{$MN \Rightarrow M'N$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{$\forall x \not\in L.\ M^x \Rightarrow M'^x$}
    \LeftLabel{$(abs)$}
    \RightLabel{(finite $L$)}
    \UnaryInfC{$\lambda M \Rightarrow \lambda M'$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{term$(\lambda M)$}
    \AxiomC{term$(N)$}
    \LeftLabel{$(\beta)$}
    \BinaryInfC{$(\lambda M)N \Rightarrow M^N$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{}
    \LeftLabel{$(Y)$}
    \UnaryInfC{$M \Rightarrow M (Y_\sigma M)$}
    \DisplayProof
\end{center} 




##$\lamy$ calculus - Definitions

**Syntax (nominal)**

**Well typed terms (nominal)**



**$\beta Y$-Reduction(nominal, typed)**

\begin{center}
    \AxiomC{$\Gamma \vdash M \Rightarrow M' : \sigma \to \tau$}
    \AxiomC{$\Gamma \vdash N : \sigma$}
    \LeftLabel{$(red_L)$}
    \BinaryInfC{$\Gamma \vdash MN \Rightarrow M'N : \tau$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\Gamma \vdash M : \sigma \to \tau$}
    \AxiomC{$\Gamma \vdash N \Rightarrow N' : \sigma$}
    \LeftLabel{$(red_R)$}
    \BinaryInfC{$\Gamma \vdash MN \Rightarrow M'N : \tau$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{$\Gamma \cup \{x:\sigma\} \vdash M \Rightarrow M' : \tau$}
    \LeftLabel{$(abs)$}
    \RightLabel{$(x\ \sharp\ \Gamma)$}
    \UnaryInfC{$\Gamma \vdash \lambda x. M \Rightarrow \lambda x. M' : \sigma \to \tau$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\Gamma \cup \{x:\sigma\} \vdash M : \tau$}
    \AxiomC{$\Gamma \vdash N : \sigma$}
    \LeftLabel{$(\beta)$}
    \RightLabel{$(x\ \sharp\ \Gamma, N)$}
    \BinaryInfC{$\Gamma \vdash (\lambda x. M)N \Rightarrow M[N/x] : \tau$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{$\Gamma \vdash M : \sigma \to \sigma$}
    \LeftLabel{$(Y)$}
    \UnaryInfC{$\Gamma \vdash Y_\sigma M \Rightarrow M (Y_\sigma M) : \sigma$}
    \DisplayProof
\end{center}



**$\beta Y$-Reduction(nominal, untyped)**

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
\end{center}


-------------------

-->
