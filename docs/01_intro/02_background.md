#Background

##Binders {#binders}

When describing the (untyped) $\lambda$-calculus on paper, the terms of the $\lambda$-calculus are usually inductively defined in the following way:

$$t::= x\ |\ tt\ |\ \lambda x.t \text{ where }x \in Var$$

This definition of terms yields an induction/recursion principle, which can be used to define functions over the $\lambda$-terms by structural recursion and prove properties about the $\lambda$-terms using structural induction (recursion and induction being two sides of the same coin).   
However, whilst the definition above describes valid terms of the $\lambda$-calculus, there are implicit assumptions one makes about the terms, namely, the $x$ in the $\lambda x.t$ case appears bound in $t$. This means that while $x$ and $y$ might be distinct terms of the $\lambda$-calculus (i.e. $x \neq y$), $\lambda x.x$ and $\lambda y.y$ represent the same term, as $x$ and $y$ are bound by the $\lambda$. Without the notion of $\alpha$-equivalence of terms, one cannot prove any properties of terms involving bound variables, such as saying that $\lambda x.x \equiv \lambda y.y$.

In an informal setting, reasoning with $\alpha$-equivalence of terms is often very implicit, however in a formal setting of theorem provers, having an inductive definition of "raw" $lambda$-terms, which are not $alpha$-equivalent, yet reasoning about $\alpha$-equivalent $\lambda$-terms poses certain challenges.   
One of the main problems is the fact that the inductive/recursive definition does not easily lift to $alpha$-equivalent terms. Take a trivial example of a function on raw terms, which checks whether a variable appears bound in a given $\lambda$-term. Clearly, such function is well formed for "raw" terms, but does not work (or even make sense) for $\alpha$-equivalent terms.   
Conversely, there are informal definitions over $\alpha$-equivalent terms, which are not straight-forward to define over raw terms. Take the usual definition of substitution, defined over $\alpha$-equivalent terms, which actually relies on this fact in the following case:

$$(\lambda y'. s')[t/x] \equiv \lambda y'.(s'[t/x]) \text{ assuming } y' \not\equiv x\text{ and }y' \not\in FV(t)$$

Here in the $\lambda$ case, it is assumed that a given $\lambda$-term $\lambda y. s$ can always be swapped out for an alpha equivalent term $\lambda y'. s'$, such that $y'$ satisfies the side condition. The assumption that a bound variable can be swapped out for a "fresh" one to avoid name clashes is often referred to as the Barendregt Variable Convention.

The direct approach of defining "raw" terms and an additional notion of $\alpha$-equivalence introduces a lot of overhead when defining functions, as one either has to use the recursive principles for "raw" terms and then show that the function lifts to the $\alpha$-equivalent terms or define functions on $alpha$-equivalence classes and prove that it is well-founded, without being able to rely on the structurally inductive principles that one gets "for free" with the "raw" terms.    
Because of this, the usual informal representation of the $\lambda$-calculus is rarely used in a fully formal setting. 

To mitigate the overheads of a fully formal definition of the $\lambda$-calculus, we want to have an encoding of the $\lambda$-terms, which includes the notion of $\alpha$-equivalence whilst being inductively defined, giving us the inductive/recursive principles for $alpha$-equivalent terms directly. This can be achieved in several different ways. In general, there are two main approaches taken in a rigorous formalization of the terms of the lambda calculus, namely the concrete approaches and the higher-order approaches, both described in some detail below.


###Concrete approaches

The concrete or first-order approaches usually encode variables using names (like strings or natural numbers). Encoding of terms and capture-avoiding substitution must be encoded explicitly. A survey by @aydemir08 details three main groups of concrete approaches, found in formalizations of the $\lambda$-calculus in the literature:

####Named

This approach generally defines terms in much the same way as the informal inductive definition given above. Using a functional language, such as Haskell or ML, such a definition might look like this:

~~~{.isabelle}
datatype trm =
  Var name
| App trm trm
| Lam name trm
~~~ 

As was mentioned before, defining "raw" terms and the notion of $\alpha$-equivalence of "raw" terms separately carries a lot of overhead in a theorem prover and is therefore not favored. 

To obtain an inductive definition of $\lambda$-terms with a built in notion of $\alpha$-equivalence, one can instead use nominal sets (**described in the section on nominal sets/Isabelle?**).
The nominal package in Isabelle provides tools to automatically define terms with binders, which generate inductive definitions of $\alpha$-equivalent terms. Using nominal sets in Isabelle results in a definition of terms which looks very similar to the informal presentation of the lambda calculus:

~~~{.isabelle}
nominal_datatype trm =
  Var name
| App trm trm
| Lam x::name l::trm  binds x in l
~~~

Most importantly, this definition allows one to define functions over $\alpha$-equivalent terms using structural induction. The nominal package also provides freshness lemmas and a strengthened induction principle with name freshness for terms involving binders.

####Nameless/de Bruijn

Using a named representation of the lambda calculus in a fully formal setting can be inconvenient when dealing with bound variables. For example, substitution, as described in the introduction, with its side-condition of freshness of $y$ in $x$ and $t$ is not structurally recursive on "raw" terms, but rather requires well-founded recursion over $\alpha$-equivalence classes of terms. To avoid this problem in the definition of substitution, the terms of the lambda calculus can be encoded using de Bruijn indices:

~~~{.isabelle}
datatype trm =
  Var nat
| App trm trm
| Lam trm
~~~

This representation of terms uses indices instead of named variables. The indices are natural numbers, which encode an occurrence of a variable in a $\lambda$-term. For bound variables, the index indicates which $\lambda$ it refers to, by encoding the number of $\lambda$-binders that are in the scope between the index and the $\lambda$-binder the variable corresponds to. For example, the term $\lambda x.\lambda y. yx$ will be represented as $\lambda\ \lambda\ 0\ 1$. Here, 0 stands for $y$, as there are no binders in scope between itself and the $\lambda$ it corresponds to, and $1$ corresponds to $x$, as there is one $\lambda$-binder in scope. To encode free variables, one simply choses an index greater than the number of $\lambda$'s currently in scope, for example, $\lambda\ 4$.   

To see that this representation of $\lambda$-terms is isomorphic to the usual named definition, we can define two function $f$ and $g$, which translate the named representation to de Bruijn notation and vice versa. More precisely, since we are dealing with $\alpha$-equivalence classes, its is an isomorphism between these that we can formalize. 

To make things easier, we consider a representation of named terms, where we map named variables, $x, y, z,...$ to indexed variables $x_1,x_2,x_3,...$. Then, the mapping from named terms to de Bruijn term is given by $f$, which we define in terms of an auxiliary function $e$:

\begin{align*} 
e_k^m(x_n) &= \begin{cases}
k-m(x_n)-1 & x_n \in \text{dom }m\\
k+n & otherwise
\end{cases}\\
e_k^m(uv) &= e_k^m(u)\ e_k^m(v)\\
e_k^m(\lambda x_n.u) &= \lambda\ e_{k+1}^{m \oplus (x_n,k)}(u)
\end{align*}

Then $f(t) \equiv e_0^\emptyset(t)$

The function $e$ takes two additional parameters, $k$ and $m$. $k$ keeps track of the scope from the root of the term and $m$ is a map from bound variables to the levels they were bound at. In the variable case, if $x_n$ appears in $m$, it is a bound variable, and it's index can be calculated by taking the difference between the current index and the index $m(x_k)$, at which the variable was bound. If $x_n$ is not in $m$, then the variable is encoded by adding the current level $k$ to $n$.   
In the abstraction case, $x_n$ is added to $m$ with the current level $k$, possibly overshadowing a previous binding of the same variable at a different level (like in $\lambda x_1. (\lambda x_1. x_1)$) and $k$ is incremented, going into the body of the abstraction. <!--For all closed terms, the choice of $k$ is arbitrary.-->


The function $g$, taking de Bruijn terms to named terms is a little more tricky. We need to replace indices encoding free variables (those that have a value greater than or equal to $k$, where $k$ is the number of binders in scope) with named variables, such that for every index $n$, we substitute $x_m$, where $m = n-k$, without capturing these free variables.

We need two auxiliary functions to define $g$:

\begin{align*} 
h_k^b(n) &= \begin{cases}
x_{n-k} & n \geq k\\
x_{k+b-n-1} & otherwise
\end{cases}\\
h_k^b(uv) &= h_k^b(u)\ h_k^b(v)\\
h_k^b(\lambda u) &= \lambda x_{k+b}.\ h_{k+1}^b(u)
\end{align*}


\begin{align*} 
\Diamond_k(n) &= \begin{cases}
n-k & n \geq k\\
0 & otherwise
\end{cases}\\
\Diamond_k(uv) &= \max (\Diamond_k(u),\ \Diamond_k(v))\\
\Diamond_k(\lambda u) &= \Diamond_{k+1}(u)
\end{align*}

The function $g$ is then defined as $g(t) \equiv h_0^{\Diamond_0(t)+1}(t)$. As mentioned above, the complicated definition has to do with avoiding free variable capture. A term like $\lambda (\lambda\ 2)$ intuitively represents a named $\lambda$-term with two bound variables and a free variable $x_0$ according to the definition above. If we started giving the bound variables names in a naive way, starting from $x_0$, we would end up with a term $\lambda x_0.(\lambda x_1.x_0)$, which is obviously not the term we had in mind, as $x_0$ is no longer a free variable. To ensure we start naming the bound variables in such a way as to avoid this situation, we use $\Diamond$ to compute the maximal value of any free variable in the given term, and then start naming bound variables with an index one higher than the value returned by $\Diamond$.


<!--Note that while $f_k^\emptyset \circ g_k = id$ is true, since the de Bruijn terms are invariant under $\alpha$-equivalence, $g_k \circ f_k^\emptyset = id$ is not, since taking the aforementioned term $\lambda x_1. (\lambda x_1. x_1)$, we have $(g_1 \circ f_1^\emptyset)( \lambda x_1. (\lambda x_1. x_1) ) = \lambda x_1. (\lambda x_2. x_2)$.
However, its easy to see that $\lambda x_1. (\lambda x_1. x_1) \equiv_\alpha \lambda x_1. (\lambda x_2. x_2)$, thus we can say that $\forall t.\ (g_k \circ f_k^\emptyset)(t) \equiv_\alpha t$.
$\\$-->

As one quickly notices, a term like $\lambda x.x$ and $\lambda y.y$ have a single unique representation as a de Bruijn term $\lambda\ 0$. Indeed, since there are no named variables in a de Bruijn term, there is only one way to represent any $\lambda$-term, and the notion of $\alpha$-equivalence is no longer relevant. We thus get around our problem of having an inductive principle and $\alpha$-equivalent terms, by having a representation of $\lambda$-terms where every $\alpha$-equivalence class of $\lambda$-terms has a single representative term in the de Bruijn notation.

In their comparison between named vs. nameless/de Bruijn representations of $\lambda$-terms, @berghofer06 give details about the definition of substitution, which no longer needs the variable convention and can therefore be defined using primitive structural recursion.   
The main disadvantage of using de Bruijn indices is the relative unreadability of both the terms and the formulation of properties about these terms. For example, the substitution lemma, which in the named setting would be stated as:

$$\text{If }x \neq y\text{ and }x \not\in FV(L)\text{, then }
M[N/x][L/y] \equiv M[L/y][N[L/y]/x].$$

becomes the following statement in the nameless formalization:

$$\text{For all indices }i, j\text{ with }i \leq j\text{, }M[N/i][L/j] = M[L/j + 1][N[L/j - i]/i]$$

Clearly, the first version of this lemma is much more intuitive.

####Locally Nameless

The locally nameless approach to binders is a mix of the two previous approaches. Whilst a named representation uses variables for both free and bound variables and the nameless encoding uses de Bruijn indices in both cases as well, a locally nameless encoding distinguishes between the two types of variables.   
Free variables are represented by names, much like in the named version, and bound variables are encoded using de Bruijn indices. By using de Bruijn indices for bound variables, we again obtain an inductive definition of terms which are already $alpha$-equivalent.

While closed terms, like $\lambda x.x$ and $\lambda y.y$ are represented as de Bruijn terms, the term $\lambda x.xz$ and $\lambda x.xz$ are encoded as $\lambda\ 0z$. The following definition captures the syntax of the locally nameless terms:

~~~{.isabelle}
datatype ptrm =
  Fvar name
  BVar nat
| App trm trm
| Lam trm
~~~

Note however, that this definition doesn't quite fit the notion of $\lambda$-terms, since a `pterm` like `(BVar 1)` does not represent a $\lambda$-term, since bound variables can only appear in the context of a lambda, such as in `(Lam (BVar 1))`.   
The advantage of using a locally nameless definition of $\lambda$-terms is a better readability of such terms, compared to equivalent de Bruijn terms. Another advantage is the fact that definitions of functions and reasoning about properties of these terms is much closer to the informal setting.

###Higher-Order approaches

Unlike concrete approaches to formalizing the lambda calculus, where the notion of binding and substitution is defined explicitly in the host language, higher-order formalizations use the function space of the implementation language, which handles binding. HOAS, or higher-order abstract syntax [@pfenning88, @harper93], is a framework for defining logics based on the simply typed lambda calculus. A form of HOAS, introduced by @harper93, called the Logical Framework (LF) has been implemented as Twelf by @pfenning99, which has been previously used to encode the $\lambda$-calculus.   
Using HOAS for encoding the $\lambda$-calculus comes down to encoding binders using the meta-language binders. This way, the definitions of capture avoiding substitution or notion of $\alpha$-equivalence are offloaded onto the meta-language. As an example, take the following definition of terms of the $\lambda$-calculus in Haskell:

~~~{.haskell}
data Term where
  Var :: Int -> Term
  App :: Term -> Term -> Term
  Lam :: (Term -> Term) -> Term
~~~

This definition avoids the need for explicitly defining substitution, because it encodes a $\lambda$-term as a Haskell function `(Term -> Term)`, relying on Haskell's internal substitution and notion of $\alpha$-equivalence. As with the de Bruijn and locally nameless representations, this encoding gives us inductively defined terms with a built in notion of $\alpha$-equivalence.      
However, using HOAS only works if the notion of $\alpha$-equivalence and substitution of the meta-language coincide with these notions in the object-language.

\newpage
##$\lamy$ calculus

**?Tie in $\lamy$ calculus to HOMC?**

###Definitions

The first part of this project focuses on formalizing the simply typed $\lamy$ calculus and the proof of confluence for this calculus. The usual/informal definition of the $\lamy$ terms and the simple types are given below:

<div class="Definition" head="$\lamy$ types and terms">Let $Var$ be a countably infinite set of atoms in the definition of the set of $\lambda$-terms $M$:
\label{lamy-trms}
\begin{align*}
\sigma ::=&\ \mathsf{o}\ |\ \sigma \to \sigma \\
M ::=&\ x\ |\ MM\ |\ \lambda x.M\ |\ Y_\sigma \text{ where }x \in Var \\
\end{align*}
</div> 

The $\lamy$ calculus differs from the simply typed $\lambda$-calculus only in the addition of the $Y$ constant family, indexed at every simple type $\sigma$, where the (simple) type of a $Y_A$ constant (indexed with the type $A$) is $(A \to A) \to A$. The usual definition of $\beta$-reduction is then augmented with the $(Y)$ rule (this is the typed version of the rule):

\begin{center}
    \AxiomC{$\Gamma \vdash M : \sigma \to \sigma$}
    \LeftLabel{$(Y)$}
    \UnaryInfC{$\Gamma \vdash Y_\sigma M \Rightarrow M (Y_\sigma M) : \sigma$}
    \DisplayProof
\end{center}

In essence, the $Y$ rule allows (some) well-typed recursive definitions over simply typed $\lambda$-terms. The typed version of the rule illustrates this restricted version of recursion, where a recursive "$Y$-reduction" will only occur if the term $M$ in $Y_\sigma M$ has the matching type $\sigma \to \sigma$ (to $Y_\sigma$'s type $(\sigma \to \sigma) \to \sigma$).

###Church-Rosser Theorem {#cr-def}

The Church-Rosser Theorem states that the $\beta$-reduction of the $\lambda$-calculus is confluent, that is, the reflexive-transitive closure of the $\beta$-reduction has the _diamond property_, i.e. $\dip(\Rightarrow^*)$, where:

<div class="Definition" head="$\dip(R)$">
A relation $R$ has the _diamond property_, i.e. $\dip(R)$, iff
$$\forall a, b, c.\ aRb \land aRc \implies \exists d.\ bRd \land cRd$$
</div>

The proof of confluence of $\Rightarrow_Y$, the $\beta Y$-reduction defined as the standard $\beta$-reduction with the addition of the aforementioned $(Y)$ rule, formalized in this project, follows a variation of the Tait-Martin-Löf Proof originally described in @takahashi95 (specifically using the notes by @pollack95). 

This proof proceeds by first defining a relation called the parallel beta reduction $\gg$, which is a reflexive and parallel $\beta Y$-reduction, in that it allows simultaneous reduction of multiple parts of a term:

<div class="Definition" head="$\gg$">
$\ $
\begin{center}
    \AxiomC{}
    \LeftLabel{$(refl)$}
    \UnaryInfC{$x \gg x$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$M \gg M'$}
    \AxiomC{$N \gg N'$}
    \LeftLabel{$(app)$}
    \BinaryInfC{$MN \gg M'N'$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{$M \gg M'$}
    \LeftLabel{$(abs)$}
    \UnaryInfC{$\lambda x. M \gg \lambda x. M'$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$M \gg M'$}
    \AxiomC{$N \gg N'$}    \LeftLabel{$(\beta)$}
    \BinaryInfC{$(\lambda x. M)N \gg M'[N'/x]$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$M \gg M'$}
    \LeftLabel{$(Y)$}
    \UnaryInfC{$Y_\sigma M \gg M' (Y_\sigma M')$}
    \DisplayProof
\end{center}
</div>

Since the transitive closure of $\gg$ is the same as the transitive closure of $\Rightarrow_Y$, i.e. $\gg^*\ =\ \Rightarrow_Y^*$, it is enough to show $\dip(\gg^*)$. The proof therefore proceeds in roughly three main steps:

1.  Prove $\dip(\gg)$
2.  Show $\dip(\gg) \implies \dip(\gg^*)$
3.  Show $\gg^*\ =\ \Rightarrow_Y^*$

The most interesting step is to show $\dip(\gg)$, as 2. and 3. follow fairly straightforwardly. To prove $\dip(\gg)$, the formalizations in this project follow the aforementioned proof by @takahashi95. The main idea in this proof is to define another relation called the maximum parallel reduction $\ggg$, which contracts all redexes in a given term with a single step:


<div class="Definition" head="$\ggg$">
$\ $
\begin{center}
    \AxiomC{}
    \LeftLabel{$(refl)$}
    \UnaryInfC{$x \ggg x$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$M \ggg M'$}
    \AxiomC{$N \ggg N'$}
    \LeftLabel{$(app)$}
    \RightLabel{($M$ is not a $\lambda$ or $Y$)}
    \BinaryInfC{$MN \ggg M'N'$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{$M \ggg M'$}
    \LeftLabel{$(abs)$}
    \UnaryInfC{$\lambda x. M \ggg \lambda x. M'$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$M \ggg M'$}
    \AxiomC{$N \ggg N'$}    \LeftLabel{$(\beta)$}
    \BinaryInfC{$(\lambda x. M)N \ggg M'[N'/x]$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$M \ggg M'$}
    \LeftLabel{$(Y)$}
    \UnaryInfC{$Y_\sigma M \ggg M' (Y_\sigma M')$}
    \DisplayProof
\end{center}
</div>

This relation differs from $\gg$ only in the $(app)$ rule, which can only be applied if $M$ is not a $\lambda$ or $Y$ term.

To prove $\dip(\gg)$, we first show that there always exists a term $M_{max}$ for every term $M$, where $M \ggg M_{max}$ is the maximal parallel reduction which contracts all redexes in $M$:

<div class="Lemma" head="$\exists\ggg$">
\label{max-ex}
$\forall M.\ \exists M_{max}.\ M \ggg M_{max}$
</div>
<div class="proof">
By induction on M.
</div>

Finally, we show that any parallel reduction $M \gg M'$ can be "closed" by reducing to the term $M_{max}$ where all redexes have been contracted:

\begin{center}
\begin{tikzpicture}[->,>=stealth',shorten >=1pt,auto,node distance=2.8cm,semithick]
  \tikzstyle{every state}=[fill=none,draw=none,text=black]

  \node[state] (A)                                    {$M$};
  \node[state] (B) [below left= 1.3cm and 1.3cm of A] {$M'$};
  \node[state] (D) [below= 3cm of A]                  {$M_{max}$};
 
  \path (A) edge [left]         node [pos=0.4] {$\gg$}  (B)
            edge                node           {$\ggg$} (D)
        (B) edge [left, dashed] node           {$\gg$}  (D);
\end{tikzpicture}
\end{center}

This triangle can be formulated as the following lemma:

<div class="Lemma">
\label{max-close}
$\forall M, M', M_{max}.\ M \ggg M_{max} \land M \gg M' \implies M' \gg M_{max}$
</div>
<div class="proof">
Omitted. Can be found on p. 8 of the @pollack95 notes.
</div>

<div class="Lemma">$\dip(\gg)$.</div>
<div class="proof">
We can now prove $\dip(\gg)$ by simply applying Lemma \ref{max-close} twice, namely for any term $M$ there is an $M_{max}$ s.t. $M \ggg M_{max}$ (by \ref{max-ex}) and for any $M', M''$ where $M \gg M'$ and $M \gg M''$, it follows by two applications of Lemma \ref{max-close} that $M' \gg M_{max}$ and $M'' \gg M_{max}$.
</div>

###Simple types

The simple types presented throughout this work (except for [Chapter 6](#itypes)) are often referred to as simple types _a la Curry_, where a simply typed $\lambda$-term is a triple $(\Gamma, M, \sigma)$ s.t. $\Gamma \vdash M : \sigma$, where $\Gamma$ is the typing context, $M$ is a term of the untyped $\lambda$-calculus and $\sigma$ is a simple type.    
In the untyped $\lambda$ calculus, simple types and $\lambda$-terms are completely separate, brought together only through the typing relation $\vdash$ in the case of simple types _a la Curry_. The definition of $\lamy$ terms, however, is dependent on the simple types in the case of the $Y$ constants, which are indexed by simple types. When talking about the $\lamy$ calculus, we tend to conflate the "untyped" $\lamy$ terms, which are simply the terms defined  in \ref{lamy-trms}, with the "typed" $\lamy$ terms, which are simply typed terms _a la Curry_ of the form $\Gamma \vdash M : \sigma$, where $M$ is an "untyped" $\lamy$ term. Thus, results about the $\lamy$ calculus in this work are in fact results about the "typed" $\lamy$ calculus.    
However, the proofs of the Church Rosser theorem, as presented in the previous section, use the untyped definition of $\beta$-reduction. Whilst it is possible to define a typed version of $\beta$-reduction, as was demonstrated by the typed version of the $(Y)$ reduction rule, it turned out to be much easier to first prove the Church Rosser theorem for the so called "untyped" $\lamy$ calculus and the additionally restrict this result to only well-types $\lamy$ terms. Thus, the definition of the Church Rosser Theorem, formulated for the $\lamy$ calculus, is the following one:

<div class="Theorem" head="Church Rosser">
$$\Gamma \vdash M : \sigma \land M \Rightarrow^* M' \land M \Rightarrow^* M'' \implies \exists M'''.\ \ M' \Rightarrow^* M''' \land M'' \Rightarrow^* M''' \land \Gamma \vdash M''' : \sigma$$
</div>

In order to prove this typed version of the Church Rosser Theorem, we need to prove an additional result of subject reduction for $\lamy$ calculus, namely:

<div class="Theorem" head="Subject reduction for $\Rightarrow_\beta$">
$$\Gamma \vdash M : \sigma \land M \Rightarrow^* M' \implies \Gamma \vdash M' : \sigma$$
</div>

\newpage
##Intersection types

For the formalization of intersection types, we initially chose a strict intersection-type system, presented in the @bakel notes. Intersection types, as classically presented in @barendregt13 as $\lambda_\cap^{BCD}$, extend simple types by adding a conjunction to the definition of types:

<div class="Definition" head="$\lambda_\cap^{BCD}$ types">
$$\mathcal{T} ::= \phi\ |\ \mathcal{T} \leadsto \mathcal{T}\ |\ \mathcal{T} \cap \mathcal{T}$$
</div>

We restrict ourselves to a version of intersection types often called _strict intersection types_. _Strict intersection types_ are a restriction on $\lambda_\cap^{BCD}$ types, where an intersection of types can only appear on the left side of an "arrow" type:

<div class="Definition" head="Strict intersection types">
\begin{align*} 
\mathcal{T}_s &::= \phi\ |\ \mathcal{T} \leadsto \mathcal{T}_s \\ 
\mathcal{T} &::= (\mathcal{T}_s \cap\hdots\cap \mathcal{T}_s)
\end{align*}
</div>

The following conventions for intersection types are adopted throughout this section; 
$\omega$ stands for the empty intersection and we write $\bigcap\tau_i$ for the type $\tau_1 \cap\hdots\cap \tau_i$. We also define a relation $\subseteq$ for intersection types:

<div class="Definition" head="$\subseteq$">This relation is the least pre-order on intersection types s.t.:
\begin{align*} 
\forall\ 1 \leq j \leq i.&\ \ \tau_j \subseteq \bigcap \tau_i \\ 
\forall\ 1 \leq j \leq i.\ \ \tau_j \subseteq \tau &\implies \bigcap \tau_i \subseteq \tau \\
\rho \subseteq \psi \land \tau \subseteq \mu &\implies \psi \leadsto \tau \subseteq \rho \leadsto \mu\\
\end{align*}
</div>


Note that $\lamy$ terms are typed with the strict types $\mathcal{T}_s$ only. The typing system, presented for the strict intersection types, is an adaptation of the one found in the @pollack95 notes, with the addition of the typing rule for the $Y$ constants.

<div class="Definition" head="Intersection-type assignment">$\\$
\begin{center}
  \AxiomC{$\exists (x, \bigcap\tau_i) \in \Gamma.\ \tau \subseteq \bigcap\tau_i$}
  \LeftLabel{$(var)$}
  \UnaryInfC{$\Gamma \Vdash x : \tau$}
  \DisplayProof
  %------------------------------------
  \hskip 1.5em
  \AxiomC{$\Gamma \Vdash M : \bigcap\tau_i \leadsto \tau$}
  \AxiomC{$\forall\ 1 \leq j \leq i.\ \ \Gamma \Vdash N : \tau_j$}
  \LeftLabel{$(app)$}
  \BinaryInfC{$\Gamma \Vdash MN : \tau$}
  \DisplayProof
  %------------------------------------
  \vskip 1.5em
  \AxiomC{$(x, \bigcap\tau_i),\Gamma \Vdash M : \tau$}
  \LeftLabel{$(abs)$}
  \UnaryInfC{$\Gamma \Vdash \lambda x.M : \bigcap\tau_i \leadsto \tau$}
  \DisplayProof
  %------------------------------------
  \vskip 1.5em
  \AxiomC{}
  \LeftLabel{$(Y)$}
  \RightLabel{$(1 \leq j \leq i)$}
  \UnaryInfC{$\Gamma \Vdash Y_\sigma : (\bigcap\tau_i \leadsto \tau_1 \cap\hdots\cap \bigcap\tau_i \leadsto \tau_i) \leadsto \tau_j$}
  \DisplayProof
  \vskip 1.5em
\end{center}
</div>

This is the initial definition, used as a basis for the mechanization, discussed in [Chapter 6](#itypes). Due to different obstacles in the formalization of the subject invariance proofs, this definition, along with the definition of intersection types was amended several times. The reasons for these changes are documented in [Chapter 6](#itypes).   
The definition above also assumes that the context $\Gamma$ is _well-formed_:

<div class="Definition" head="Well-formed intersection-type context">
Assuming that $\Gamma$ is a finite list, consisting of pairs of atoms $Var$ and intersection types $\mathcal{T}$, $\Gamma$ is a _well-formed_ context iff:$\\$
\begin{center}
  \AxiomC{}
  \LeftLabel{$(nil)$}
  \UnaryInfC{$\wf [\ ]$}
  \DisplayProof
  %------------------------------------
  \hskip 1.5em
  \AxiomC{$x \not\in \mathsf{dom}\ \Gamma$}
  \AxiomC{$\wf \Gamma$}
  \LeftLabel{$(cons)$}
  \BinaryInfC{$\wf (x,\bigcap\tau_i),\Gamma$}
  \DisplayProof
  \vskip 1.5em
\end{center}
</div>
