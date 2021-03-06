#Background
\label{chap:background}

This chapter introduces some of the main concepts, discussed in greater length throughout the thesis. The first section provides an overview of the different approaches to mechanizing binders in a $\lambda$-calculus, since the treatment of binders is the most involved/problematic part of a fully formal mechanization of a $\lambda$-calculus.    
The next section then introduces the simply-typed $\lamy$ calculus along with a broad overview of the proof of confluence and important associated lemmas, which are discussed further in the following chapters.    
Lastly, we introduce the theory underpinning HOMC, namely the intersection type system for the $\lamy$ calculus along with the proofs of subject invariance for intersection types.

##Binders
\label{binders}

When describing the (untyped) $\lambda$-calculus on paper, the terms of the $\lambda$-calculus are usually inductively defined in the following way:

\begin{center}
$t::= x\ |\ tt\ |\ \lambda x.t \text{ where }x \in Var$
\end{center}

This definition of terms yields an induction/recursion principle, which can be used to define functions over the $\lambda$-terms by structural recursion and prove properties about the $\lambda$-terms using structural induction (recursion and induction being two sides of the same coin).   
However, whilst the definition above describes valid terms of the $\lambda$-calculus, there are implicit assumptions one makes about the terms, namely, the $x$ in the $\lambda x.t$ case appears bound in $t$. This means that while $x$ and $y$ might be distinct terms of the $\lambda$-calculus (i.e. $x \neq y$), $\lambda x.x$ and $\lambda y.y$ represent the same term, as $x$ and $y$ are bound by the $\lambda$. Without the notion of $\alpha$-equivalence of terms, one cannot prove any properties of terms involving bound variables, such as saying that $\lambda x.x \equiv \lambda y.y$.

In an informal setting, reasoning with $\alpha$-equivalence of terms is often very implicit, however in a formal setting of theorem provers, having an inductive definition of "raw" $\lambda$-terms, which are not $\alpha$-equivalent, yet reasoning about $\alpha$-equivalent $\lambda$-terms poses certain challenges.   
One of the main problems is the fact that the inductive/recursive definition does not easily lift to $\alpha$-equivalent terms and using induction as a proof technique for such a definition is no longer valid. Take a trivial example of a function on raw terms, which checks whether a variable appears bound in a given $\lambda$-term. Clearly, such function is well formed for "raw" terms, but does not work (or even make sense) for $\alpha$-equivalent terms.   
Conversely, there are informal definitions over $\alpha$-equivalent terms, which are not straight-forward to define over raw terms. Take the usual definition of substitution, defined over $\alpha$-equivalent terms, which actually relies on the following fact in the $\lambda$-case:

\begin{center}
$(\lambda y'. s')[t/x] \equiv \lambda y'.(s'[t/x]) \text{ assuming } y' \not\equiv x\text{ and }y' \not\in FV(t)$
\end{center}


In this, the $\lambda$ case, it is assumed, that a given $\lambda$-term $\lambda y. s$ can always be swapped out for an alpha equivalent term $\lambda y'. s'$, such that $y'$ satisfies the side condition. The assumption that a bound variable can be swapped out for a "fresh" one to avoid name clashes is often referred to as the Barendregt Variable Convention.

The direct approach of defining "raw" terms and an additional notion of $\alpha$-equivalence introduces a lot of overhead when defining functions, as one either has to use the recursive principles for "raw" terms and then show that the function lifts to the $\alpha$-equivalent terms or define functions on $alpha$-equivalence classes and prove that it is well-founded, without being able to rely on the structurally inductive principles that one gets "for free" with the "raw" terms.    
Because of this, the usual informal representation of the $\lambda$-calculus is rarely used in a fully formal setting. 

To mitigate the overheads of a fully formal definition of the $\lambda$-calculus, we want to have an encoding of $\lambda$-terms, which includes the notion of $\alpha$-equivalence, whilst being inductively defined, giving us the inductive/recursive principles for $alpha$-equivalent terms directly. This can be achieved in several different ways. In general, there are two main approaches taken in a rigorous formalization of the terms of the lambda calculus, namely the concrete approaches and the higher-order approaches, both described in some detail below.


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

To obtain an inductive definition of $\lambda$-terms with a built in notion of $\alpha$-equivalence, one can instead use nominal sets. The theory of nominal sets captures the notion of bound variables and freshness, as it is based around the notion of having properties invariant in name permutation (@gabbay02).    
The nominal package in Isabelle (@urban05) provides tools to automatically define terms with binders, which generate inductive definitions of $\alpha$-equivalent terms. Using nominal sets in Isabelle results in a definition of terms, which looks very similar to the informal presentation of the lambda calculus:

~~~{.isabelle}
nominal_datatype trm =
  Var name
| App trm trm
| Lam x::name l::trm  binds x in l
~~~

Most importantly, this definition allows one to define functions over $\alpha$-equivalent terms using structural induction. The nominal package also provides freshness lemmas and a strengthened induction principle with name freshness for terms involving binders.

####Nameless/de Bruijn

Using a named representation of the $\lambda$-calculus in a fully formal setting can be inconvenient when dealing with bound variables. For example, substitution, as described in the introduction, with its side-condition of freshness of $y$ in $x$ and $t$ is not structurally recursive on "raw" terms, but rather requires well-founded recursion over $\alpha$-equivalence classes of terms. To avoid this problem in the definition of substitution, the terms of the lambda calculus can be encoded using de Bruijn indices, instead of named variables:

~~~{.isabelle}
datatype trm =
  I nat
| App trm trm
| Lam trm
~~~

The indices are natural numbers, which encode an occurrence of a variable in a $\lambda$-term. For bound variables, the index indicates which $\lambda$ it refers to, by encoding the number of $\lambda$-binders that are in the scope between the index and the $\lambda$-binder the variable corresponds to. 

<div class="Example">
The term $\lambda x.\lambda y. yx$ will be represented as $\lambda\ \lambda\ 0\ 1$. Here, 0 stands for $y$, as there are no binders in scope between itself and the $\lambda$ it corresponds to, and $1$ corresponds to $x$, as there is one $\lambda$-binder in scope. To encode free variables, one simply choses an index greater than the number of $\lambda$'s currently in scope, for example, $\lambda\ 4$.
</div>

To see that this representation of $\lambda$-terms is isomorphic to the usual named definition, we can define two functions $f$ and $g$, which translate the named representation to de Bruijn notation and vice versa. More precisely, since we are dealing with $\alpha$-equivalence classes, it is an isomorphism between the equivalence classes of named $\lambda$-terms and de Bruijn terms. 

We assume that $\lambda$-terms are built over the countable set of variables $x_1,x_2,x_3,...$. Then, the mapping from named terms to de Bruijn term is given by $f$, which we define in terms of an auxiliary function $e$:

\begin{center}
$\begin{aligned}
e_k^m(x_n) &= \begin{cases}
k-m(x_n)-1 & x_n \in \text{dom }m\\
k+n & otherwise
\end{cases}\\
e_k^m(uv) &= e_k^m(u)\ e_k^m(v)\\
e_k^m(\lambda x_n.u) &= \lambda\ e_{k+1}^{m \oplus (x_n,k)}(u)
\end{aligned}$
\end{center}

Then $f(t) = e_0^\emptyset(t)$.

The function $e$ takes two additional parameters, $k$ and $m$. $k$ keeps track of the scope from the root of the term and $m$ is a map from bound variables to the levels they were bound at. In the variable case, if $x_n$ appears in $m$, it is a bound variable, and its index can be calculated by taking the difference between the current index and the index $m(x_k)$ (at which the variable was bound). If $x_n$ is not in $m$, then the variable is encoded by adding the current level $k$ to $n$.   
In the abstraction case, $x_n$ is added to $m$ with the current level $k$, possibly overshadowing a previous binding of the same variable at a different level (like in $\lambda x_1. (\lambda x_1. x_1)$) and $k$ is incremented, going into the body of the abstraction. <!--For all closed terms, the choice of $k$ is arbitrary.-->

For the opposite direction, we replace indices with the corresponding indexed variables, taking care to chose named variables in such a way as to not capture any free variables.    
<div class="Example">A term like $\lambda (\lambda\ 2)$ intuitively represents a named $\lambda$-term which contains two bound variables and a free variable $x_0$. If we started giving the bound variables names in a naive way, for example starting from $x_0$, we would end up with a term $\lambda x_0.(\lambda x_1.x_0)$, which is obviously not the term we had in mind, as $x_0$ is no longer a free variable.</div>

<!--
The function $g$, taking de Bruijn terms to named terms is a little more tricky. We need to replace the indices encoding free variables (those that have a value greater than or equal to $k$, where $k$ is the number of binders in scope) with named variables, such that for every index $n$, we substitute $x_m$, where $m = n-k$, without capturing these free variables.

We need two auxiliary functions to define $g$:

\begin{center}
$\begin{aligned}
h_k^b(n) &= \begin{cases}
x_{n-k} & n \geq k\\
x_{k+b-n-1} & otherwise
\end{cases}\\
h_k^b(uv) &= h_k^b(u)\ h_k^b(v)\\
h_k^b(\lambda u) &= \lambda x_{k+b}.\ h_{k+1}^b(u)\\[2.5em]
\Diamond_k(n) &= \begin{cases}
n-k & n \geq k\\
0 & otherwise
\end{cases}\\
\Diamond_k(uv) &= \max (\Diamond_k(u),\ \Diamond_k(v))\\
\Diamond_k(\lambda u) &= \Diamond_{k+1}(u)
\end{aligned}$
\end{center}

The function $g$ is then defined as $g(t) = h_0^{\Diamond_0(t)+1}(t)$. As mentioned above, the complicated definition has to do with avoiding free variable capture. A term like $\lambda (\lambda\ 2)$ intuitively represents a named $\lambda$-term with two bound variables and a free variable $x_0$ according to the definition above. If we started giving the bound variables names in a naive way, starting from $x_0$, we would end up with a term $\lambda x_0.(\lambda x_1.x_0)$, which is obviously not the term we had in mind, as $x_0$ is no longer a free variable. To ensure we start naming the bound variables in such a way as to avoid this situation, we use $\Diamond$ to compute the maximal value of any free variable in the given term, and then start naming bound variables with an index one higher than the value returned by $\Diamond$.-->

As one quickly notices, terms like $\lambda x.x$ and $\lambda y.y$ have a single unique representation as a de Bruijn term $\lambda\ 0$. Indeed, since there are no named variables in a de Bruijn term, there is only one way to represent any $\lambda$-term, and the notion of $\alpha$-equivalence is no longer relevant. We thus get around our problem of having an inductive principle and $\alpha$-equivalent terms, by having a representation of $\lambda$-terms where every $\alpha$-equivalence class of $\lambda$-terms has a single representative term in the de Bruijn notation.

As pointed out by @berghofer06, the definition of substitution no longer needs the variable convention and can therefore be defined using primitive structural recursion. However, the main disadvantage of using de Bruijn indices is the relative unreadability of both the terms and the formulation of properties about these terms. For instance, take the substitution lemma, which in the named setting would be stated as:

\begin{center}
$\text{If }x \neq y\text{ and }x \not\in FV(L)\text{, then }
M[N/x][L/y] \equiv M[L/y][N[L/y]/x].$
\end{center}

In de Bruijn notation, the statement of this lemma becomes:

\begin{center}
$\text{For all indices }i, j\text{ with }i \leq j\text{, }M[N/i][L/j] = M[L/j + 1][N[L/j - i]/i]$
\end{center}

Clearly, the first version of this lemma is much more intuitive.

####Locally Nameless

The locally nameless approach to binders is a mix of the two previous approaches. Whilst a named representation uses variables for both free and bound variables and the nameless encoding uses de Bruijn indices in both cases as well, a locally nameless encoding distinguishes between the two types of variables.   
Free variables are represented by names, much like in the named version, and bound variables are encoded using de Bruijn indices. By using de Bruijn indices for bound variables, we again obtain an inductive definition of terms which are $\alpha$-equivalent.

While closed terms, like $\lambda x.x$ and $\lambda y.y$ are represented as de Bruijn terms, the term $\lambda x.xz$ and $\lambda y.yz$ are encoded as $\lambda\ 0z$. The following definition captures the syntax of the locally nameless terms:

~~~{.isabelle}
datatype ptrm =
  Fvar name
  BVar nat
| App trm trm
| Lam trm
~~~

Note however, that this definition doesn't quite fit the notion of $\lambda$-terms, since a `ptrm` like `(BVar 0)` does not represent a valid $\lambda$-term, since bound variables can only appear in the context of a $\lambda$, such as in `(Lam (BVar 0))`.   

The locally nameless approach is championed by @aydemir08, who claim several benefits:

> "First, our \[locally nameless\] presentation is transparent: the proofs closely follow their informal equivalents. Second the overheads of the approach are low: we do not need manual proofs of freshness side-conditions nor reasoning about alpha-equivalence ... At the same time, there is no need for external tools, and the style works in any general purpose theorem prover (although we found Coq to be well-suited to the task)."

Another advantage of using a locally nameless definition of $\lambda$-terms is a better readability of such terms, compared to equivalent de Bruijn terms. We decided to put these claims to test in  \cref{chap:compIsa} of this thesis and therefore chose the locally nameless approach for one of our mechanizations.

###Higher-Order approaches

Unlike concrete approaches to formalizing the $\lambda$-calculus, where the notion of binding and substitution is defined explicitly in the host language, higher-order formalizations use the function space of the implementation language, which handles binding. HOAS, or higher-order abstract syntax [@pfenning88, @harper93], is a framework for defining logics based on the simply typed $\lambda$-calculus.   
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
Originally, the field of higher order model checking mainly involved studying higher order recursion schemes (HORS), which are used to model higher-order programs, which are then checked exhaustively for desired properties, encoded as automata or intersection types. More recently, exploring the $\lamy$ calculus (an extension of the simply typed $\lambda$-calculus) as an alternative to using HORS to model programs, has gained traction (@clairambault13). We therefore present the $\lamy$ calculus, along with the proofs of the Church Rosser theorem and the formalization of intersection types for the $\lamy$ calculus, as the basis for formalizing the theory of HOMC.

###Definition of $\lamy$ terms

The first part of this project focuses on formalizing the simply typed $\lamy$ calculus and the proof of confluence for this calculus (proof of the Church Rosser Theorem is sometimes also referred to as proof of confluence). The usual/informal definition of the $\lamy$ terms and the simple types are given below:   
<div class="Definition" head="$\lamy$ types and terms">The set of simple types $\sigma$ is built up inductively form the $\mathsf{o}$ constant and the arrow type $\to$.     
Let $Var$ be a countably infinite set of atoms in the definition of the set of $\lamy$ terms $M$:
\label{Definition:lamyTrms}
\begin{center}
$\begin{aligned}
\sigma ::=&\ \mathsf{o}\ |\ \sigma \to \sigma \\
M ::=&\ x\ |\ MM\ |\ \lambda x.M\ |\ Y_\sigma \text{ where }x \in Var
\end{aligned}$
\end{center}
</div> 

The $\lamy$ calculus differs from the simply typed $\lambda$-calculus only in the addition of the $Y$ constant family, indexed at every simple type $\sigma$, where the (simple) type of a $Y_A$ constant (indexed with the type $A$) is $(A \to A) \to A$. The usual definition of $\beta Y$-reduction is then augmented with the $(Y)$ rule (this is the typed version of the rule):

\begin{center}
  \vskip 1em
  \AxiomC{$\Gamma \vdash M : \sigma \to \sigma$}
  \LeftLabel{$(Y)$}
  \UnaryInfC{$\Gamma \vdash Y_\sigma M \red M (Y_\sigma M) : \sigma$}
  \DisplayProof
  \vskip 1em
\end{center}

In essence, the $Y$ rule allows (some) well-typed recursive definitions over simply typed $\lambda$-terms.   
<div class="Example">
Take for example the term $\lambda x.x$, commonly referred to as the _identity_. The _identity_ term can be given a type $\sigma \to \sigma$ for any simple type $\sigma$. We can therefore perform the following (well-typed) reduction in the $\lamy$ calculus:

\begin{center}
$Y_\sigma (\lambda x.x) \red (\lambda x.x)(Y_\sigma (\lambda x.x))$
\end{center}
</div>

The typed version of the rule illustrates the restricted version of recursion clearly, since a recursive "$Y$-reduction" will only occur if the term $M$ in $Y_\sigma M$ has the matching type $\sigma \to \sigma$ (to $Y_\sigma$'s type $(\sigma \to \sigma) \to \sigma$), as in the example above. <!--Due to the type restriction on $M$, recursion using the $Y$ constant will be **weakly normalizing (this is right? right?)**, which cannot be said of unrestricted recursion in the untyped $\lambda$-calculus.-->


###Simple types

The simple types introduced above and presented throughout this work (except for \cref{chap:itypes}) are often referred to as simple types _a la Curry_, where a simply typed $\lambda$-term is a triple $(\Gamma, M, \sigma)$ written as $\Gamma \vdash M : \sigma$, where $\Gamma$ is the typing context, a finite set of variable and type tuples, $M$ is a term of the untyped $\lambda$-calculus and $\sigma$ is a simple type. A well typed term is valid, if one can construct a typing tree from the given type and typing context, using the following deduction system: 

<div class="Definition" head="Simple-type assignment">
\begin{center}
  \vskip 1.5em
  \AxiomC{$x : A \in \Gamma$}
  \LeftLabel{$(var)$}
  \UnaryInfC{$\Gamma \vdash x : A$}
  \DisplayProof
  %------------------------------------
  \hskip 1.5em
  \AxiomC{$\Gamma \vdash u : A \to B$}
  \AxiomC{$\Gamma \vdash v : A$}
  \LeftLabel{$(app)$}
  \BinaryInfC{$\Gamma \vdash uv : B$}
  \DisplayProof
  %------------------------------------
  \vskip 1.5em
  \AxiomC{$x : A,\Gamma \vdash m : B$}
  \LeftLabel{$(abs)$}
  \UnaryInfC{$\Gamma \vdash \lambda.m : A \to B$}
  \DisplayProof
  %------------------------------------
  \hskip 1.5em
  \AxiomC{}
  \LeftLabel{$(Y)$}
  \UnaryInfC{$\Gamma \vdash Y_{A} : (A \to A) \to A$}
  \DisplayProof
  \vskip 1.5em
\end{center}
</div>


<div class="Example">
Take the following simply typed term $\{y:\tau\} \vdash \lambda x.xy : (\tau \to \phi) \to \phi$. To show that this is a well-typed $\lambda$-term, we construct the following typing tree:

\begin{center}
    \vskip 1.5em
    \AxiomC{}
    \LeftLabel{$(var)$}
    \UnaryInfC{$\{x: \tau \to \phi,\ y:\tau\} \vdash x : \tau \to \phi$}
    \AxiomC{}
    \LeftLabel{$(var)$}
    \UnaryInfC{$\{x: \tau \to \phi,\ y:\tau\} \vdash y : \tau$}
    \LeftLabel{$(app)$}
    \BinaryInfC{$\{x: \tau \to \phi,\ y:\tau\} \vdash xy : \phi$}
    \LeftLabel{$(abs)$}
    \UnaryInfC{$\{y:\tau\} \vdash \lambda x.xy : (\tau \to \phi) \to \phi$}
    \DisplayProof
\end{center}
</div>

In the simple typing _a la Curry_, simple types and $\lambda$-terms are completely separate, brought together only through the typing relation $\vdash$. The definition of $\lamy$ terms, however, is dependent on the simple types in the case of the $Y$ constants, which are indexed by simple types. When talking about the $\lamy$ calculus, we tend to conflate the "untyped" $\lamy$ terms, which are just the terms defined in \cref{Definition:lamyTrms}, with the "typed" $\lamy$ terms, which are simply-typed terms _a la Curry_ of the form $\Gamma \vdash M : \sigma$, where $M$ is an "untyped" $\lamy$ term. Thus, results about the $\lamy$ calculus in this work are in fact results about the "typed" $\lamy$ calculus.

###Church-Rosser Theorem
\label{cr-def}

The Church-Rosser Theorem states that the $\beta Y$-reduction of the $\lambda$-calculus is confluent, that is, the reflexive-transitive closure of the $\beta Y$-reduction has the _diamond property_, i.e. $\dip(\red^*)$, where:

<div class="Definition" head="$\dip(R)$">
A binary relation $R$ has the _diamond property_, $\dip(R)$, iff

\begin{center}
$\forall a, b, c.\ aRb \land aRc \implies \exists d.\ bRd \land cRd$
\end{center}
</div>

The proof of confluence of $\red$, the $\beta Y$-reduction defined as the standard $\beta Y$-reduction with the addition of the aforementioned $(Y)$ rule, follows a variation of the Tait-Martin-Löf Proof originally described in @takahashi95 (specifically using the notes by @pollack95). To show why following this proof over the traditional proof is beneficial, we first give a high level overview of how the usual proof proceeds.

####Overview

In the traditional proof of the Church Rosser theorem, we define a new reduction relation, called the _parallel_ $\beta Y$-reduction ($\gg$), which, unlike the "plain" $\beta Y$-reduction satisfies the _diamond property_ (note that we are talking about the "single step" $\beta Y$-reduction and not the reflexive transitive closure). Once we prove the _diamond property_ for $\gg$, the proof of $\dip(\gg^*)$ follows easily. The reason why we prove $\dip(\gg)$ in the first place is because the reflexive-transitive closure of $\gg$ coincides with the reflexive transitive closure of $\red$ and it is much easier to prove $\dip(\gg)$ than trying to prove $\dip(\red^*)$ directly. The usual proof of the _diamond property_ for $\gg$ involves a double induction on the shape of the two parallel $\beta Y$-reductions from $M$ to $P$ and $Q$, where we try to show that the following diamond always exists, that is, given any reductions $M \gg P$ and $M \gg Q$, there is some $M'$ s.t. $P \gg M'$ and $Q \gg M'$:

\begin{figure}[h]
\begin{center}
\begin{tikzpicture}[->,>=stealth',shorten >=1pt,auto,node distance=2.8cm,semithick]
  \tikzstyle{every state}=[fill=none,draw=none,text=black]

  \node[state] (A)                                     {$M$};
  \node[state] (B) [below left= 1.3cm and 1.3cm of A]  {$P$};
  \node[state] (C) [below right= 1.3cm and 1.3cm of A] {$Q$};
  \node[state] (D) [below= 3cm of A]                   {$M'$};
 
  \path (A) edge [left]          node [pos=0.4] {$\gg$} (B)
            edge                 node [pos=0.59]           {$\gg$} (C)
        (B) edge [left, dashed]  node           {$\gg$} (D)
        (C) edge [right, dashed] node           {$\gg$} (D);
\end{tikzpicture}
\end{center}
\caption{The diamond property of $\gg$, visualized}
\end{figure}

The @takahashi95 proof simplifies this proof by eliminating the need to do simultaneous induction on the $M \gg P$ and $M \gg Q$ reductions. This is done by introducing another reduction, referred to as the _maximal parallel_ $\beta Y$-reduction ($\ggg$). The idea of using $\ggg$ is to show that for every term $M$ there is a reduct term $M_{max}$ s.t. $M \ggg M_{max}$ and that any $M'$, s.t. $M \gg M'$, also reduces to $M_{max}$. We can then separate the "diamond" diagram above into two instances of the following triangle, where $M'$ from the previous diagram is $M_{max}$:

\begin{figure}[h]
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
\caption{The proof of $\dip(\gg)$ is split into two instances of this triangle}
\label{figure:gggTriangle}
\end{figure}

Proving this triangle instead of the original diamond simplifies the overall proof, as there is no longer a need for the complicated double induction form the original proof.

####(Parallel) $\beta Y$-reduction
Having described the high-level overview of the classical proof and the reason for following the @takahashi95 proof, we now present some of the major lemmas in more detail, as they form the core comparison of the $\lamy$ calculus mechanizations, presented in \cref{chap:compIsa}.   
For later comparison to the parallel reductions, defined below, we first give the definition of the normal $\beta Y$-reduction:

<div class="Definition" head="$\beta Y$-reduction">
\begin{center}
    \AxiomC{$M \red M'$}
    \LeftLabel{$(red_L)$}
    \UnaryInfC{$MN \red M'N$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$N \red N'$}
    \LeftLabel{$(red_R)$}
    \UnaryInfC{$MN \red M'N$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{$M \red M'$}
    \LeftLabel{$(abs)$}
    \UnaryInfC{$\lambda x. M \red \lambda x. M'$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{}
    \LeftLabel{$(\beta)$}
    \UnaryInfC{$(\lambda x.M)N \red M[N/x]$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{}
    \LeftLabel{$(Y)$}
    \UnaryInfC{$Y_\sigma M \red M (Y_\sigma M)$}
    \DisplayProof
    \vskip 1.5em
\end{center}
</div>

Next, is the definition of _parallel_ $\beta Y$-reduction $\gg$ formulated for the terms of the $\lamy$ calculus, which allows simultaneous reduction of multiple parts of a term:

<div class="Definition" head="$\gg$">
\begin{center}
  \AxiomC{}
  \LeftLabel{$(refl)$}
  \UnaryInfC{$x \gg x$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{}
  \LeftLabel{$(refl_Y)$}
  \UnaryInfC{$Y_\sigma \gg Y_\sigma$}
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
  \AxiomC{$N \gg N'$}
  \LeftLabel{$(\beta)$}
  \BinaryInfC{$(\lambda x. M)N \gg M'[N'/x]$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$M \gg M'$}
  \LeftLabel{$(Y)$}
  \UnaryInfC{$Y_\sigma M \gg M' (Y_\sigma M')$}
  \DisplayProof
  \vskip 1.5em
\end{center}
</div>

The first difference between the normal $\beta Y$-reduction and _parallel_ $\beta Y$-reduction is the $(refl)/(refl_Y)$ rule, where $x \gg x$, for example, is a valid reduction, but we have $x \nRightarrow_Y x$ for the normal $\beta Y$-reduction ($x \red^* x$ is valid, since $\red^*$ is the reflexive transitive closure of $\red$). THe addition of these two rules then allows us to derive the general reflexivity rule $(refl^*): \forall M.\ M \gg M$ (see \cref{Lemma:reflM}).

<div class="Example">
\label{Example:ggVsGgg}
Another example where the two reductions differ is the simultaneous reduction of multiple sub-terms. _Parallel_ $\beta Y$-reduction, unlike $\red$, allows the reduction of the term $((\lambda xy.x)z)(\lambda x.x)y$ to $(\lambda y.z)y$, by simultaneously reducing the two sub-terms $(\lambda xy.x)z$ and $(\lambda x.x)y$ to $\lambda y.z$ and $y$ respectively:   
\begin{center}
  \vskip 1.5em
  \AxiomC{}
  \LeftLabel{$(refl^*)$}
  \UnaryInfC{$\lambda xy.x \gg \lambda xy.x$}
  \AxiomC{}
  \LeftLabel{$(refl)$}
  \UnaryInfC{$z \gg z$}
  \LeftLabel{$(\beta)$}
  \BinaryInfC{$(\lambda xy.x)z \gg \lambda y.z$}
  \AxiomC{}
  \LeftLabel{$(refl^*)$}
  \UnaryInfC{$\lambda x.x \gg \lambda x.x$}
  \AxiomC{}
  \LeftLabel{$(refl)$}
  \UnaryInfC{$y \gg y$}
  \LeftLabel{$(\beta)$}
  \BinaryInfC{$(\lambda x.x)y \gg y$}
  \LeftLabel{$(app)$}
  \BinaryInfC{$((\lambda xy.x)z)(\lambda x.x)y \gg (\lambda y.z)y$}
  \DisplayProof
  \vskip 1.5em
\end{center}

If we try to construct a similar tree for $\beta Y$-reduction, we quickly discover that the only two rules we can use are $(red_L)$ or $(red_R)$. We can thus only perform the right-side or the left side reduction of the two sub-terms, but not both<!--(for the rules of normal $\beta Y$-reduction see \cref{Definition:betaRedNom})-->.
</div>

Now that we have described the intuition behind the _parallel_ $\beta Y$-reduction, following @takahashi95, we proceed to define the _maximum parallel_ $\beta Y$-reduction $\ggg$, which contracts all redexes in a given term with a single step:

<div class="Definition" head="$\ggg$">
\begin{center}
  \AxiomC{}
  \LeftLabel{$(refl)$}
  \UnaryInfC{$x \ggg x$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{}
  \LeftLabel{$(refl_Y)$}
  \UnaryInfC{$Y_\sigma \ggg Y_\sigma$}
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

This relation only differs from $\gg$ in the $(app)$ rule, which can only be applied if $M$ is not a $\lambda$ or $Y$ term.

<div class="Example">
To demonstrate the difference between $\gg$ and $\ggg$, we take a look at the term $(\lambda xy.x)((\lambda x.x)z)$. Whilst $(\lambda xy.x)((\lambda x.x)z) \gg (\lambda xy.x)z$ or $(\lambda xy.x)((\lambda x.x)z) \gg \lambda y.z$ (amongst others) are valid reductions, the reduction $(\lambda xy.x)((\lambda x.x)z) \ggg (\lambda xy.x)z$ is not.    
To see why this is the case, we observe that the last rule applied in the derivation tree must have been the $(app)$ rule, since we see that a reduction on the sub-term $(\lambda x.x)z \ggg z$ occurs:

\begin{center}
  \AxiomC{$\vdots$}
  \UnaryInfC{$\lambda xy.x \ggg \lambda xy.x$}

  \AxiomC{$\vdots$}
  \UnaryInfC{$(\lambda x.x)z \ggg z$}
  \LeftLabel{$(app)$}
  \RightLabel{($\lambda xy.x$ is not a $\lambda$ or $Y$)}
  \BinaryInfC{$(\lambda xy.x)(\lambda x.x)z \ggg (\lambda xy.x)z$}
  \DisplayProof
  \vskip1em
\end{center}

However, this clearly could not happen, because $\lambda xy.x$ is in fact a $\lambda$-term.
</div>


To prove $\dip(\gg)$, we first show that there always exists a term $M_{max}$ for every term $M$, where $M \ggg M_{max}$ is the maximal parallel reduction which contracts all redexes in $M$:

<div class="Lemma">
\label{Lemma:maxEx}
$\forall M.\ \exists M_{max}.\ M \ggg M_{max}$
<div class="proof">
By induction on M.
</div></div>


Finally, we show that any parallel reduction $M \gg M'$ can be "closed" by reducing to the term $M_{max}$ where all redexes have been contracted (as seen in \cref{figure:gggTriangle}):

<div class="Lemma">
\label{Lemma:maxClose}
$\forall M, M', M_{max}.\ M \ggg M_{max} \land M \gg M' \implies M' \gg M_{max}$
<div class="proof">
Omitted. Can be found on p. 8 of the @pollack95 notes.
</div></div>


<div class="Lemma">$\dip(\gg)$
<div class="proof">
We can now prove $\dip(\gg)$ by simply applying \cref{Lemma:maxClose} twice, namely for any term $M$ there is an $M_{max}$ s.t. $M \ggg M_{max}$ (by \cref{Lemma:maxEx}) and for any $M', M''$ where $M \gg M'$ and $M \gg M''$, it follows by two applications of \cref{Lemma:maxClose} that $M' \gg M_{max}$ and $M'' \gg M_{max}$.
</div></div>

###Typed version of Church Rosser
The proof of the Church Rosser theorem, as presented above, uses the untyped definition of $\beta Y$-reduction. Whilst it is possible to define a typed version of $\beta Y$-reduction, it turned out to be much easier to first prove the Church Rosser theorem for the so called "untyped" $\lamy$ calculus and then additionally restrict this result to only well-typed $\lamy$ terms.   
Thus, the definition of the Church Rosser Theorem, formulated for the $\lamy$ calculus, is the following one:

<div class="Theorem" head="Typed Church Rosser Theorem">
$\Gamma \vdash M : \sigma \land M \red^* M' \land M \red^* M'' \implies \exists M'''.\ \ M' \red^* M''' \land M'' \red^* M''' \land \Gamma \vdash M''' : \sigma$
</div>

In order to prove this typed version of the Church Rosser Theorem, we need to prove an additional result of subject reduction for $\lamy$ calculus, which states that if a simply typed term $M$ (with a type $\tau$) $\beta Y$-reduces to $M'$, $M'$ can also be typed with $\tau$:

<div class="Theorem" head="Subject reduction for $\red^*$">
\label{Theorem:subRedSimp}
$\Gamma \vdash M : \sigma \land M \red^* M' \implies \Gamma \vdash M' : \sigma$
</div>

\newpage
##Intersection types
\label{itypesIntro}

For the formalization of intersection types, we initially chose a _strict_ intersection-type system, presented in the @bakel notes. Intersection types, classically presented by @barendregt13 as $\lambda_\cap^{BCD}$, extend simple types by adding a conjunction to the definition of types:

<div class="Definition" head="$\lambda_\cap^{BCD}$ types">
In the definition below, $\phi$ is a constant (analogous to the constant $\mathsf{o}$, introduced for the simple types in \cref{Definition:lamyTrms}). To avoid confusion between simple and intersection types, the usual arrow-type notation $\to$, used in the definition of both type-systems is substituted for the $\leadsto$ arrow.
\begin{center}
$\mathcal{T} ::= \phi\ |\ \mathcal{T} \leadsto \mathcal{T}\ |\ \mathcal{T} \cap \mathcal{T}$
\end{center}
</div>

Following @bakel, we restrict ourselves to a version of intersection types often called _strict_ intersection types. _Strict_ intersection types are a restriction on $\lambda_\cap^{BCD}$ types, where an intersection of types can only appear on the left side of an "arrow" type:

<div class="Definition" head="Strict intersection types">
\label{Definition:itypes}
As in the definition above, $\phi$ is a constant.

\begin{center}
$\begin{aligned}
\mathcal{T}_s &::= \phi\ |\ \mathcal{T} \leadsto \mathcal{T}_s \\ 
\mathcal{T} &::= (\mathcal{T}_s \cap\hdots\cap \mathcal{T}_s)
\end{aligned}$
\end{center}
</div>

The following conventions for intersection types are adopted throughout this section; 
$\omega$ stands for the empty intersection and we write $\taui$ for the type $\tau_1 \cap\hdots\cap \tau_n$. We also define a subtype relation $\subseteq$ for intersection types, which intuitively captures the idea of one intersection of types being a subset of another, where we think of $\tau_1 \cap \hdots \cap \tau_i$ as a finite set $\{\tau_1, \hdots , \tau_i\}$, wherein $\subseteq$ for intersection types roughly corresponds to subset inclusion e.g. $\tau \subseteq \tau \cap \psi$ because $\{\tau\} \subseteq \{\tau, \psi\}$.   

$\ $
<div class="Remark">
The reason for defining the subset relation in this way, rather than taking the usual view of $\tau \cap \phi \leq \tau$, was due the implementation of intersection types in Agda. Since intersection types $\mathcal{T}$ ended up being defined as lists of strict types $\mathcal{T}_s$ (the definition of lists in Agda included the notion of list inclusion $\in$ and by extension the $\subseteq$ relation), the above convention seemed more natural.</div>

The formal definition of this relation is given below:

<div class="Definition" head="$\subseteq$">
\label{Definition:subseteqOrig}
This relation is the least pre-order on intersection types s.t.:

\begin{center}
$\begin{aligned}
\forall\ i \in \underline{n}.\ \ \tau_i \subseteq& \taui \\ 
\forall\ i \in \underline{n}.\ \ \tau_i \subseteq \psi \implies& \taui \subseteq \psi \\
\rho \subseteq \psi \land \tau \subseteq \mu \implies& \psi \leadsto \tau \subseteq \rho \leadsto \mu\\
\end{aligned}$
\end{center}

(This relation is equivalent the $\leq$ relation, defined in @bakel notes, i.e. $\tau \leq \psi = \psi \subseteq \tau$.)
</div>


In this presentation, $\lamy$ terms are typed with the strict types $\mathcal{T}_s$ only. Much like the simple types, presented in the previous sections, an intersection-typing judgment is a triple $\Gamma, M, \tau$, written as $\Gamma \vDash M : \tau$, where $\Gamma$ is the intersection-type context, similar in construction to the simple typing context, $M$ is a $\lamy$ term and $\tau$ is a strict intersection type $\mathcal{T}_s$.    
The definition of the intersection-typing system, like the $\subseteq$ relation, has also been adapted from the typing system found in the @bakel notes, by adding the typing rule for the $Y$ constants:   
<div class="Definition" head="Intersection-type assignment">$\ $
\begin{center}
  \AxiomC{$x: \taui \in \Gamma$}
  \AxiomC{$\tau \subseteq \taui$}
  \LeftLabel{$(var)$}
  \BinaryInfC{$\Gamma \Vdash x : \tau$}
  \DisplayProof
  %------------------------------------
  \hskip 1.5em
  \AxiomC{$\Gamma \Vdash M : \taui \leadsto \tau$}
  \AxiomC{$\forall\ i \in \underline{n}.\ \ \Gamma \Vdash N : \tau_i$}
  \LeftLabel{$(app)$}
  \BinaryInfC{$\Gamma \Vdash MN : \tau$}
  \DisplayProof
  %------------------------------------
  \vskip 1.5em
  \AxiomC{$x: \taui,\Gamma \Vdash M : \tau$}
  \LeftLabel{$(abs)$}
  \UnaryInfC{$\Gamma \Vdash \lambda x.M : \taui \leadsto \tau$}
  \DisplayProof
  %------------------------------------
  \vskip 1.5em
  \AxiomC{}
  \LeftLabel{$(Y)$}
  \RightLabel{$(j \in \underline{n})$}
  \UnaryInfC{$\Gamma \Vdash Y_\sigma : (\taui \leadsto \tau_1 \cap\hdots\cap \taui \leadsto \tau_i) \leadsto \tau_j$}
  \DisplayProof
\end{center}
</div>

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
  \AxiomC{$x \not\in \dom\ \Gamma$}
  \AxiomC{$\wf \Gamma$}
  \LeftLabel{$(cons)$}
  \BinaryInfC{$\wf (x: \bigcap\tau_i,\Gamma)$}
  \DisplayProof
  \vskip 1.5em
\end{center}
</div>

###Type refinement
\label{initTypeRefine}

It is important for the theory underpinning HOMC to be decidable. In order to guarantee this, we introduce a type refinement relation $\tau :: A$ for intersection types, where $\tau$ is an intersection type, refining a simple type $A$. Intuitively, the notion of refinement restricts the intersection types to those which correspond in "shape" to the simple type they refine. By restricting intersection types to only those that refine a given simple type, we can guarantee that the search space for an intersection type, which can type a given $\lamy$ term $M$ with the simple type $A$ is finite (and typing such a term is thus decidable), since the set $\{\tau\ |\ \tau :: A\}$ is finite. Therefore, enumerating and checking whether $\Gamma \Vdash M : \tau$ for any of the types $\tau$ in this set will take finite time.

We define the type refinement relation, presented by @kobayashi09 (amongst others):   
<div class="Definition" head="Intersection-type refinement">
\begin{center}
  \AxiomC{}
  \UnaryInfC{$\phi :: \mathsf{o}$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\taui :: A$}
  \AxiomC{$\tau :: B$}
  \BinaryInfC{$\taui \leadsto \tau :: A \to B$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\forall i \in \underline{n}.\ \ \tau_i :: A$}
  \UnaryInfC{$\taui :: A$}
  \DisplayProof
\end{center}
</div>

###Subject invariance
\label{initSubjectInv}

An interesting property of intersection-type systems is the fact that they admit both subject expansion and subject reduction, namely $\Vdash$ is closed under $\beta Y$-equality. This means that given a term $M$ with intersection type $\tau$ and $N$ s.t. $M =_\beta N$, $N$ can be typed at $\tau$:

<div class="Theorem" head="Subject invariance for $\Vdash$">

i)    Subject reduction: $\Gamma \Vdash m : \tau \implies m \red m' \implies \Gamma \Vdash m' : \tau$
ii)   Subject expansion: $\Gamma \Vdash m' : \tau \implies m \red m' \implies \Gamma \Vdash m : \tau$
</div>   

$\ $
<div class="Remark">The definitions presented in this section are the initial definitions, used as a basis for the mechanization discussed in \cref{chap:itypes}. Due to different obstacles in the formalization of the subject invariance proofs, these definitions were amended several times. The reasons for these changes are also documented in \cref{chap:itypes}.</div>

