---
header-includes:
- \usepackage{bussproofs}
- \usepackage{amsthm}
- \usepackage{minted}
- \hypersetup{ colorlinks=true, linkcolor=blue, filecolor=magenta, urlcolor=cyan}
- \urlstyle{same}
- \let\OldTexttt\texttt
- \renewcommand{\texttt}[1]{\small\OldTexttt{#1}}
- \newcommand{\concat}{\ensuremath{+\!\!\!\!+\,}}
---

#Intersection types

In this section, we will work with both the simple types introduced earlier (definition given again below), as well as intersection types, defined in the following way:
$\\$

**Definition** (Types) - Note that $\mathsf{o}$ and $\varphi$ are constants. $\omega$ is used to denote an empty list of strict intersection types and $\bigcap \tau \equiv [ \tau ]$.

i)  Simple types:
    $$\sigma ::= \mathsf{o}\ |\ \sigma \to \sigma$$
ii) Intersection types:
    $$\mathcal{T}_s ::= \varphi\ |\ \mathcal{T} \leadsto \mathcal{T}$$
    $$\mathcal{T} ::= \mathsf{List}\ \mathcal{T}_s$$


The reason why $\mathcal{T}$ is defined as a list of strict types $\mathcal{T}_s$ is due to the requirement that the types in $\mathcal{T}$ be finite. The decision to use lists was taken because the Agda standard library includes a definition of lists along with definitions of list membership $\in$ for lists and other associated lemmas.

Next, we redefine the $\lambda$-terms slightly, by annotating the terms with simple types. The reason for this will be clear later on.

**Definition** (Terms) - Let $\sigma$ range over simple types in the following definition:

i)  Simply-typed terms:
    $$M::= x_\sigma\ |\ MM\ |\ \lambda x_\sigma.M\ |\ Y_\sigma \text{ where }x \in Var$$
ii) Simply-typed pre-terms:
    $$M'::= x_\sigma\ |\ i\ |\ M'M'\ |\ \lambda_\sigma.M'\ |\ Y_\sigma \text{ where }x \in Var\text{ and }i \in \mathbb{N}$$

Note that both definitions implicitly assume that in the case of application, a well formed simply-typed term will be of the form $st$, where $s$ has some simple type $A \to B$ and $t$ is typed with the simple type $A$. Sometimes the same subscript notation will be used to indicate the simple type of a given pre-/term, for example: $m_{A \to B}$.    
The typed versions of substitution and the open and close operations are virtually identical to the untyped versions.

##Type refinement

Next, we introduce the notion of type refinement by defining the refinement relation $::$, between simple types and intersection types.

**Definition** ($::$) - Since intersection types are defined in terms of strict ($\mathcal{T}_s$) and non-strict ($\mathcal{T}$) intersection types, for correct typing, the definition of $::$ is split into two versions, one for strict and another for non-strict types. In the definition below, $\tau$ ranges over strict intersection types $\mathcal{T}_s$, with $\tau_i, \tau_j$ ranging over non-strict intersection types $\mathcal{T}$, and $A, B$ range over simple types $\sigma$:

\begin{center}
    \AxiomC{}
    \LeftLabel{$(base)$}
    \UnaryInfC{$\varphi ::_s \mathsf{o}$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\tau_i :: A$}
    \AxiomC{$\tau_j :: B$}
    \LeftLabel{$(arr)$}
    \BinaryInfC{$\tau_i \leadsto \tau_j ::_s A \to B$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{}
    \LeftLabel{$(nil)$}
    \UnaryInfC{$\omega :: A$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\tau ::_s A$}
    \AxiomC{$\tau_i :: A$}
    \LeftLabel{$(cons)$}
    \BinaryInfC{$(\tau ,\ \tau_i) :: A$}
    \DisplayProof
\end{center}

Having a notion of refinement, we define a restricted version of a subset relation on intersection types, which is defined only for pairs of intersection types, which refine the same simple type.

**Definition** ($\subseteq^A$) - In the definition below, $\tau, \tau'$ range over $\mathcal{T}_s$, $\tau_i, \hdots, \tau_n$ range over $\mathcal{T}$ and $A, B$ range over $\sigma$:

\begin{center}
    \AxiomC{}
    \LeftLabel{$(base)$}
    \UnaryInfC{$\varphi \subseteq^\mathsf{o}_s \varphi$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\tau_i \subseteq^A \tau_j$}
    \AxiomC{$\tau_m \subseteq^B \tau_n$}
    \LeftLabel{$(arr)$}
    \BinaryInfC{$\tau_j \leadsto \tau_m \subseteq^{A \to B}_s \tau_i \leadsto \tau_n$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{$\tau_i :: A$}
    \LeftLabel{$(nil)$}
    \UnaryInfC{$\omega \subseteq^A \tau_i$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\exists \tau' \in \tau_j.\ \tau \subseteq^A_s \tau'$}
    \AxiomC{$\tau_i \subseteq^A \tau_j$}
    \LeftLabel{$(cons)$}
    \BinaryInfC{$(\tau ,\ \tau_i) \subseteq^A \tau_j$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{$(\tau_i \leadsto (\tau_j \concat \tau_k) ,\ \tau_m) :: A \to B$}
    \LeftLabel{$(\leadsto\cap)$}
    \UnaryInfC{$(\tau_i \leadsto (\tau_j \concat \tau_k) ,\ \tau_m) \subseteq^{A \to B} (\tau_i \leadsto \tau_j ,\ \tau_i \leadsto \tau_k ,\ \tau_m)$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\tau_i \subseteq^A \tau_j$}
    \AxiomC{$\tau_j \subseteq^A \tau_k$}
    \LeftLabel{$(trans)$}
    \BinaryInfC{$\tau_i \subseteq^A \tau_k$}
    \DisplayProof
\end{center}

It's easy to show the following properties hold for the $\subseteq^A$ and $::$ relations:

**Lemma** ($\subseteq\implies::$)

i)  $\tau \subseteq^A_s \delta \implies \tau ::_s A \land \delta ::_s A$
ii) $\tau_i \subseteq^A \delta_i \implies \tau_i :: A \land \delta_i :: A$

_Proof:_ By **?mutual?** induction on the relations $\subseteq^A_s$ and $\subseteq^A$.

**Lemma** ($\subseteq$-_refl_) 

i)  $\tau ::_s A \implies \tau \subseteq^A_s \tau$
ii) $\tau_i :: A \implies \tau_i \subseteq^A \tau_i$

_Proof:_ By induction on $\tau$ and $\tau_i$.

##Intersection type assignment


Having annotated the $\lambda$-terms with simple types, the following type assignment only permits the typing of simply-typed $\lambda$-terms with an intersection type, which refines the simple type of the $\lambda$-term:


**Definition** (Intersection-type assignment) 
\begin{center}
    \AxiomC{$\exists (x, \tau_i, A) \in \Gamma.\ \bigcap \tau \subseteq^A \tau_i$}
    \LeftLabel{$(var)$}
    \UnaryInfC{$\Gamma \Vdash_s x_A : \tau$}
    \DisplayProof
    %------------------------------------
    \hskip 1.5em
    \AxiomC{$\Gamma \Vdash_s s : \tau_i \leadsto \tau_j$}
    \AxiomC{$\Gamma \Vdash t : \tau_i$}
    \LeftLabel{$(app)$}
    \RightLabel{$(\bigcap \tau \subseteq^B \tau_j)$}
    \BinaryInfC{$\Gamma \Vdash_s st : \tau$}
    \DisplayProof
    %------------------------------------
    \vskip 1.5em
    \AxiomC{$\forall x \not\in L.\ (x, \tau_i, A),\Gamma \Vdash t_B^x : \tau_j$}
    \LeftLabel{$(abs)$}
    \UnaryInfC{$\Gamma \Vdash_s \lambda_A.t : \tau_i \leadsto \tau_j$}
    \DisplayProof
    %------------------------------------
    \hskip 1.5em
    \AxiomC{$\exists \tau_x.\ \bigcap \tau_x \leadsto \tau_x \subseteq^{A \to A} \tau_i \land \tau_j \subseteq^A \tau_x$}
    \LeftLabel{$(Y)$}
    \UnaryInfC{$\Gamma \Vdash_s Y_{A} : \tau_i \leadsto \tau_j$}
    \DisplayProof
    %------------------------------------
    \vskip 1.5em
    \AxiomC{$\Gamma \Vdash_s m_{A \to B} : \tau_i \leadsto \tau_j$}
    \AxiomC{$\Gamma \Vdash_s m_{A \to B} : \tau_i \leadsto \tau_k$}
    \LeftLabel{$(\leadsto\cap)$}
    \RightLabel{$(\tau_j \concat \tau_k \subseteq^B \tau_x)$}
    \BinaryInfC{$\Gamma \Vdash_s m_{A \to B} : \tau_i \leadsto \tau_x$}
    \DisplayProof
    %------------------------------------
    \vskip 1.5em
    \AxiomC{$\tau_i :: A$}
    \LeftLabel{$(nil)$}
    \UnaryInfC{$\omega \subseteq^A \tau_i$}
    \DisplayProof
    %------------------------------------
    \hskip 1.5em
    \AxiomC{$\exists \tau' \in \tau_j.\ \tau \subseteq^A_s \tau'$}
    \AxiomC{$\bigcap \tau_i \subseteq^A \tau_j$}
    \LeftLabel{$(cons)$}
    \BinaryInfC{$(\tau ,\ \tau_i) \subseteq^A \tau_j$}
    \DisplayProof
\end{center}
<!--
\newpage
#References
-->