#Methodology

##$\lambda$-Y calculus - Definitions

**Syntax (nominal)**

Types: 
$$\sigma ::= a\ |\ \sigma \to \sigma \text{ where }a \in \mathcal{TV}$$

Terms:
$$M::= x\ |\ MM\ |\ \lambda x.M\ |\ Y_\sigma \text{ where }x \in Var$$


**Well typed terms (nominal)**

\begin{center}
    \AxiomC{}
    \LeftLabel{$(var)$}
    \RightLabel{$(x : \sigma \in \Gamma)$}
    \UnaryInfC{$\Gamma \vdash x : \sigma$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{}
    \LeftLabel{$(Y)$}
    \UnaryInfC{$\Gamma \vdash Y_\sigma : (\sigma \to \sigma) \to \sigma$}
    \DisplayProof
    \vskip 1.5em
    \AxiomC{$\Gamma \cup \{x:\sigma\} \vdash M : \tau$}
    \LeftLabel{$(abs)$}
    \RightLabel{$(x\ \sharp\ \Gamma/ x \not\in Subjects(\Gamma))$}
    \UnaryInfC{$\Gamma \vdash \lambda x. M : \sigma \to \tau$}
    \DisplayProof
    \hskip 1.5em
    \AxiomC{$\Gamma \vdash M : \sigma \to \tau$}
    \AxiomC{$\Gamma \vdash N : \sigma$}
    \LeftLabel{$(app)$}
    \BinaryInfC{$\Gamma \vdash MN : \tau$}
    \DisplayProof
\end{center}

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
    \UnaryInfC{$M \Rightarrow M (Y_\sigma M)$}
    \DisplayProof
\end{center}


-------------------





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