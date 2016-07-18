#Methodology

##Comparison of formalizations

The idea of formalizing a functional language in multiple theorem provers and objectively assessing the merits and pitfalls of the different formalizations is definitely not a new idea. The most well known attempt to do so on a larger scale is the $\poplm$ challenge, proposed in the "Mechanized Metatheory for the Masses: The $\poplm$ Challenge" paper by @aydemir05.   
Whilst this paper prompted several formalizations of the benchmark typed $\lambda$-calculus, proposed by the authors of the challenge, in multiple theorem provers, such as Coq, Isabelle, Matita or Twelf, there seems to have been no attempt made at analyzing and comparing the different formalizations and drawing any conclusions with regards to the stated aims of the challenge.

Whilst this project does not aim to answer the same question as the original challenge, namely: 

> "How close are we to a world where every paper on programming languages is accompanied by an electronic appendix with machine- checked proofs?" (@aydemir05)

It draws inspiration from the criteria for the "benchmark mechanization", specified by the challenge.

The comparison proceeded in two stages of elimination, where the first stage was a comparison of the two chosen mechanizations of binders for the $\lamy$ calculus ([Chapter 4](#comp-isa)), namely nominal set and locally nameless representations of binders.   
After choosing the optimal mechanization of binders, the [next chapter](#comp-agda) then goes on to compare this mechanization in two different theorem provers, Isabelle and Agda.   
The "wining" theorem prover from this round was then used to formalize intersection-types and prove subject invariance.

###Evaluation criteria

The $\poplm$ challenge stated three main criteria for evaluating the submitted mechanizations of the benchmark calculus:

- Mechanization/implementation overheads
- Technology transparency
- Cost of entry

To this, we add another criterion: 

- Proof automation

This project focuses mainly on the tree criteria of mechanization overheads, technology transparency and automation, since the focus of our comparison is to chose the best mechanization and theorem prover to use for implementing intersection types for the $\lamy$ calculus (and proving subject invariance). These criteria are described in greater detail below:

####Mechanization/implementation overheads

This aspect of the mechanization is explored predominantly in the next chapter, which compares two different approaches to formalizing binders in the $\lamy$ calculus. Binders are an aspect of our chosen formalization, where mechanization overheads are most apparent, as binders are usually overlooked to a large extent in informal setting.   
As was discussed previously, the treatment of binders is a well studied problem with several viable solutions. In this project, we decided to use nominal sets and locally nameless representation for binders, due to several reasons.    
The choice of nominal sets was tied to the implementation language, namely Isabelle, which has a well developed [nominal sets library](http://www.inf.kcl.ac.uk/staff/urbanc/Nominal/), maintained by Christian Urban. The appeal of using nominal sets is of course the touted minimal overheads in comparison to the informal presentation.   
The choice of locally nameless encoding, as opposed to using pure de Bruijn indices, was motivated by the claim that locally nameless encoding largely mitigates the disadvantages of de Bruin indices especially when it comes to technology transparency (i.e. theorems about locally nameless presentation are much closer in formulation to the informal presentation than theorems formulated for de Bruijn indices).   
Both of these choices were guided in part by the initial choice of implementation language, Isabelle, which was chosen mainly due to previous experience in mechanizing similar proofs.   
The comparison between nominal and locally nameless versions of the $\lamy$ calculus, presented in [Chapter 4](#comp-isa), tries to highlight the differences in the two approaches in contrast to the usual informal reasoning.

####Technology transparency

This criterion is discussed mainly in [Chapter 5](#comp-agda), which deals with the comparison of Isabelle and Agda. The choice of the two theorem provers, but especially of Isabelle, was largely subjective. Having had previous experience with Isabelle, it was natural to use it initially, to lower the cost of entry. Initially only using Isabelle for both formalizations of binders also allowed for a more uniform comparison of the mechanization overheads.   
The choice of Agda as the second implementation language was motivated by Agda having a dependent-type system. As a result, the style of proofs in Agda seems quite different to Isabelle, since the distinction between proofs and programs is largely erased. Agda was chosen over Coq, which is also a dependently-typed language, because it is more "bare-bones" and thus seemed more accessible to a novice in dependently-typed languages. __Agda also has a higher "cool"-factor than Coq, being a newer language. (Is a joke here ok?)__


####Proof automation

Proof automation ties into both the mechanization overheads and transparency aspects of a formalization, since high degree of automation can often result in a more natural/transparent looking proof where the "menial" reasoning steps are taken care of by the theorem prover, and the user only sees the higher-level reasoning of informal proofs.    
Both following chapters discuss the automation features of Isabelle and Agda and try to draw comparisons by analyzing the same/equivalent lemmas in different mechanizations and theorem provers, in terms of automation. Whilst on paper, Isabelle includes a lot more automation, in the form of several tactics and automated theorem provers, whereas Agda comes with only very simple proof search tactics, Agda's more sophisticated type-system takes on and replicates at least some of the automation seen in Isabelle.


<!--
###Scope of comparison

The high-level overview of the main results formalized in all versions of the $\lamy$ calculus mechanizations can be found in the previous chapter. 

##$\lamy$ calculus - Definitions

**Syntax (nominal)**

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
    \UnaryInfC{$Y_\sigma M \Rightarrow M (Y_\sigma M)$}
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
\end{center} -->