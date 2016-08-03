#Intersection types
\label{chap:itypes}

Having compared different mechanizations and implementation languages for the simply typed $\lamy$ calculus in the previous two chapters, we arrived at the "winning" combination of a locally nameless mechanization using Agda. Carrying on in this setting, in this chapter, we present the formalization of intersection types for the $\lamy$ calculus along with the proof of subject invariance for intersection types.   
Whilst the proof is not novel, there is, to our knowledge, no known of it for the $\lamy$ calculus. The chapter mainly focuses on the engineering choices that were made in order to simplify the proofs as much as possible, as well as the necessary implementation overheads that were necessary for the implementation.    
The chapter is presented in sections, each explaining implementation details that had to be considered and any tweaks to the definitions, presented in \cref{itypesIntro}, that were needed to be made.

##Intersection types in Agda
\label{itypesAgda}

The first implementation detail we had to consider was the implementation of the definition of intersection types themselves. Unlike simple types, the definition of intersection-types is split into two mutually recursive definitions of strict `ITypeS` ($\mathcal{T}_s$) and non-strict `IType` ($\mathcal{T}$) intersection types:

~~~{.agda xleftmargin=1em linenos=true}
data IType : Set
data ITypeS : Set

data ITypeS where
  φ : ITypeS
  _~>_ : (s : IType) -> (t : ITypeS) -> ITypeS

data IType where
  ∩ : List ITypeS -> IType
~~~

The reason why `IType` is defined as a list of strict types `ITypeS` in line 9, is due to the (usually) implicit requirement that the types in $\mathcal{T}$ be finite. The decision to use lists was taken because the Agda standard library includes a definition of lists along with definitions of list membership $\in$ for lists and other associated lemmas, which proved to be useful for definitions of the $\subseteq$ relation on types. 


From the above definition, it is obvious that the above definition is redundant, in that `IType` only has one constructor `∩`, taking a list of strict types `ITypeS`, and therefore, any instance of `IType` in the definition of `ITypeS` can simply be replaced by `List ITypeS`:

~~~{.agda}
data IType : Set where
  φ : IType
  _~>_ : List IType -> IType -> IType
~~~

(Note that `ITypeS` was renamed to `IType` for convenience.)

##Type refinement

One of the first things we needed to add to the notion of intersection type assignment (and as a result also to the $\subseteq$ relation on intersection types) was the notion of simple-type refinement. The main idea of intersection types for $\lamy$ terms is for the intersection types to somehow "refine" the simple types. Intuitively, this notion should capture the relationship between the "shape" of the intersection and simple types. 

To demonstrate the reason for introducing type refinement, we look at the initial formulation of the (intersection) typing rule $(Y)$:

\begin{center}
  \vskip 1.5em
  \AxiomC{}
  \LeftLabel{$(Y)$}
  \RightLabel{$(j \in \underline{n})$}
  \UnaryInfC{$\Gamma \Vdash Y_\sigma : (\taui \leadsto \tau_1 \cap\hdots\cap \taui \leadsto \tau_i) \leadsto \tau_j$}
  \DisplayProof
  \vskip 1.5em
\end{center}

The lack of connection between simple and intersection types in the typing relation is especially apparent here, as $\taui$ seems to be chosen arbitrarily. Once we reformulate the above definition to include type refinement, the choice of $\taui$ makes more sense, since we know that $\tau_1, \hdots, \tau_i$ will somehow be related to the simple type $\sigma$:

\begin{center}
  \vskip 1.5em
  \AxiomC{$\taui :: \sigma$}
  \LeftLabel{$(Y)$}
  \RightLabel{$(j \in \underline{n})$}
  \UnaryInfC{$\Gamma \Vdash Y_\sigma : (\taui \leadsto \tau_1 \cap\hdots\cap \taui \leadsto \tau_i) \leadsto \tau_j$}
  \DisplayProof
  \vskip 1.5em
\end{center}


The refinement relation has been defined in @kobayashi09 (amongst others) and is presented below:

<div class="Definition" head="Intersection type refinement">
Since intersection types are defined in terms of strict ($\mathcal{T}_s$) and non-strict ($\mathcal{T}$) intersection types, the definition of refinement ($::$) is split into two versions, one for strict and another for non-strict types. In the definition below, $\tau$ ranges over strict intersection types $\mathcal{T}_s$, with $\tau_i, \tau_j$ ranging over non-strict intersection types $\mathcal{T}$, and $A, B$ range over simple types $\sigma$:

\begin{center}
  \AxiomC{}
  \LeftLabel{$(base)$}
  \UnaryInfC{$\phi :: \mathsf{o}$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\tau_i ::_\ell A$}
  \AxiomC{$\tau_j ::_\ell B$}
  \LeftLabel{$(arr)$}
  \BinaryInfC{$\tau_i \leadsto \tau_j :: A \to B$}
  \DisplayProof
  \vskip 1.5em
  \AxiomC{}
  \LeftLabel{$(nil)$}
  \UnaryInfC{$\omega ::_\ell A$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\tau :: A$}
  \AxiomC{$\tau_i ::_\ell A$}
  \LeftLabel{$(cons)$}
  \BinaryInfC{$\tau , \tau_i ::_\ell A$}
  \DisplayProof
\end{center}
</div>

Having a notion of type refinement, we then modified the subset relation on intersection types, s.t. $\subseteq$ is defined only for pairs of intersection types, which refine the same simple type:

<div class="Definition" head="$\subseteq^A$">
In the definition below, $\tau, \tau'$ range over $\mathcal{T}_s$, $\tau_i, \hdots, \tau_n$ range over $\mathcal{T}$ and $A, B$ range over $\sigma$:

\begin{center}
  \AxiomC{}
  \LeftLabel{$(base)$}
  \UnaryInfC{$\phi \subseteq^\mathsf{o} \phi$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\tau_i \subseteq^A_\ell \tau_j$}
  \AxiomC{$\tau_m \subseteq^B \tau_n$}
  \LeftLabel{$(arr)$}
  \BinaryInfC{$\tau_j \leadsto \tau_m \subseteq^{A \to B} \tau_i \leadsto \tau_n$}
  \DisplayProof
  \vskip 1.5em
  \AxiomC{$\tau_i ::_\ell A$}
  \LeftLabel{$(nil)$}
  \UnaryInfC{$\omega \subseteq^A_\ell \tau_i$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\exists \tau' \in \tau_j.\ \tau \subseteq^A \tau'$}
  \AxiomC{$\tau_i \subseteq^A_\ell \tau_j$}
  \LeftLabel{$(cons)$}
  \BinaryInfC{$\tau , \tau_i \subseteq^A_\ell \tau_j$}
  \DisplayProof
  \vskip 1.5em
\end{center}
</div>

The typing relation **add link to future def** was also modified to include type refinement **... didn't want to include it here because it will differ significantly from the initial** 

##Well typed $\subseteq$

The presentation of the $\subseteq$ relation in \cref{Definition:subseteqOrig} differs quite significantly from the one presented above. The main difference is obviously the addition of type refinement, but the definition now also includes the $(base)$ rule, which allows one to derive the  previously **?verbally/implicitly?** stated reflexivity and transitivity rules.
<!--\vspace{1.5em}
<div class="Remark">
From $(base)$, one can prove the general $(refl_S)$ and $(refl)$ rules: 

<div class="Lemma">
The following rules are admissible in $\subseteq^A_s/\subseteq^A$:

\begin{center}
  \AxiomC{$\tau ::_s A$}
  \LeftLabel{$(refl_s)$}
  \UnaryInfC{$\tau \subseteq^A_s \tau$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\tau_i :: A$}
  \LeftLabel{$(refl)$}
  \UnaryInfC{$\tau_i \subseteq^A \tau_i$}
  \DisplayProof
\end{center}

</div>
</div>-->   
Another departure from the original definition is the formulation of the following two properties as the $(nil)$ and $(cons)$ rules:

\begin{center}
$\begin{aligned}
\forall\ i \in \underline{n}.\ \ \tau_i \subseteq& \taui \\ 
\forall\ i \in \underline{n}.\ \ \tau_i \subseteq \tau \implies& \taui \subseteq \tau \\
\end{aligned}$
\end{center}

To give a motivation as to why we chose the formulation of these rules, we first examine the original definition and show why it's not rigorous enough for a well typed Agda definition.   
As we've shown in \cref{itypesAgda}, the definition of intersection types is implicitly split into strict `IType`'s and intersections, encoded as `List IType`'s. All the preceding definitions follow this split with the strict and non strict versions of the type refinement ($::$ and $::_\ell$ respectively) and sub-typing relations ($\subseteq$ and $\subseteq_\ell$ respectively).    
If we now tried to turn the first property above into a rule, such as:

\begin{center}
  \AxiomC{$\tau \in \tau_i$}
  \LeftLabel{$(prop'\ 1)$}
  \UnaryInfC{$\tau \subseteq \tau_i$}
  \DisplayProof
\end{center}

Where $\tau$ is a strict type and $\tau_i$ is an intersection, we would immediately get an error because the type signature of $\subseteq$ (does not include type refinement) is:

~~~{.agda}
data _⊆_ : IType -> IType -> Set
~~~

In order to get a well typed version of this rule, we would have to write something like:

\begin{center}
  \AxiomC{$\tau \in \tau_i$}
  \LeftLabel{$(prop'\ 1)$}
  \UnaryInfC{$[\tau] \subseteq_\ell \tau_i$}
  \DisplayProof
\end{center}

Similarly for the second property, the well typed version might be formulated as:

\begin{center}
  \AxiomC{$\forall \tau' \in \tau_i.\ [\tau'] \subseteq_\ell \tau$}
  \LeftLabel{$(prop'\ 2)$}
  \UnaryInfC{$\tau_i \subseteq_\ell \tau$}
  \DisplayProof
\end{center}

However, in the rule above, we assumed/forced $\tau$ to be an intersection, yet the property does not enforce this, and thus the two rules above do not actually capture the two properties from \cref{Definition:subseteqOrig}. 

<div class="Example">
For example, take the two intersection types $((\psi \cap \tau) \to \psi) \cap ((\psi \cap \tau \cap \rho) \to \psi)$ and $(\psi \cap \tau) \to \psi$. According to the original definition, we will have: 

\begin{center}
  \AxiomC{}
  \LeftLabel{$(refl)$}
  \UnaryInfC{$(\psi \cap \hdots$}

  \AxiomC{}
  \LeftLabel{$(prop\ 1)$}
  \UnaryInfC{$\psi \subseteq \psi \cap \tau \cap \rho$}
  \AxiomC{}
  \LeftLabel{$(prop\ 1)$}
  \UnaryInfC{$\tau \subseteq \psi \cap \tau \cap \rho$}
  \LeftLabel{$(prop\ 2)$}
  \BinaryInfC{$\psi \cap \tau \subseteq \psi \cap \tau \cap \rho$}
  \AxiomC{}
  \LeftLabel{$(refl)$}
  \UnaryInfC{$\psi \subseteq \psi$}
  \LeftLabel{$(prop\ 3)$}
  \BinaryInfC{$(\psi \cap \tau \cap \rho) \to \psi \subseteq (\psi \cap \tau) \to \psi$}
  \LeftLabel{$(prop\ 2)$}
  \BinaryInfC{$((\psi \cap \tau) \to \psi) \cap ((\psi \cap \tau \cap \rho) \to \psi) \subseteq (\psi \cap \tau) \to \psi$}
  \DisplayProof
\end{center}

When we try to prove the above using the well typed rules, we first need to coerce $(\psi \cap \tau) \to \psi$ into an intersection:

\begin{center}
  \AxiomC{}
  \LeftLabel{$(refl)$}
  \UnaryInfC{$[[\psi , \tau] \to \psi] \subseteq_\ell [[\psi , \tau] \to \psi]$}

  \AxiomC{$[[\psi , \tau , \rho] \to \psi] \subseteq_\ell [[\psi , \tau] \to \psi]$}
  \LeftLabel{$(prop'\ 2)$}
  \BinaryInfC{$[[\psi , \tau] \to \psi, [\psi , \tau , \rho] \to \psi] \subseteq_\ell [[\psi , \tau] \to \psi]$}
  \DisplayProof
\end{center}

The open branch $[[\psi , \tau , \rho] \to \psi] \subseteq_\ell [[\psi , \tau] \to \psi]$ in the example clearly demonstrates that the current formulation of the rules clearly doesn't capture the properties, outlined in \cref{Definition:subseteqOrig}.
</div>

Since we know by reflexivity that $\tau \subseteq \tau$, we can reformulate $(prop'\ 1)$ as:

\begin{center}
  \AxiomC{$\exists \tau' \in \tau_i.\ \tau \subseteq \tau'$}
  \LeftLabel{$(prop'\ 1)$}
  \UnaryInfC{$[\tau] \subseteq_\ell \tau_i$}
  \DisplayProof
\end{center}

Using this rule, we can complete the previously open branch in the example above. Also, since the only rules that can proceed $(prop'\ 2)$ in the derivation tree are $(refl)$ or $(prop'\ 1)$, and it's easy to see that in case of $(refl)$ preceding, we can always apply $(prop'\ 1)$ before $(refl)$, we can in fact merge $(prop'\ 1)$ and $(prop'\ 2)$ into the single rule:

\begin{center}
  \AxiomC{$\forall \tau' \in \tau_i.\ \exists \tau'' \in \tau.\ \tau' \subseteq \tau''$}
  \LeftLabel{$(prop'\ 12)$}
  \UnaryInfC{$\tau_i \subseteq_\ell \tau$}
  \DisplayProof
\end{center}
