#Intersection types
\label{chap:itypes}

Having compared different mechanizations and implementation languages for the simply typed $\lamy$ calculus in the previous two chapters, we arrived at the "winning" combination of a locally nameless mechanization using Agda. Carrying on in this setting, in this chapter, we present the formalization of intersection types for the $\lamy$ calculus along with the proof of subject invariance for intersection types.   
Whilst the proof is not novel, there is, to our knowledge, no known of it for the $\lamy$ calculus. The chapter mainly focuses on the engineering choices that were made in order to simplify the proofs as much as possible, as well as the necessary implementation overheads that were necessary for the implementation.    
The chapter is presented in sections, each explaining implementation details that had to be considered and any tweaks to the definitions, presented in \cref{itypesIntro}, that were needed to be made.

##Intersection types in Agda

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

One of the first things we needed to add to the $\subseteq$ relation on intersection types and notion of intersection type assignment was simple-type refinement. The main idea of intersection types for $\lamy$ terms is for the intersection types to somehow "refine" the simple types. Intuitively, this notion should capture the relationship between the "shape" of the intersection and simple types. The refinement relation has been defined in @kobayashi09 (amongst others) and is presented below:

<div class="Definition" head="Intersection type refinement">
Since intersection types are defined in terms of strict ($\mathcal{T}_s$) and non-strict ($\mathcal{T}$) intersection types, the definition of refinement ($::$) is split into two versions, one for strict and another for non-strict types. In the definition below, $\tau$ ranges over strict intersection types $\mathcal{T}_s$, with $\tau_i, \tau_j$ ranging over non-strict intersection types $\mathcal{T}$, and $A, B$ range over simple types $\sigma$:

\begin{center}
  \AxiomC{}
  \LeftLabel{$(base)$}
  \UnaryInfC{$\phi ::_s \mathsf{o}$}
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
  \BinaryInfC{$\tau , \tau_i :: A$}
  \DisplayProof
\end{center}
</div>

Having a notion of type refinement, we then modified the subset relation on intersection types, s.t. $\subseteq$ is defined only for pairs of intersection types, which refine the same simple type:

<div class="Definition" head="$\subseteq^A$">
In the definition below, $\tau, \tau'$ range over $\mathcal{T}_s$, $\tau_i, \hdots, \tau_n$ range over $\mathcal{T}$ and $A, B$ range over $\sigma$:

\begin{center}
  \AxiomC{}
  \LeftLabel{$(base)$}
  \UnaryInfC{$\phi \subseteq^\mathsf{o}_s \phi$}
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
  \BinaryInfC{$\tau , \tau_i \subseteq^A \tau_j$}
  \DisplayProof
  \vskip 1.5em
  \AxiomC{$\tau_i \subseteq^A \tau_j$}
  \AxiomC{$\tau_j \subseteq^A \tau_k$}
  \LeftLabel{$(trans)$}
  \BinaryInfC{$\tau_i \subseteq^A \tau_k$}
  \DisplayProof
  \vskip 1.5em
\end{center}
</div>

##Quantification

There are several differences between the presentation of the $\subseteq$ relation in \cref{Definition:subseteqOrig} and the one above. The main differences arise mainly in