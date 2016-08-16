#Intersection types
\label{chap:itypes}

Having compared different mechanizations and implementation languages for the simply typed $\lamy$ calculus in the previous two chapters, we arrived at the "winning" combination of a locally nameless mechanization using Agda. Carrying on in this setting, we present the formalization of intersection types for the $\lamy$ calculus along with the proof of subject invariance for intersection types.   
Whilst the theory formalized so far "only"  includes the basic definitions of intersection type assignment and the proof of subject invariance, these proofs turned out to be significantly more difficult than their simply typed counterparts (e.g. in case of sub-tying and subject reduction lemmas). Indeed the whole formalization of simple types, along with the proof of the Church Rosser theorem, is roughly only 1350 lines of code in Agda, in comparison to about 1890 lines, for the intersection typing together with proofs of subject invariance.   
Even though the proof is not novel, there is, to our knowledge, no known fully formal version of it for the $\lamy$ calculus. The chapter mainly focuses on the engineering choices that were made in order to simplify the proofs as much as possible, as well as the necessary implementation overheads that were necessary for the implementation.    
The chapter is presented in sections, each explaining implementation details that had to be considered and any tweaks to the definitions, presented in \cref{itypesIntro}, that needed to be made. Some of the definitions presented early on in this chapter, thus undergo several revisions, as we discuss the necessities for these changes in a pseudo-chronological manner in which they occurred throughout the mechanization.

##Intersection types in Agda
\label{itypesAgda}

The first implementation detail we had to consider was the implementation of the definition of intersection types themselves. Unlike simple types, the definition of intersection-types is split into two mutually recursive definitions of strict (`IType` $/\mathcal{T}_s$) and intersection (`IType`$_\ell$ $/\mathcal{T}$) types:

~~~{.agda escapeinside=|| xleftmargin=1em linenos=true}
data IType|$_\ell$| : Set
data IType : Set

data IType where
  φ : IType
  _~>_ : (s : IType|$_\ell$|) -> (t : IType) -> IType

data IType|$_\ell$| where
  ∩ : List IType -> IType|$_\ell$|
~~~

The reason why the intersection `IType`$_\ell$ is defined as a list of strict types `IType` in line 9, is due to the (usually) implicit requirement that the types in $\mathcal{T}$ be finite. The decision to use lists as an implementation of fine sets was taken, because the Agda standard library includes a definition of lists with definitions of list membership $\in$ and other associated lemmas, which proved to be useful for definitions of the $\subseteq$ relation on types. 


From the above definition, it is obvious that the split definitions of `IType` and `IType`$_\ell$ are somewhat redundant, in that `IType`$_\ell$ only has one constructor `∩` and therefore, any instance of `IType`$_\ell$ in the definition of `IType` can simply be replaced by `List IType`:

~~~{.agda}
data IType : Set where
  φ : IType
  _~>_ : List IType -> IType -> IType
~~~

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
\label{Definition:subseteqNew}
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

To give a motivation as to why we chose a different formulation of these properties, we first examine the original definition and show why it's not rigorous enough for a well typed Agda definition.   
As we've shown in \cref{itypesAgda}, the definition of intersection types is implicitly split into strict `IType`s and intersections, encoded as `List IType`s. All the preceding definitions follow this split with the strict and non strict versions of the type refinement ($::$ and $::_\ell$ respectively) and sub-typing relations ($\subseteq$ and $\subseteq_\ell$ respectively).    
If we tried to turn the first property above into a rule, such as:

\begin{center}
  \AxiomC{$\tau \in \tau_i$}
  \LeftLabel{$(prop'\ 1)$}
  \UnaryInfC{$\tau \subseteq \tau_i$}
  \DisplayProof
\end{center}

where $\tau$ is a strict type `IType` and $\tau_i$ is an intersection `List IType`, we would immediately get a type error, because the type signature of $\subseteq$ (which does not include type refinement) is:

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
To demonstrate this, take the two intersection types $((\psi \cap \tau) \to \psi) \cap ((\psi \cap \tau \cap \rho) \to \psi)$ and $(\psi \cap \tau) \to \psi$. According to the original definition, we will have: 

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

When we try to prove the above using the well typed rules, we first need to coerce $(\psi \cap \tau) \to \psi$ into an intersection. Then, we try to construct the derivation tree:

\begin{center}
  \AxiomC{}
  \LeftLabel{$(refl)$}
  \UnaryInfC{$[[\psi , \tau] \to \psi] \subseteq_\ell [[\psi , \tau] \to \psi]$}

  \AxiomC{$[[\psi , \tau , \rho] \to \psi] \subseteq_\ell [[\psi , \tau] \to \psi]$}
  \LeftLabel{$(prop'\ 2)$}
  \BinaryInfC{$[[\psi , \tau] \to \psi, [\psi , \tau , \rho] \to \psi] \subseteq_\ell [[\psi , \tau] \to \psi]$}
  \DisplayProof
\end{center}

The open branch $[[\psi , \tau , \rho] \to \psi] \subseteq_\ell [[\psi , \tau] \to \psi]$ in the example clearly demonstrates that the current formulation of the two properties clearly doesn't quite capture the intended **??meaning??**.
</div>

Since we know by reflexivity that $\tau \subseteq \tau$, we can reformulate $(prop'\ 1)$ as:

\begin{center}
  \AxiomC{$\exists \tau' \in \tau_i.\ \tau \subseteq \tau'$}
  \LeftLabel{$(prop''\ 1)$}
  \UnaryInfC{$[\tau] \subseteq_\ell \tau_i$}
  \DisplayProof
\end{center}

Using this rule, we can now complete the previously open branch in the example above:

\begin{center}
  \AxiomC{$\vdots$}

  \AxiomC{}
  \LeftLabel{$(refl)$}
  \UnaryInfC{$\psi \subseteq \psi$}
  \LeftLabel{$(prop''\ 1)$}
  \UnaryInfC{$[\psi] \subseteq_\ell [\psi , \tau , \rho]$}

  \AxiomC{}
  \LeftLabel{$(refl)$}
  \UnaryInfC{$\tau \subseteq \tau$}
  \LeftLabel{$(prop''\ 1)$}
  \UnaryInfC{$[\tau] \subseteq_\ell [\psi , \tau , \rho]$}
  \LeftLabel{$(prop'\ 2)$}
  \BinaryInfC{$[\psi , \tau] \subseteq_\ell [\psi , \tau , \rho]$}
  
  \AxiomC{}
  \LeftLabel{$(refl)$}
  \UnaryInfC{$\psi \subseteq \psi$}
  \LeftLabel{$(arr)$}
  \BinaryInfC{$[\psi , \tau , \rho] \to \psi \subseteq [\psi , \tau] \to \psi$}
  \LeftLabel{$(prop''\ 1)$}
  \UnaryInfC{$[[\psi , \tau , \rho] \to \psi] \subseteq_\ell [[\psi , \tau] \to \psi]$}
  \LeftLabel{$(prop'\ 2)$}
  \BinaryInfC{$[[\psi , \tau] \to \psi, [\psi , \tau , \rho] \to \psi] \subseteq_\ell [[\psi , \tau] \to \psi]$}
  \DisplayProof
\end{center}

Also, since the only rules that can proceed $(prop'\ 2)$ in the derivation tree are $(refl)$ or $(prop'\ 1)$, and it's easy to see that in case of $(refl)$ preceding, we can always apply $(prop'\ 1)$ before $(refl)$, we can in fact merge $(prop'\ 1)$ and $(prop'\ 2)$ into the single rule:

\begin{center}
  \AxiomC{$\forall \tau' \in \tau_i.\ \exists \tau'' \in \tau.\ \tau' \subseteq \tau''$}
  \LeftLabel{$(prop'\ 12)$}
  \UnaryInfC{$\tau_i \subseteq_\ell \tau$}
  \DisplayProof
\end{center}

The final version of this rule, as it appears in \cref{Definition:subseteqNew}, is simply an iterated version, split into the $(nil)$ and $(cons)$ cases, to mirror the constructors of lists, since these rules "operate" with `List IType`. This iterated style of rules was adopted throughout this chapter for all definitions involving `List IType`, wherever possible, since it is more natural to work with, in Agda.

<div class="Example">
To illustrate this, take the following lemma about type refinement:

<div class="Lemma"> The following rule is admissible in the typing refinement relation $::_\ell$:
\begin{center}
  \AxiomC{$\tau_i ::_\ell A$}
  \AxiomC{$\tau_j ::_\ell A$}
  \LeftLabel{$(\ \ \ensuremath{+\!\!\!\!\!\!\!+\,}\ )$}
  \BinaryInfC{$\tau_i \concat \tau_j ::_\ell A$}
  \DisplayProof
\end{center}

<div class="proof">By induction on $\tau_i ::_\ell A$:

- $(nil)$: Therefore $\tau_i \equiv []$ and $[] \concat \tau_j \equiv \tau_j$. Thus $\tau_j ::_\ell A$ holds by assumption.
- $(cons)$: We have $\tau_i \equiv \tau , \tau_s$. Thus we know that $\tau :: A$ and $\tau_s ::_\ell A$. Then, by IH, we have $\tau_s \concat \tau_j ::_\ell A$ and thus:

\begin{center}
  \AxiomC{}
  \LeftLabel{$(assm)$}
  \UnaryInfC{$\tau :: A$}
  \AxiomC{}
  \LeftLabel{$(IH)$}
  \UnaryInfC{$\tau_s \concat \tau_j ::_\ell A$}
  \LeftLabel{$(cons)$}
  \BinaryInfC{$\tau , \tau_s \concat \tau_j ::_\ell A$}
\DisplayProof
\end{center}
</div>
</div>

For comparison, the same proof in Agda reads much the same as the "paper" one, given above: 

~~~{.agda escapeinside=||}
++-∷'|$_\ell$| : ∀ {A τ|$_\texttt{i}$| τ|$_\texttt{j}$|} -> τ|$_\texttt{i}$| ∷'|$_\ell$| A -> τ|$_\texttt{j}$| ∷'|$_\ell$| A -> (τ|$_\texttt{i}$| ++ τ|$_\texttt{j}$|) ∷'|$_\ell$| A
++-∷'|$_\ell$| nil τ|$_\texttt{j}$|∷'A = τ|$_\texttt{j}$|∷'A
++-∷'|$_\ell$| (cons τ∷'A τ|$_\texttt{s}$|∷'A) τ|$_\texttt{j}$|∷'A = cons τ∷'A (++-∷'|$_\ell$| τ|$_\texttt{s}$|∷'A τ|$_\texttt{j}$|∷'A)
~~~
</div>

##Intersection-type assignment

Having modified the initial definition of sub-typing and added the notion of type refinement, we now take a look at the definition of intersection type assignment and the modifications that were needed for the mechanization.

Whilst before, intersection typing consisted of the triple $\Gamma \Vdash M : \tau)$, where $\Gamma$ was the intersection type context, $M$ was an untyped $\lamy$ term and $\tau$ was an intersection type, this information is not actually sufficient when we introduce type refinement. As we've shown with the $(Y)$ rule, the refinement relation $::$ provides a connection between intersection and simple types. We therefore want $M$ in the triple to be a simply typed $\lamy$ term.   
Even though, we could use the definition of simple types from the previous chapters, this notation would be rather cumbersome. 

<div class="Example">Consider the simply typed term $\{\} \vdash \lambda x.x : A \to A$ being substituted for the untyped $\lambda x.x$ in $\{\} \Vdash \lambda x.x : (\tau \cap \phi) \leadsto \phi$ (where $\tau :: A$ and $\phi :: A$):

\begin{center}
$\{\} \Vdash (\{\} \vdash \lambda x.x : A \to A) : (\tau \cap \phi) \leadsto \phi$
\end{center}

Already, this simple example demonstrates the clutter of using _Curry_-style simple types in conjunction with the intersection typing.
</div>

Instead of using the _a la Curry_ simple typing, presented in the example above, we chose to define typed $\lamy$ terms _a la Church_. However, since we are using the Locally Nameless representation of binders, we actually give the definition of simply typed pre-terms: 

<div class="Definition" head="Simply typed pre-terms a la Church">
For every simple type $A$, the set of simply typed pre-terms $\Lambda_A$ is inductively defined in the following way:

\begin{center}
  \AxiomC{}
  \LeftLabel{$(fv)$}
  \UnaryInfC{$x \in \Lambda_A$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{}
  \LeftLabel{$(bv)$}
  \UnaryInfC{$n \in \Lambda_A$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$s \in \Lambda_{B \to A}$}
  \AxiomC{$t \in \Lambda_B$}
  \LeftLabel{$(app)$}
  \BinaryInfC{$st \in \Lambda_A$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$s \in \Lambda_B$}
  \LeftLabel{$(lam)$}
  \UnaryInfC{$\lambda_A.s \in \Lambda_{A \to B}$}
  \DisplayProof
  \vskip 1.5em
  \AxiomC{}
  \LeftLabel{$(Y)$}
  \UnaryInfC{$Y_A \in \Lambda_{(A \to A) \to A}$}
  \DisplayProof
\end{center}

</div>

It's easy to see that the definition of Church-style simply typed $\lamy$ pre-terms differs form the untyped pre-terms only in the $\lambda$ case, with the addition of the extra typing information, much like in the case of $Y$. We also adopt a typing convention, where we write $M_{\{A\}}$ to mean $M \in \Lambda_A$.    

The next hurdle we faced in defining the intersection typing relation was the formulation of the $(Y)$ rule. The intuition behind this rule is to type a $Y_A$ constant with a type $\tau$ s.t. $\tau :: (A \to A) \to A$. If we used the $\lambda_\cap^{BCD}$ types (introduced in \cref{itypesIntro}), we could easily have $\tau \equiv (\taui \leadsto \taui) \leadsto \taui$, where $\taui :: A$. However, as we have restricted ourselves to strict-intersection types, the initial definition for the $(Y)$ rule was the somewhat cumbersome:

\begin{center}
  \vskip 1.5em
  \AxiomC{$\taui :: \sigma$}
  \LeftLabel{$(Y)$}
  \RightLabel{$(j \in \underline{n})$}
  \UnaryInfC{$\Gamma \Vdash Y_\sigma : (\taui \leadsto \tau_1 \cap\hdots\cap \taui \leadsto \tau_i) \leadsto \tau_j$}
  \DisplayProof
  \vskip 1.5em
\end{center}

The implementation of this rule clearly demonstrates the complexity, which made it difficult to reason with in proofs: 

~~~{.agda escapeinside=||}
Y :    ∀ {Γ A τ|$_\texttt{i}$| τ} -> (τ|$_\texttt{i}$|∷A : τ|$_\texttt{i}$| ∷'|$_\ell$| A) -> (τ∈τ|$_\texttt{i}$| : τ ∈ τ|$_\texttt{i}$|) ->
    ----------------------------------------------------------
    Γ ⊩ Y A ∶ (∩ (Data.List.map (λ τ|$_\texttt{k}$| -> (∩ τ|$_\texttt{i}$| ~> τ|$_\texttt{k}$|)) τ|$_\texttt{i}$|) ~> τ)
~~~

Even though Agda's main strength is its the powerful pattern matching, it was quickly realized that pattern matching on the type `(∩ (Data.List.map (λ τ\textsubscript{k} -> (∩ τ\textsubscript{i} \textasciitilde > τ\textsubscript{k})) τ\textsubscript{i}) \textasciitilde > τ)` is difficult due to the map function, which appears inside the definition.    
Several modifications were made to the rule, until we arrived at it's current form. To create a compromise between the unrestricted intersection-types of $\lambda_\cap^{BCD}$, which made expressing the $(Y)$ rule much simpler, and the strict typing, which provided a restricted version of type derivation over the $\lambda_\cap^{BCD}$ system, we modified strict types to include intersections on both the left and right sub-terms of a strict type:

<div class="Definition" head="Semi-strict intersection types">
\begin{center}
$\begin{aligned}
\mathcal{T}_s &::= \phi\ |\ (\mathcal{T}_s \cap\hdots\cap \mathcal{T}_s) \leadsto (\mathcal{T}_s \cap\hdots\cap \mathcal{T}_s) \\ 
\end{aligned}$
\end{center}
</div>
 
$\ $
<div class="Remark">Using strict intersection types and having two intersection typing relations $\Vdash$ and $\Vdash_\ell$ makes proving lemmas about the system much easier. The clearest example of this is the nice property of _inversion_, one gets "for free" with strict types. Take, for example, the term $\Gamma \Vdash uv : \tau$ (where for the puproses of this example, $uv$ is a term of the simply-typed $\lambda$-calculus and not a $\lamy$ term). Since for the $\Vdash$ relation, $uv$ can only be given a strict intersection type, we can easily prove the following inversion lemma:

<div class="Lemma" head="Inversion Lemma for $(app)$">
\label{Lemma:invApp}
In the following lemma, $\tau_i$ is an intersection, i.e. a list of strict intersection types $\mathcal{T}_s$:

\begin{center}
$\Gamma \Vdash uv : \tau \iff \exists \tau_i.\ \Gamma \Vdash u : \tau_i \leadsto \tau \land \Gamma \Vdash_\ell v : \tau_i$
\end{center}
</div>


Such a lemma is in fact not even needed in Agda, since the shape of the term $uv$ and the type $\tau$ uniquely determine that the derivation tree must have had an application of the $(app)$ rule at its base. In an Agda proof, such as:

~~~{.agda}
sample-lemma Γ⊩uv∶τ = ?
~~~

One can perform a case analysis on the variable `Γ⊩uv∶τ` (the type of which is `Γ ⊩ app u v ∶ τ`) and obtain:

~~~{.agda escapeinside=||}
sample-lemma (app Γ⊩u∶τ|$_\texttt{i}$|~>τ Γ⊩v∶τ|$_\texttt{i}$|) = ?
~~~

In the $\lambda_\cap^{BCD}$ system (or similar), such an inversion lemma would be a lot more complicated and might look something like:

\begin{center}
$\begin{aligned}
\Gamma \Vdash uv : \tau \iff &\exists k \geq 1.\ \exists \tau_1,\hdots,\tau_k,\psi_1,\hdots,\psi_k.\\
&\tau \subseteq \psi_1 \cap \hdots \cap \psi_k \land\\
&\forall i \in \{1,\hdots,k\}.\ \Gamma \Vdash u : \tau_i \leadsto \psi_i \land \Gamma \Vdash v : \tau_i
\end{aligned}$
\end{center}

The semi-strict typing loses some of the advantages of the strict types, as we will later modify the typing relation, losing the "free" _inversion_ properties that we currently have, i.e. for a given term $uv$, \cref{Lemma:invApp} won't be trivial any more. However, the complexity of the inversion lemmas for semi-strict typing is still lower than that of the unrestricted intersection-typing systems.
</div>

The final version of the $(Y)$ rule, along with the other modified rules of the typing relation are presented below:

<div class="Definition" head="Intersection-type assignment">This definition assumes that the typing context $\Gamma$, which is a list of triples $(x, \tau_i, A)$, is well formed. For each triple, written as $x : \tau_i ::_\ell A$, this means that the free variable $x$ does not appear elsewhere in the domain of $\Gamma$. Each intersection type $\tau_i$, associated with a variable $x$, also refines a simple type $A$. In the definition below, we also assume the following convention $\bigcap \tau \equiv [\tau]$:
\label{Definition:itypAssignment}
\begin{center}
  \AxiomC{$\exists (x : \tau_i ::_\ell A) \in \Gamma.\ \bigcap \tau \subseteq^A_\ell \tau_i$}
  \LeftLabel{$(var)$}
  \UnaryInfC{$\Gamma \Vdash x_{\{A\}} : \tau$}
  \DisplayProof
  %------------------------------------
  \vskip 1.5em
  \AxiomC{$\Gamma \Vdash u_{\{A \to B\}} : \tau_i \leadsto \tau_j$}
  \AxiomC{$\Gamma \Vdash_\ell v_{\{A\}} : \tau_i$}
  \LeftLabel{$(app)$}
  \RightLabel{$(\bigcap \tau \subseteq^B_\ell \tau_j)$}
  \BinaryInfC{$\Gamma \Vdash uv : \tau$}
  \DisplayProof
  %------------------------------------
  \vskip 1.5em
  \AxiomC{$\forall x \not\in L.\ (x : \tau_i ::_\ell A),\Gamma \Vdash_\ell m^x : \tau_j$}
  \LeftLabel{$(abs)$}
  \UnaryInfC{$\Gamma \Vdash \lambda_A.m : \tau_i \leadsto \tau_j$}
  \DisplayProof
  %------------------------------------
  \hskip 1.5em
  \AxiomC{$\exists \tau_x.\ \bigcap (\tau_x \leadsto \tau_x) \subseteq^{A \to A}_\ell \tau_i \land \tau_j \subseteq^A_\ell \tau_x$}
  \LeftLabel{$(Y)$}
  \UnaryInfC{$\Gamma \Vdash_s Y_{A} : \tau_i \leadsto \tau_j$}
  \DisplayProof
  %------------------------------------
  \vskip 1.5em
  \AxiomC{}
  \LeftLabel{$(nil)$}
  \UnaryInfC{$\Gamma \Vdash_\ell m : \omega$}
  \DisplayProof
  %------------------------------------
  \hskip 1.5em
  \AxiomC{$\Gamma \Vdash m : \tau$}
  \AxiomC{$\Gamma \Vdash_\ell m : \tau_i$}
  \LeftLabel{$(cons)$}
  \BinaryInfC{$\Gamma \Vdash_\ell m : \tau , \tau_i$}
  \DisplayProof
  \vskip 1.5em
\end{center}
</div>

##Proof of subject expansion

An interesting property of the intersection types is the fact that they admit both subject expansion and subject reduction, namely $\Vdash$ is closed under $\beta$-equality. In this section, we will focus on the subject expansion lemma:

<div class="Theorem" head="Subject expansion for $\Vdash/\Vdash_\ell$">

i)    $\Gamma \Vdash m : \tau \implies m \red m' \implies \Gamma \Vdash m' : \tau$
ii)   $\Gamma \Vdash_\ell m : \tau_i \implies m \red m' \implies \Gamma \Vdash_\ell m' : \tau_i$
</div>

The proof of this theorem follows by induction on the $\beta$-reduction $m \red m'$. We will focus on the $(Y)$ reduction rule and show that given a well typed term $\Gamma \Vdash m(Y_\sigma m) : \tau$, s.t. $Y_\sigma m \red m(Y_\sigma m)$, we can also type $Y_\sigma m$ with the same intersection type $\tau$.    
We will start with a very high-level overview of the proof. Having assumed, $\Gamma \Vdash m(Y_\sigma m) : \tau$, we must necessarily have the following derivation tree for the intersection typing relation $\Vdash$:

\begin{figure}[h]
\begin{center}
  \vskip 1em
  \AxiomC{$\vdots$}
  \UnaryInfC{$\Gamma \Vdash_s m : \tau_i \leadsto \tau_j$}
  \AxiomC{$\vdots$}
  \UnaryInfC{$\Gamma \Vdash_\ell Y_A m : \tau_i$}
  \LeftLabel{$(app)$}
  \RightLabel{$([\tau] \subseteq^A_\ell \tau_j)$}
  \BinaryInfC{$\Gamma \Vdash m(Y_{A} m) : \tau$}
  \DisplayProof
  \vskip 1em
\end{center}
\caption{Analysis of the shape of the derivation tree for $\Gamma \Vdash m(Y_{A} m) : \tau$}
\label{figure:shapemYm}
\end{figure}

We have two cases, where $\tau_i$ is an empty intersection $\tau_i \equiv \omega$ or a non-empty list of strict intersection types $\tau_i \equiv [\tau_1,\hdots,\tau_n]$.

###$\tau_i \equiv \omega$

From \cref{figure:shapemYm} above, we have $(1): \Gamma \Vdash_s m : \omega \leadsto \tau_j$. Then, we can construct the following proof tree:

\begin{center}
  \AxiomC{$[[\tau] \leadsto [\tau]] \subseteq^{A \to A}_\ell [\omega \leadsto [\tau]] \land [\tau] \subseteq^A_\ell [\tau]$}
  \LeftLabel{$(Y)$}
  \UnaryInfC{$\Gamma \Vdash Y : [\omega \leadsto [\tau]] \leadsto [\tau]$}

  \AxiomC{$\Gamma \Vdash m : \omega \leadsto [\tau]$}
  \AxiomC{}
  \LeftLabel{$(nil)$}
  \UnaryInfC{$\Gamma \Vdash_\ell m : \omega$}
  \LeftLabel{$(cons)$}
  \BinaryInfC{$\Gamma \Vdash_\ell m : [\omega \leadsto [\tau]]$}
  \LeftLabel{$(app)$}
  \BinaryInfC{$\Gamma \Vdash Y_{A} m : \tau$}
  \DisplayProof
  \vskip 1em
\end{center}

The only (non-trivial) open branch in the above tree is to show that $\Gamma \Vdash m : \omega \leadsto [\tau]$. In order to do so, we need to use the sub-typing lemma for intersection types:

<div class="Lemma" head="Sub-typing for $\Vdash/\Vdash_\ell$">
In the definition below, the binary relation $\subseteq_\Gamma$ is defined for any well-formed contexts $\Gamma$ and $\Gamma'$, where for each triple $(x : \tau_i ::_\ell A) \in \Gamma$, there is a corresponding triple $(x : \tau_j ::_\ell A) \in \Gamma'$ s.t. $\tau_i \subseteq^A_\ell \tau_j\ $:

\begin{center}
  \vskip 1em
  \AxiomC{$\Gamma \Vdash m_{\{A\}} : \tau$}
  \LeftLabel{$(\subseteq)$}
  \RightLabel{$(\Gamma \subseteq_\Gamma \Gamma', \tau' \subseteq^A \tau)$}
  \UnaryInfC{$\Gamma' \Vdash m_{\{A\}} : \tau'$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\Gamma \Vdash_\ell m_{\{A\}} : \tau_i$}
  \LeftLabel{$(\subseteq_\ell)$}
  \RightLabel{$(\Gamma \subseteq_\Gamma \Gamma', \tau_j \subseteq^A_\ell \tau_i)$}
  \UnaryInfC{$\Gamma' \Vdash_\ell m_{\{A\}} : \tau_j$}
  \DisplayProof
  \vskip 1em
\end{center}
<div class="proof">Ommited.</div>
</div>

Thus, we have:

\begin{center}
  \AxiomC{}
  \LeftLabel{$(1)$}
  \UnaryInfC{$\Gamma \Vdash m : \omega \leadsto \tau_j$}
  \LeftLabel{$(\subseteq)$}
  \RightLabel{$(\Gamma \subseteq_\Gamma \Gamma, \omega \leadsto [\tau] \subseteq^{A \to A} \omega \leadsto \tau_j)$}
  \UnaryInfC{$\Gamma \Vdash m : \omega \leadsto [\tau]$}
  \DisplayProof
  \vskip 1em
\end{center}

###$\tau_i \equiv [\tau_1,\hdots,\tau_n]$

This case of the proof is a lot more involved and required several additional rules and lemmas. We will outline the main ideas of the proof in this section.   
$\ $
<div class="Remark">
The first thing to note is that since $\tau_i$ is a non-empty list of semi-strict intersection types, it will have the shape:

\begin{center}
  \AxiomC{$\vdots$}
  \UnaryInfC{$\Gamma \Vdash Y_A m : \tau_1$}

  \AxiomC{$\vdots$}
  \UnaryInfC{$\Gamma \Vdash Y_A m : \tau_2$}

  \AxiomC{$\vdots$}
  \UnaryInfC{$\Gamma \Vdash Y_A m : \tau_n$}

  \AxiomC{}
  \LeftLabel{$(nil)$}
  \UnaryInfC{$\Gamma \Vdash_\ell Y_A m : \omega$}
  \BinaryInfC{$\Gamma \Vdash_\ell Y_A m : [\tau_n]$}
  \UnaryInfC{$\vdots$} 
  \LeftLabel{$(cons)$}
  \BinaryInfC{$\Gamma \Vdash_\ell Y_A m : [\tau_2,\hdots,\tau_n]$}
  \LeftLabel{$(cons)$}
  \BinaryInfC{$\Gamma \Vdash_\ell Y_A m : \tau_i$}
  \DisplayProof
  \vskip 1em
\end{center}

We will simplify this notation slightly and just write:

\begin{center}
  \AxiomC{$\vdots$}
  \UnaryInfC{$\Gamma \Vdash Y_A m : \tau_1$}

  \AxiomC{$\vdots$}
  \UnaryInfC{$\Gamma \Vdash Y_A m : \tau_2$}

  \AxiomC{$\hdots$}

  \AxiomC{$\vdots$}
  \UnaryInfC{$\Gamma \Vdash Y_A m : \tau_n$}

  \QuaternaryInfC{$\Gamma \Vdash_\ell Y_A m : \tau_i$}
  \DisplayProof
  \vskip 1em
\end{center}
</div>

In order to type $Y_A m$ with $\tau$, we first have to show that for every tree above, we can find a type $\tau'_k$ s.t. $\Gamma \Vdash m : \tau'_k \leadsto \tau'_k$ and $[\tau_k] \subseteq^A_\ell \tau'_k$:

<div class="Lemma">
$\Gamma \Vdash Y_A m : \tau \implies \exists \tau'.\ \Gamma \Vdash_\ell m : [\tau' \leadsto \tau'] \land [\tau] \subseteq^A_\ell \tau'$

<div class="proof">
\label{Lemma:Ymax}
Unfolding the typing tree of $\Gamma \Vdash Y_A m : \tau$, we have:

\begin{center}
  \AxiomC{$[\tau_x \leadsto \tau_x] \subseteq^{A \to A} \tau_i \land \tau_j \subseteq^A \tau_x$}
  \UnaryInfC{$\Gamma \Vdash_s Y_A : \tau_i \leadsto \tau_j$}
  \AxiomC{$\Gamma \Vdash_\ell m : \tau_i$}
  \LeftLabel{$(app)$}
  \RightLabel{$([\tau] \subseteq^A_\ell \tau_j)$}
  \BinaryInfC{$\Gamma \Vdash Y_A m : \tau$}
  \DisplayProof
  \vskip 1em
\end{center}

Then it follows by transitivity, that $[\tau] \subseteq^A_\ell \tau_x$, and $\Gamma \Vdash_\ell m : [\tau_x \leadsto \tau_x]$ by sub-typing:

\begin{center}
  \vskip 1em
  \AxiomC{$\Gamma \Vdash_\ell m : \tau_i$}
  \LeftLabel{$(\subseteq_\ell)$}
  \RightLabel{$(\Gamma \subseteq_\Gamma \Gamma, [\tau_x \leadsto \tau_x] \subseteq^{A \to A}_\ell \tau_i)$}
  \UnaryInfC{$\Gamma \Vdash_\ell m : [\tau_x \leadsto \tau_x]$}
  \DisplayProof
  \hskip 1em
  \AxiomC{$[\tau] \subseteq^A_\ell \tau_j$}
  \AxiomC{$\tau_j \subseteq^A_\ell \tau_x$}
  \LeftLabel{$(trans)$}
  \BinaryInfC{$[\tau] \subseteq^A_\ell \tau_x$}
  \DisplayProof
\end{center}
</div>
</div>

Since for every type $\tau_k \in \tau_i$ we now have $\Gamma \Vdash_\ell m : [\tau'_k \leadsto \tau'_k]$ as well as $[\tau_k] \subseteq^A_\ell \tau'_k$, we want to "mege" all these types given to $m$:

\begin{center}
  \vskip 1em
  \AxiomC{$\Gamma \Vdash Y_A m : \tau_1$}
  \LeftLabel{(\cref{Lemma:Ymax})}
  \UnaryInfC{$\Gamma \Vdash_\ell m : [\tau'_1 \leadsto \tau'_1]$}

  \AxiomC{$\hdots$}

  \AxiomC{$\Gamma \Vdash Y_A m : \tau_n$}
  \LeftLabel{(\cref{Lemma:Ymax})}
  \UnaryInfC{$\Gamma \Vdash_\ell m : [\tau'_n \leadsto \tau'_n]$}

  \LeftLabel{(???)}
  \TrinaryInfC{$\Gamma \Vdash m : \tau'_1\concat\hdots\concat\tau'_n \leadsto \tau'_1\concat\hdots\concat\tau'_n$}
  \DisplayProof
  \vskip 1em
\end{center}

such that we have $\tau'_i \equiv \tau'_1 \concat \hdots \concat \tau'_n$ where $\tau_i \subseteq^A_\ell \tau'_i$.

To illustrate how to prove the last step in the tree above (i.e. how to derive the (???) rule), we will look at a simpler example, where $\tau_i \equiv [\tau_1, \tau_2]$. Thus, we want to show:

\begin{center}
  \vskip 1em
  \AxiomC{$\Gamma \Vdash Y_A m : \tau_1$}
  \LeftLabel{(\cref{Lemma:Ymax})}
  \UnaryInfC{$\Gamma \Vdash_\ell m : [\tau'_1 \leadsto \tau'_1]$}

  \AxiomC{$\Gamma \Vdash Y_A m : \tau_2$}
  \LeftLabel{(\cref{Lemma:Ymax})}
  \UnaryInfC{$\Gamma \Vdash_\ell m : [\tau'_2 \leadsto \tau'_2]$}

  \BinaryInfC{$\Gamma \Vdash m : \tau'_1\concat\tau'_2 \leadsto \tau'_1\concat\tau'_2$}
  \DisplayProof
  \vskip 1em
\end{center}

Using the sub-typing lemma we can show:

\begin{center}
  \vskip 1em
  \AxiomC{$\Gamma \Vdash_\ell m : [\tau'_1 \leadsto \tau'_1]$}
  \LeftLabel{$(\subseteq_\ell)$}
  \RightLabel{$([\tau'_1\concat\tau'_2 \leadsto \tau'_1] \subseteq^{A \to A}_\ell [\tau'_1 \leadsto \tau'_1])$}
  \UnaryInfC{$\Gamma \Vdash_\ell m : [\tau'_1\concat\tau'_2 \leadsto \tau'_1]$}
  \DisplayProof
  \vskip 1em
\end{center}

since we have:

\begin{center}
  \AxiomC{}
  \LeftLabel{$(\subseteq^*)$\footnotemark}
  \UnaryInfC{$\tau'_1 \subseteq^A \tau'_1\concat\tau'_2$}
  \AxiomC{}
  \LeftLabel{$(refl)$}
  \UnaryInfC{$\tau'_1 \subseteq^A \tau'_1$}
  \BinaryInfC{$\tau'_1\concat\tau'_2 \leadsto \tau'_1 \subseteq^{A \to A} \tau'_1 \leadsto \tau'_1$}
  
  \AxiomC{}
  \LeftLabel{$(nil)$}
  \UnaryInfC{$\omega \subseteq^{A \to A}_\ell [\tau'_1 \leadsto \tau'_1]$}
  \LeftLabel{$(cons)$}
  \BinaryInfC{$[\tau'_1\concat\tau'_2 \leadsto \tau'_1] \subseteq^{A \to A}_\ell [\tau'_1 \leadsto \tau'_1]$}
  \DisplayProof
  \vskip 1em
\end{center}

\footnotetext{This is a derived rule defined for the subset relation on lists, i.e. if the list $\tau_k$ is a subset of $\tau_n$, then it is also a subtype of $\tau_n$. Th derivation of this rule trivially follows from the $(refl)$, $(nil)$ and $(cons)$ rules.}

Similarly, we can also prove $\Gamma \Vdash_\ell m : [\tau'_1\concat\tau'_2 \leadsto \tau'_2]$, but at this point there is no way we can merge these two types, to produce $\Gamma \Vdash_\ell m : [\tau'_1\concat\tau'_2 \leadsto \tau'_1\concat\tau'_2]$.   
In order to proceed, we had to introduce a new rule to the typing relation $\Vdash$, to allow us to derive the type above:

\begin{center}
  \AxiomC{$\Gamma \Vdash m_{\{A \to B\}} : \tau_i \leadsto \tau_j$}
  \AxiomC{$\Gamma \Vdash m_{\{A \to B\}} : \tau_i \leadsto \tau_k$}
  \LeftLabel{$(\tocap)$}
  \RightLabel{$(\tau_{jk} \subseteq^B \tau_j \concat \tau_k)$}
  \BinaryInfC{$\Gamma \Vdash m_{\{A \to B\}} : \tau_i \leadsto \tau_{jk}$}
  \DisplayProof
  \vskip 1em
\end{center}

Introducing this rule created a host of complications, the chief of which was the fact that we lost our "free" inversion lemmas, as it is now no longer obvious from the shape of the term, which rule was used last in the type derivation tree.

<div class="Example">
Consider a term $\lambda_A. m$ s.t. $\Gamma \Vdash \lambda_A. m : \tau$. Since $\tau$ must necessarily be of the shape $\psi_i \leadsto \psi_j$, either of these two derivation trees could be valid:

\begin{center}
  \vskip 1em
  \AxiomC{$\vdots$}
  \UnaryInfC{$\forall x \not\in L.\ (x : \psi_i ::_\ell A),\Gamma \Vdash_\ell (m^x)_{\{B\}} : \psi_j$}
  \LeftLabel{$(abs)$}
  \UnaryInfC{$\Gamma \Vdash (\lambda_A. m)_{\{A \to B\}} : \psi_i \leadsto \psi_j$}
  \DisplayProof
  \vskip 1.5em
  \AxiomC{$\vdots$}
  \UnaryInfC{$\Gamma \Vdash_s (\lambda_A. m)_{\{A \to B\}} : \psi_i \leadsto \tau_j$}
  \AxiomC{$\vdots$}
  \UnaryInfC{$\Gamma \Vdash_s (\lambda_A. m)_{\{A \to B\}} : \psi_i \leadsto \tau_k$}
  \LeftLabel{$(\tocap)$}
  \RightLabel{$(\psi_j \subseteq^B \tau_j \concat \tau_k)$}
  \BinaryInfC{$\Gamma \Vdash_s (\lambda_A. m)_{\{A \to B\}} : \psi_i \leadsto \psi_j$}
  \DisplayProof
  \vskip 1em
\end{center}

However, it's easy to see that since these derivation trees must be finite, if we apply $(\tocap)$ multiple times, eventually, all of the branches will have to have an application of the $(abs)$ rule.
</div>

Besides having to derive inversion lemmas for the $(abs)$ and $(Y)$ rules, another derived rule, namely the sub-typing rule, breaks. In order to fix this rule, we also had to add an axiom scheme corresponding to the $(\tocap)$ rule, to the definition of the type subset relation:

\begin{center}
  \vskip 1em
  \AxiomC{$[\tau_i \leadsto (\tau_j \concat \tau_k)] \concat \tau_m ::_\ell A \to B$}
  \LeftLabel{$(\tocap_\ell)$}
  \UnaryInfC{$[\tau_i \leadsto (\tau_j \concat \tau_k)] \concat \tau_m \subseteq^{A \to B}_\ell [\tau_i \leadsto \tau_j ,\ \tau_i \leadsto \tau_k] \concat \tau_m$}
  \DisplayProof
  \vskip 1em
\end{center}

$\ $
<div class="Remark">Initially, we tried to simply add $(\tocap_\ell)$ to the type subset relation and add the sub-typing rule to $\Vdash$, instead of having the rule $(\tocap)$. However, this made the inversion lemmas, as well as some other lemmas too difficult to prove. Finding the right balance in the formalization of the $(\tocap)/(\tocap_\ell)$ and the sub-typing rules proved to be perhaps the most challenging part of the formalization of intersection types.</div>

We can now finish or proof for the case where $\tau_i \equiv [\tau_1, \tau_2]$:

\begin{center}
  \AxiomC{$\Gamma \Vdash Y_A m : \tau_1$}
  \LeftLabel{(\cref{Lemma:Ymax})}
  \UnaryInfC{$\Gamma \Vdash_\ell m : [\tau'_1 \leadsto \tau'_1]$}
  \LeftLabel{$(\subseteq_\ell)$}
  \UnaryInfC{$\Gamma \Vdash_\ell m : [\tau'_1\concat\tau'_2 \leadsto \tau'_1]$}
  \LeftLabel{$(\in_\ell)$\footnotemark}
  \UnaryInfC{$\Gamma \Vdash m : \tau'_1\concat\tau'_2 \leadsto \tau'_1$}

  \AxiomC{$\Gamma \Vdash Y_A m : \tau_2$}
  \LeftLabel{(\cref{Lemma:Ymax})}
  \UnaryInfC{$\Gamma \Vdash_\ell m : [\tau'_2 \leadsto \tau'_2]$}
  \LeftLabel{$(\subseteq_\ell)$}
  \UnaryInfC{$\Gamma \Vdash_\ell m : [\tau'_1\concat\tau'_2 \leadsto \tau'_2]$}
  \LeftLabel{$(\in_\ell)$}
  \UnaryInfC{$\Gamma \Vdash m : \tau'_1\concat\tau'_2 \leadsto \tau'_2$}
  
  \LeftLabel{$(\tocap)$}
  \BinaryInfC{$\Gamma \Vdash m : \tau'_1\concat\tau'_2 \leadsto \tau'_1\concat\tau'_2$}
  \DisplayProof
  \vskip 1em
\end{center}

\footnotetext{The derived rule $(\in_\ell)$ is used to convert between the strict typing relation $\Vdash$ and intersection typing $\Vdash_\ell$ and is stated as: $\Gamma \Vdash_\ell m : \tau_i \land \tau \in \tau_i \implies \Gamma \Vdash m : \tau$}


Having demonstrated the case when $\tau_i \equiv [\tau_1, \tau_2]$, the proof when $\tau_i$ is arbitrarily long proceeds in much the same way:

<div class="Lemma">
\label{Lemma:Ymaxl}
Assuming $\tau_i$ is a non-empty intersection, we have:   
$\Gamma \Vdash_\ell Y_A m : \tau_i \implies \exists \tau'_i.\ \Gamma \Vdash m : \tau'_i \leadsto \tau'_i \land \tau_i \subseteq^A_\ell \tau'_i$
</div>

Using \cref{Lemma:Ymaxl}, we can finally show that $\Gamma \Vdash Y_A m : \tau$.    

\setlength\parindent{-.75mm}
$\begin{aligned}\text{First, from \cref{figure:shapemYm}, we have: }
&(1): \Gamma \Vdash m : \tau_i \leadsto \tau_j \text{ , }\\
&(2): [\tau] \subseteq^A_\ell \tau_j \text{ and }\\
&(3): \Gamma \Vdash_\ell Y_A m : \tau_i.
\end{aligned}$

$\begin{aligned}
\text{Since $\tau_i$ is not empty, from $(3)$ and \cref{Lemma:Ymaxl}, we have some $\tau'_i$ s.t. }
&(4): \Gamma \Vdash m : \tau'_i \leadsto \tau'_i\text{ and }\\
&(5): \tau_i \subseteq^A_\ell \tau'_i.
\end{aligned}$

\setlength\parindent{0mm}

We can therefore derive $\Gamma \Vdash_\ell m : [\tau'_i \leadsto ([\tau] \concat \tau'_i)]$:

\begin{center}
  \AxiomC{}
  \LeftLabel{$(1)$}
  \UnaryInfC{$\Gamma \Vdash m : \tau_i \leadsto \tau_j$}
  \LeftLabel{$(\subseteq)$}
  \RightLabel{$(\tau'_i \leadsto [\tau] \subseteq^{A \to A} \tau_i \leadsto \tau_j)$}
  \UnaryInfC{$\Gamma \Vdash m : \tau'_i \leadsto [\tau]$}
  
  \AxiomC{}
  \LeftLabel{$(4)$}
  \UnaryInfC{$\Gamma \Vdash m : \tau'_i \leadsto \tau'_i$}
  \LeftLabel{$(\tocap)$}
  \BinaryInfC{$\Gamma \Vdash m : \tau'_i \leadsto ([\tau] \concat \tau'_i)$}

  \AxiomC{}
  \LeftLabel{$(nil)$}
  \UnaryInfC{$\Gamma \Vdash_\ell m : \omega$}
  \LeftLabel{$(cons)$}
  \BinaryInfC{$\Gamma \Vdash_\ell m : [\tau'_i \leadsto ([\tau] \concat \tau'_i)]$}
  \DisplayProof
  \vskip 1em
\end{center}
$\ $
<div class="Remark">
In the sub-typing rule, used in the tree above, $\tau'_i \leadsto [\tau] \subseteq^{A \to A} \tau_i \leadsto \tau_j$ follows by:

\begin{center}
  \vskip 1em
  \AxiomC{}
  \LeftLabel{$(5)$}
  \UnaryInfC{$\tau_i \subseteq^A_\ell \tau'_i$}
    
  \AxiomC{}
  \LeftLabel{$(2)$}
  \UnaryInfC{$[\tau] \subseteq^A_\ell \tau_j$}

  \LeftLabel{$(arr)$}
  \BinaryInfC{$(\tau'_i \leadsto [\tau] \subseteq^{A \to A} \tau_i \leadsto \tau_j)$}
  \DisplayProof
  \vskip 1em
\end{center}
</div>

Finally, putting all the pieces together, we get $\Gamma \Vdash Y_{A} m : \tau$:

\begin{center}
  \vskip 1em
  \AxiomC{
    \stackanchor{$[([\tau] \concat \tau'_i) \leadsto ([\tau] \concat \tau'_i)] \subseteq^{A \to A}_\ell [\tau'_i \leadsto ([\tau] \concat \tau'_i)]\ \land$}
    {$[\tau] \subseteq^A_\ell [\tau] \concat \tau'_i$}}
  \LeftLabel{$(Y)$}
  \UnaryInfC{$\Gamma \Vdash Y : [\tau'_i \leadsto ([\tau] \concat \tau'_i)] \leadsto [\tau]$}

  \AxiomC{$\Gamma \Vdash_\ell m : [\tau'_i \leadsto ([\tau] \concat \tau'_i)]$}
  \LeftLabel{$(app)$}
  \BinaryInfC{$\Gamma \Vdash Y_{A} m : \tau$}
  \DisplayProof
  \vskip 1em
\end{center}

##Proofs of termination for the LN representation

This final section of the chapter briefly describes an interesting implementation quirk/overhead, encountered when proving the substitution lemma, which was required for the proofs of both subject expansion and reduction:

<div class="Lemma" head="Substitution lemma">Given that $m$ and $n$ are both well formed terms and $x \not\in \dom\ \Gamma$, we have:
\begin{center}
$\Gamma \Vdash m_{\{A\}}[n_{\{B\}}/x] : \tau \iff \exists \tau_i.\ (x : \tau_i ::_\ell B), \Gamma \Vdash m_{\{A\}} : \tau \land \Gamma \Vdash_\ell n_{\{B\}} : \tau_i$
\end{center}
</div>

In the backwards direction ($\Leftarrow$), this proof is fairly straight forward and follows much like the homonymous lemma for simple types.    
The other direction ($\Rightarrow$), used in the proof of subject expansion, turned out to be more complicated in Agda. This part of the proof proceeds by induction on the well formed term $m$, and whilst trying to prove the goal, when $m$ is a $\lambda$-term, Agda's termination checker would fail. To show why this was the case, we first examine the definition for the $\lambda$-case:

~~~{.agda escapeinside=||}
subst-⊩-2 : ∀ {A B Γ τ x} ->
  {m : Λ A} {n : Λ B} -> 
  ΛTerm m -> ΛTerm n ->
  x ∉ dom Γ -> Γ ⊩ (m Λ[ x ::= n ]) ∶ τ ->
  ∃(λ τ|$_\texttt{i}$| -> ( ((x , τ|$_\texttt{i}$| , B) ∷ Γ) ⊩ m ∶ τ ) × ( Γ ⊩|$_\ell$| n ∶ τ|$_\texttt{i}$| ))
|$\texttt{\vdots}$|
subst-⊩-2 {A ⟶ B} {C} {Γ} {τ ~> τ'} {x} 
  {_} {n} 
  (lam L {m} cf) trm-n 
  x∉Γ (abs L' cf') = ?
~~~

Informally, the (pieces of) definition above can be read as:

- `(lam L {m} cf)` : $m$ is a well formed $\lambda$-term, s.t. we have $\forall x' \not\in L.\ \trm(m^{x'})$ for some finite $L$.   
  (This is captured by the type of `cf`, which is `x₁ ∉ L → ΛTerm (Λ[ 0 >> fv x₁ ] m)`.)
- `trm-n` : $n$ is a well-formed $\lamy$ term
- `(abs L' cf')` : the last rule in the derivation tree of $\Gamma \Vdash \lambda_A.m_{\{B\}}[n_{\{C\}}/x] : \tau \leadsto \tau'$ was the $(abs)$ rule and therefore we have `cf'`, which encodes the premise, that there is some finite $L'$ s.t. $\forall x' \not\in L'.\ (x' : \tau ::_\ell A),\Gamma \Vdash_\ell (m[n/x])^{x'} : \tau$.    

The proof proceeds, by first showing that we can obtain a fresh $x'$ s.t. $\trm(m^{x'})$. By picking a sufficiently fresh $x'$, we can also derive $(x' : \tau ::_\ell A),\Gamma \Vdash_\ell (m^{x'})[n/x] : \tau$, essentially swapping the substitution and opening from the assumption above.   
However, when we then try to apply the induction hypothesis, which corresponds to the following recursive call in Agda, we get an error, claiming that termination checking failed:

~~~{.agda escapeinside=||}
ih' : (x' , τ , A) ∷ Γ ⊩|$_\ell$| (Λ[ 0 >> fv {A} x' ] m) Λ[ x ::= n ] ∶ τ'
ih' = ....

ih : ∃(λ τ|$_\texttt{i}$| ->
  (x , τ|$_\texttt{i}$| , C) ∷ (x' , τ , A) ∷ Γ ⊩|$_\ell$| Λ[ 0 >> fv x' ] m ∶ τ' × 
  (x' , τ , A) ∷ Γ ⊩|$_\ell$| n ∶ τ|$_\texttt{i}$|)
ih = subst-⊩|$_\ell$|-2 (cf (∉-cons-l L _ (∉-∷-elim _ x'∉)))
                trm-n
                (∉-∷ _ (dom Γ) (λ x₂ -> fv-x≠y _ _ x'∉ (sym x₂)) x∉Γ)
                ih'
~~~

In order to see why this happens, we will ignore the explicit arguments passed to `subst-⊩$_\ell$-2` and instead rewrite the snippet above with the implicit arguments:

~~~{.agda escapeinside=||}
ih = subst-⊩|$_\ell$|-2 {A} {C} {(x' , τ , A) ∷ Γ} {τ'} {x} 
  {Λ[ 0 >> fv x' ] m} {n} ...
~~~

Agda's termination checking relies on the fact that the data-types, being pattern matched on, get structurally smaller in recursive calls[^6]. Thus, the parameter `Λ[ 0 >> fv x' ] m` in this definition is obviously problematic, as Agda doesn't know that $m^{x'}$ is structurally smaller than $m$, even though we know that is the case, as the open operation simply replaces a bound variable with a free one. However, whilst $m^{x'}$ is not "bigger" than $m$, it is not structurally smaller than $\lambda.m$ and therefore, structural induction/recursion principles cannot be used in this definition.

[^6]: The details on how the termination checking algorithm in Agda works are sparse, so we are not actually sure about the specifics of how the termination check fails.

Whilst one can suppress termination checking for a specific definition/lemma in Agda, by adding the `\{-\# TERMINATING \#-\}` pragma in front of the definition, it is generally not a good idea to do this, even though we know that the definition is actually terminating. We initially contemplated using well-founded recursion to prove that the proof terminates, but having little experience in Agda, this looked quite complicated.   
Instead, we devised a simple "hack" to allow Agda to prove termination, by first defining "skeleton" terms $T$, which capture the structure of $\lamy$ terms:

<div class="Definition">
$T ::= *\ |\ \circ T\ |\ T\ \amp\ T$
</div>

<div class="Example">
As an illustration, take the LN $\lamy$ term $\lambda.0(Y_A x)$. We can represented this term as a tree (left). Then, we simply replace any $\lambda$ and $Y_\sigma$ with $\circ$, application becomes & and any free or bound variables are represented as * in the skeleton tree (on the right):

\begin{minipage}{.5\textwidth}
\begin{center}
\begin{tikzpicture}[distance=1em,
  every node/.style = {align=center}]]
  \node {$\lambda$}
    child { node {app}
      child { node {0} }
      child { node {app} 
        child { node {$Y_A$} }
        child { node {x} } } };
\end{tikzpicture}
\end{center}
\end{minipage}
\begin{minipage}{.5\textwidth}
\begin{center}
\begin{tikzpicture}[distance=3em,
  every node/.style = {align=center}]]
  \node {$\circ$}
    child { node {$\amp$}
      child { node {*} }
      child { node {$\amp$} 
        child { node {*} }
        child { node {*} } } };
\end{tikzpicture}
\end{center}
\end{minipage}

Thus, the skeleton term of $\lambda.0(Y_A x)$ is $\circ(*\ \amp\ (*\ \amp\ *))$.
</div>

Next, we defined the congruence relation $\sim_T$ between locally nameless $\lamy$ terms and skeleton terms:

<div class="Definition" head="$\sim_T$ relation">
In the following definition, $m,p,q$ range over simply-typed locally nameless $\lamy$ terms and $s,t$ range over skeleton terms $T$:
\begin{center}
  \AxiomC{}
  \LeftLabel{$(bvar)$}
  \UnaryInfC{$n \sim_T *$}
  \DisplayProof
  %------------------------------------
  \hskip 1.5em
  \AxiomC{}
  \LeftLabel{$(fvar)$}
  \UnaryInfC{$x \sim_T *$}
  \DisplayProof
  %------------------------------------
  \hskip 1.5em
  \AxiomC{}
  \LeftLabel{$(Y)$}
  \UnaryInfC{$Y_A \sim_T *$}
  \DisplayProof
  %------------------------------------
  \vskip 1.5em
  \AxiomC{$m \sim_T t$}
  \LeftLabel{$(un)$}
  \UnaryInfC{$\lambda_A.m \sim_T \circ t$}
  \DisplayProof
  %------------------------------------
  \hskip 1.5em
  \AxiomC{$p \sim_T s$}
  \AxiomC{$q \sim_T t$}
  \LeftLabel{$(bin)$}
  \BinaryInfC{$pq \sim_T s\ \amp\ t$}
  \DisplayProof
  \vskip 1.5em
\end{center}
</div>