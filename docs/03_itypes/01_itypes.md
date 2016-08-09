#Intersection types
\label{chap:itypes}

Having compared different mechanizations and implementation languages for the simply typed $\lamy$ calculus in the previous two chapters, we arrived at the "winning" combination of a locally nameless mechanization using Agda. Carrying on in this setting, we present the formalization of intersection types for the $\lamy$ calculus along with the proof of subject invariance for intersection types.   
Whilst the proof is not novel, there is, to our knowledge, no known fully formal version of it for the $\lamy$ calculus. The chapter mainly focuses on the engineering choices that were made in order to simplify the proofs as much as possible, as well as the necessary implementation overheads that were necessary for the implementation.    
The chapter is presented in sections, each explaining implementation details that had to be considered and any tweaks to the definitions, presented in \cref{itypesIntro}, that needed to be made. Some of the definitions presented early on in this chapter, thus undergo several revisions, as we discuss the necessities for these changes in a pseudo-chronological manner in which they occurred throughout the mechanization.

##Intersection types in Agda
\label{itypesAgda}

The first implementation detail we had to consider was the implementation of the definition of intersection types themselves. Unlike simple types, the definition of intersection-types is split into two mutually recursive definitions of strict (`IType` $/\mathcal{T}_s$) and intersection (`ITypeI` $/\mathcal{T}$) types:

~~~{.agda xleftmargin=1em linenos=true}
data ITypeI : Set
data IType : Set

data IType where
  φ : IType
  _~>_ : (s : ITypeI) -> (t : IType) -> IType

data ITypeI where
  ∩ : List IType -> ITypeI
~~~

The reason why the intersection `ITypeI` is defined as a list of strict types `IType` in line 9, is due to the (usually) implicit requirement that the types in $\mathcal{T}$ be finite. The decision to use lists as an implementation of fine sets was taken, because the Agda standard library includes a definition of lists with definitions of list membership $\in$ and other associated lemmas, which proved to be useful for definitions of the $\subseteq$ relation on types. 


From the above definition, it is obvious that the split definitions of `IType` and `ITypeI` are somewhat redundant, in that `ITypeI` only has one constructor `∩` and therefore, any instance of `IType` in the definition of `ITypeS` can simply be replaced by `List IType`:

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

~~~{.agda}
++-∷'l : ∀ {A τi τj} -> τi ∷'l A -> τj ∷'l A -> (τi ++ τj) ∷'l A
++-∷'l nil τj∷'A = τj∷'A
++-∷'l (cons τ∷'A τs∷'A) τj∷'A = cons τ∷'A (++-∷'l τs∷'A τj∷'A)
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

~~~{.agda}
Y :    ∀ {Γ A τi τ} -> (τi∷A : τi ∷'l A) -> (τ∈τi : τ ∈ τi) ->
    ------------------------------------------------------------
    Γ ⊩ Y A ∶ (∩ (Data.List.map (λ τk -> (∩ τi ~> τk)) τi) ~> τ)
~~~

Even though Agda's main strength is its the powerful pattern matching, it was quickly realized that pattern matching on the type `(∩ (Data.List.map (λ τk -> (∩ τi ~> τk)) τi) ~> τ)` is difficult due to the map function, which appears inside the definition.    
Several modifications were made to the rule, until we arrived at it's current form. To create a compromise between the unrestricted intersection-types of $\lambda_\cap^{BCD}$, which made expressing the $(Y)$ rule much simpler, and the strict typing, which provided a restricted version of type derivation over the $\lambda_\cap^{BCD}$ system, we modified strict types to include intersections on both the left and right sub-terms of a strict type:

<div class="Definition" head="Semi-strict intersection types">
\begin{center}
$\begin{aligned}
\mathcal{T}_s &::= \phi\ |\ (\mathcal{T}_s \cap\hdots\cap \mathcal{T}_s) \leadsto (\mathcal{T}_s \cap\hdots\cap \mathcal{T}_s) \\ 
\end{aligned}$
\end{center}
</div>

$\ $
<div class="Remark">**Maybe too much detail??**
After redefining the intersection types, the definition of the $(arr)$ rule for the type subset relation is now:

\begin{center}
\AxiomC{$\tau_i \subseteq^A_\ell \tau_j$}
  \AxiomC{$\tau_m \subseteq^B_\ell \tau_n$}
  \LeftLabel{$(arr)$}
  \BinaryInfC{$\tau_j \leadsto \tau_m \subseteq^{A \to B} \tau_i \leadsto \tau_n$}
  \DisplayProof
\end{center}
</div>

The final version of the $(Y)$ rule, along with the other modified rules of the typing relation are presented below:

<div class="Definition" head="Intersection-type assignment">This definition assumes that the typing context $\Gamma$, which is a list of triples $(x, \tau_i, A)$, is well formed. For each triple, written as $x : \tau_i ::_\ell A$, this means that the free variable $x$ does not appear elsewhere in the domain of $\Gamma$. Each intersection type $\tau_i$, associated with a variable $x$, also refines a simple type $A$. In the definition below, we also assume the following convention $\bigcap \tau \equiv [\tau]$:
\label{Definition:itypAssignment}
\begin{center}
  \AxiomC{$\exists (x : \tau_i ::_\ell A) \in \Gamma.\ \bigcap \tau \subseteq^A \tau_i$}
  \LeftLabel{$(var)$}
  \UnaryInfC{$\Gamma \Vdash x_{\{A\}} : \tau$}
  \DisplayProof
  %------------------------------------
  \vskip 1.5em
  \AxiomC{$\Gamma \Vdash u_{\{A \to B\}} : \tau_i \leadsto \tau_j$}
  \AxiomC{$\Gamma \Vdash_\ell v_{\{A\}} : \tau_i$}
  \LeftLabel{$(app)$}
  \RightLabel{$(\bigcap \tau \subseteq^B \tau_j)$}
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
  \AxiomC{$\exists \tau_x.\ \bigcap (\tau_x \leadsto \tau_x) \subseteq^{A \to A} \tau_i \land \tau_j \subseteq^A \tau_x$}
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

##Proofs?

To further motivate the final version of the $(Y)$ rule, we look at ? ....

precondition is as it is because we need $\tocap$ and subtyping rule....