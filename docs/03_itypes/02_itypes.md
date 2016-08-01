<!--
<div class="Definition" head="Intersection Types">
Note that $\mathsf{o}$ and $\phi$ are constants. $\omega$ is used to denote an empty list of strict intersection types. The following sugar notation will also occasionally be used: $\bigcap \tau \equiv [ \tau ]$ and $\tau \cap \tau' \equiv \bigcap \tau \concat \bigcap \tau' \equiv [ \tau, \tau' ]$.

i)  Simple types:
    $$\sigma ::= \mathsf{o}\ |\ \sigma \to \sigma$$
ii) Intersection types:
    $$\mathcal{T}_s ::= \phi\ |\ \mathcal{T} \leadsto \mathcal{T}$$
    $$\mathcal{T} ::= \mathsf{List}\ \mathcal{T}_s$$
</div>


Next, we redefine the $\lambda$-terms slightly, by annotating the terms with simple types. The reason for this will be clear later on.

<div class="Definition" head="Terms">
Let $\sigma$ range over simple types in the following definition:

i)  Simply-typed terms:
    $$M::= x_\sigma\ |\ MM\ |\ \lambda x_\sigma.M\ |\ Y_\sigma \text{ where }x \in Var$$
ii) Simply-typed pre-terms:
    $$M'::= x_\sigma\ |\ i\ |\ M'M'\ |\ \lambda_\sigma.M'\ |\ Y_\sigma \text{ where }x \in Var\text{ and }i \in \mathbb{N}$$
</div>

Note that both definitions implicitly assume that in the case of application, a well formed simply-typed term will be of the form $st$, where $s$ has some simple type $A \to B$ and $t$ is typed with the simple type $A$. Sometimes the same subscript notation will be used to indicate the simple type of a given pre-/term, for example: $m_{A \to B}$. Also, rather confusingly, the simple type of $Y_A$ is $(A \to A) \to A$, and thus $Y_A$ should not be confused with a constant $Y$ having a simple type $A$. **Maybe use something like this instead?:** $m_{:A \to B}$ i.e. $Y_{A:(A \to A) \to A}$.   
The typed versions of substitution and the open and close operations are virtually identical to the untyped versions.



--------Rules ~>^ and trans for  <=A -----------------

\AxiomC{$(\tau_i \leadsto (\tau_j \concat \tau_k) ,\ \tau_m) :: A \to B$}
  \LeftLabel{$(\tocap)$}
  \UnaryInfC{$(\tau_i \leadsto (\tau_j \concat \tau_k) ,\ \tau_m) \subseteq^{A \to B} (\tau_i \leadsto \tau_j ,\ \tau_i \leadsto \tau_k ,\ \tau_m)$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\tau_i \subseteq^A \tau_j$}
  \AxiomC{$\tau_j \subseteq^A \tau_k$}
  \LeftLabel{$(trans)$}
  \BinaryInfC{$\tau_i \subseteq^A \tau_k$}
  \DisplayProof
  \vskip 1.5em




It's easy to show the following properties hold for the $\subseteq^A$ and $::$ relations:

<div class="Lemma" head="$\subseteq\implies::$">
i)  $\tau \subseteq^A_s \delta \implies \tau ::_s A \land \delta ::_s A$
ii) $\tau_i \subseteq^A \delta_i \implies \tau_i :: A \land \delta_i :: A$
</div>
<div class="proof">
\label{test}
By **?mutual?** induction on the relations $\subseteq^A_s$ and $\subseteq^A$.
</div>

**Lemma** ($\subseteq$ admissible) The following rules are admissible in $\subseteq^A_s/\subseteq^A$:

i)    
  \AxiomC{$\tau ::_s A$}
  \LeftLabel{$(refl_s)$}
  \UnaryInfC{$\tau \subseteq^A_s \tau$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\tau_i :: A$}
  \LeftLabel{$(refl)$}
  \UnaryInfC{$\tau_i \subseteq^A \tau_i$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\tau \subseteq^A_s \tau'$}
  \AxiomC{$\tau' \subseteq^A_s \tau''$}
  \LeftLabel{$(trans_s)$}
  \BinaryInfC{$\tau \subseteq^A_s \tau''$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\tau_i \subseteq \tau_j$}
  \LeftLabel{$(\subseteq)$}
  \RightLabel{$(\tau_j :: A)$}
  \UnaryInfC{$\tau_i \subseteq^A \tau_j$}
  \DisplayProof

ii)
  \AxiomC{$\tau_i :: A$}
  \AxiomC{$\tau_j \subseteq^A \tau_{j'}$}
  \LeftLabel{$(\conL)$}
  \BinaryInfC{$\tau_i \concat \tau_j \subseteq^A \tau_i \concat \tau_{j'}$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\tau_i \subseteq^A \tau_{i'}$}
  \AxiomC{$\tau_j :: A$}
  \LeftLabel{$(\conR)$}
  \BinaryInfC{$\tau_i \concat \tau_j \subseteq^A \tau_{i'} \concat \tau_j$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\tau_i \subseteq^A \tau_{k}$}
  \AxiomC{$\tau_j \subseteq^A \tau_{k}$}
  \LeftLabel{$(glb)$}
  \BinaryInfC{$\tau_i \concat \tau_j \subseteq^A \tau_k$}
  \DisplayProof

iii)
  \AxiomC{$\tau_i \subseteq^A \tau_j$}
  \AxiomC{$\tau_{i'} \subseteq^A \tau_{j'}$}
  \LeftLabel{$(mon)$}
  \BinaryInfC{$\tau_i \concat \tau_{i'} \subseteq^A \tau_j \concat \tau_{j'}$}
  \DisplayProof

iv)
  \AxiomC{$\tau_i :: A$}
  \AxiomC{$\tau_j :: A$}
  \LeftLabel{$(\tocap')$}
  \BinaryInfC{$\bigcap ((\tau_i \concat \tau_j) \leadsto (\tau_i \concat \tau_j)) \subseteq^{A \to B} \tau_i \leadsto \tau_i \cap \tau_j \leadsto \tau_j$}
  \DisplayProof


_Proof:_ 
  
i)    By induction on $\tau$ and $\tau_i$.
ii)   By induction on $\tau_i \subseteq^A \tau_{i'}$.
iii)  
  \vskip 1em
  \AxiomC{$\tau_i \subseteq^A \tau_j$}
  \AxiomC{}
  \UnaryInfC{$\tau_j \subseteq \tau_j \concat \tau_{j'}$}
  \LeftLabel{$(\subseteq)$}
  \UnaryInfC{$\tau_j \subseteq^A \tau_j \concat \tau_{j'}$}
  \LeftLabel{$(trans)$}
  \BinaryInfC{$\tau_i \subseteq^A \tau_j \concat \tau_{j'}$}
  \AxiomC{$\tau_{i'} \subseteq^A \tau_{j'}$}
  \AxiomC{}
  \UnaryInfC{$\tau_{j'} \subseteq \tau_j \concat \tau_{j'}$}
  \LeftLabel{$(\subseteq)$}
  \UnaryInfC{$\tau_{j'} \subseteq^A \tau_j \concat \tau_{j'}$}
  \LeftLabel{$(trans)$}
  \BinaryInfC{$\tau_{i'} \subseteq^A \tau_j \concat \tau_{j'}$}
  \LeftLabel{$(glb)$}
  \BinaryInfC{$\tau_i \concat \tau_{i'} \subseteq^A \tau_j \concat \tau_{j'}$}
  \DisplayProof

iv)  Follows from $(\tocap)$, $(cons)$ and $(trans)$.

##Intersection-type assignment


Having annotated the $\lambda$-terms with simple types, the following type assignment only permits the typing of simply-typed $\lambda$-terms with an intersection type, which refines the simple type of the $\lambda$-term:


**Definition** (Intersection-type assignment) 
\begin{center}
  \AxiomC{$\exists (x, \tau_i, A) \in \Gamma.\ \bigcap \tau \subseteq^A \tau_i$}
  \LeftLabel{$(var)$}
  \UnaryInfC{$\Gamma \Vdash_s x_A : \tau$}
  \DisplayProof
  %------------------------------------
  \hskip 1.5em
  \AxiomC{$\Gamma \Vdash_s u_{A \to B} : \tau_i \leadsto \tau_j$}
  \AxiomC{$\Gamma \Vdash v_A : \tau_i$}
  \LeftLabel{$(app)$}
  \RightLabel{$(\bigcap \tau \subseteq^B \tau_j)$}
  \BinaryInfC{$\Gamma \Vdash_s uv_B : \tau$}
  \DisplayProof
  %------------------------------------
  \vskip 1.5em
  \AxiomC{$\forall x \not\in L.\ (x, \tau_i, A),\Gamma \Vdash m^x : \tau_j$}
  \LeftLabel{$(abs)$}
  \UnaryInfC{$\Gamma \Vdash_s \lambda_A.m : \tau_i \leadsto \tau_j$}
  \DisplayProof
  %------------------------------------
  \hskip 1.5em
  \AxiomC{$\exists \tau_x.\ \bigcap (\tau_x \leadsto \tau_x) \subseteq^{A \to A} \tau_i \land \tau_j \subseteq^A \tau_x$}
  \LeftLabel{$(Y)$}
  \UnaryInfC{$\Gamma \Vdash_s Y_{A} : \tau_i \leadsto \tau_j$}
  \DisplayProof
  %------------------------------------
  \vskip 1.5em
  \AxiomC{$\Gamma \Vdash_s m_{A \to B} : \tau_i \leadsto \tau_j$}
  \AxiomC{$\Gamma \Vdash_s m_{A \to B} : \tau_i \leadsto \tau_k$}
  \LeftLabel{$(\tocap)$}
  \RightLabel{$(\tau_{jk} \subseteq^B \tau_j \concat \tau_k)$}
  \BinaryInfC{$\Gamma \Vdash_s m_{A \to B} : \tau_i \leadsto \tau_{jk}$}
  \DisplayProof
  %------------------------------------
  \vskip 1.5em
  \AxiomC{}
  \LeftLabel{$(nil)$}
  \UnaryInfC{$\Gamma \Vdash m : \omega$}
  \DisplayProof
  %------------------------------------
  \hskip 1.5em
  \AxiomC{$\Gamma \Vdash_s m : \tau$}
  \AxiomC{$\Gamma \Vdash m : \tau_i$}
  \LeftLabel{$(cons)$}
  \BinaryInfC{$\Gamma \Vdash m : \tau , \tau_i$}
  \DisplayProof
  \vskip 1.5em
\end{center}

In the definition above, $\Gamma$ is the typing context, consisting of triples of the variable name and the corresponding intersection and simple types. $\Gamma$ is defined as a list of these triples in the Agda implementation. It is assumed in the typing system, that $\Gamma$ is well-formed. Formally, this can be expressed in the following way:

**Definition** (Well-formed intersection-type context)
\begin{center}
  \AxiomC{}
  \LeftLabel{$(nil)$}
  \UnaryInfC{$\wf [\ ]$}
  \DisplayProof
  %------------------------------------
  \hskip 1.5em
  \AxiomC{$x \not\in \mathsf{dom}\ \Gamma$}
  \AxiomC{$\tau_i :: A$}
  \AxiomC{$\wf \Gamma$}
  \LeftLabel{$(cons)$}
  \TrinaryInfC{$\wf (x,\tau_i,A),\Gamma$}
  \DisplayProof
  \vskip 1.5em
\end{center}


###Subtyping

In the typing system, the rules $(Y)$ and $(\tocap)$ are defined in a slightly more complicated way than might be necessary. For example, one might assume, the $(Y)$ rule could simply be:   

\begin{center}
  \vskip 1em
  \AxiomC{}
  \LeftLabel{$(Y)$}
  \UnaryInfC{$\Gamma \Vdash_s Y_{A} : \bigcap (\tau_x \leadsto \tau_x) \leadsto \tau_x$}
  \DisplayProof
  \vskip 1.5em
\end{center}

The reason why the more complicated forms of both rules were introduced was purely an engineering one, namely to make the proof of sub-typing/weakening possible, as the sub-typing rule is required in multiple further proofs:

**Lemma** (Sub-typing) The following rule(s) are admissible in $\Vdash_s$/$\Vdash$:

\begin{center}
  \AxiomC{$\Gamma \Vdash_s m_A : \tau$}
  \LeftLabel{$(\supseteq_s)$}
  \RightLabel{$(\Gamma' \subseteq_\Gamma \Gamma, \tau \supseteq^A_s \tau')$}
  \UnaryInfC{$\Gamma' \Vdash_s m_A : \tau'$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\Gamma \Vdash m_A : \tau_i$}
  \LeftLabel{$(\supseteq)$}
  \RightLabel{$(\Gamma' \subseteq_\Gamma \Gamma, \tau_i \supseteq^A_s \tau_j)$}
  \UnaryInfC{$\Gamma' \Vdash m_A : \tau_j$}
  \DisplayProof
\end{center}
_Proof:_ Ommited.

The relation $\Gamma \subseteq_\Gamma \Gamma'$ is defined for any well-formed contexts $\Gamma, \Gamma'$, where for each triple $(x ,\tau_i, A) \in \Gamma$, there is a corresponding triple $(x ,\tau_j, A) \in \Gamma'$ s.t. $\tau_i \subseteq^A \tau_j$.

###Inversion lemmas

The shape of the derivation tree is not always unique for arbitrary typed term $\Gamma \Vdash_s m :\tau$. For example, given a typed term $\Gamma \Vdash_s \lambda_A.m :\tau_i \leadsto \tau_j$, either of the following two derivation trees, could be valid:

\begin{center}\hskip 1.5em
  \AxiomC{$\vdots$}
  \UnaryInfC{$\forall x \not\in L.\ (x, \tau_i, A),\Gamma \Vdash m^x : \tau_j$}
  \LeftLabel{$(abs)$}
  \UnaryInfC{$\Gamma \Vdash_s \lambda_A.m : \tau_i \leadsto \tau_j$}
  \DisplayProof
  %------------------------------------
  \vskip 1.5em
  \AxiomC{$\vdots$}
  \UnaryInfC{$\Gamma \Vdash_s \lambda_A.m_B : \tau_i \leadsto \tau_p$}

  \AxiomC{$\vdots$}
  \UnaryInfC{$\Gamma \Vdash_s \lambda_A.m_B : \tau_i \leadsto \tau_q$}
  \LeftLabel{$(\tocap)$}
  \RightLabel{$(\tau_j \subseteq^B \tau_p \concat \tau_q)$}
  \BinaryInfC{$\Gamma \Vdash_s \lambda_A.m_B : \tau_i \leadsto \tau_j$}
  \DisplayProof
\end{center}


However, it is obvious that the second tree will always necessarily have to have an application of $(abs)$ in all its branches. Because it will be necessary to reason about the shape of the typing derivation trees, it is useful to prove the following inversion lemmas:

**Lemma** ($Y$-inv, $abs$-inv)

i)  $\Gamma \Vdash_s Y_{A} : \tau_i \leadsto \tau_j \implies \exists \tau_x.\ \bigcap (\tau_x \leadsto \tau_x) \subseteq^{A \to A} \tau_i \land \tau_j \subseteq^A \tau_x$
ii) $\Gamma \Vdash_s \lambda_A.m : \tau_i \leadsto \tau_j \implies \exists L.\ \forall x \not\in L.\ (x, \tau_i, A),\Gamma \Vdash m^x : \tau_j$

_Proof_:

i)  There are two cases to consider, one, where the last rule in the derivation tree of $\Gamma \Vdash_s Y_{A} : \tau_i \leadsto \tau_j$ was $(Y)$. Otherwise, the last rule was $(\tocap)$:

    $(Y)$: Follows immediately.   
    $(\tocap)$: We must have a derivation tree of the shape:

    \begin{center}
      \AxiomC{$\vdots$}
      \UnaryInfC{$\Gamma \Vdash_s Y_A : \tau_i \leadsto \tau_p$}

      \AxiomC{$\vdots$}
      \UnaryInfC{$\Gamma \Vdash_s Y_A : \tau_i \leadsto \tau_q$}
      \LeftLabel{$(\tocap)$}
      \RightLabel{$(\tau_j \subseteq^B \tau_p \concat \tau_q)$}
      \BinaryInfC{$\Gamma \Vdash_s Y_A : \tau_i \leadsto \tau_j$}
      \DisplayProof
    \end{center}

    Then by IH, we have:   
    - $\exists \tau_{xp}.\ \bigcap (\tau_{xp} \leadsto \tau_{xp}) \subseteq^{A \to A} \tau_i \land \tau_p \subseteq^A \tau_{xp}$ and
    
    - $\exists \tau_{xq}.\ \bigcap (\tau_{xq} \leadsto \tau_{xq}) \subseteq^{A \to A} \tau_i \land \tau_q \subseteq^A \tau_{xq}$

    We then take $\tau_x \equiv \tau_{xp} \concat \tau_{xq}$:

\begin{center}
  \tiny
  \AxiomC{}
  \LeftLabel{$(\tocap')$}
  \UnaryInfC{$\bigcap (\tau_{x} \leadsto \tau_{x}) \subseteq^{A \to A} \tau_{xp}\leadsto \tau_{xp} \cap \tau_{xq} \leadsto \tau_{xq}$}

  \AxiomC{}
  \LeftLabel{$(IH)$}
  \UnaryInfC{$\tau_{xp} \leadsto \tau_{xp} \subseteq^{A \to A} \tau_i$}
  \AxiomC{}
  \LeftLabel{$(IH)$}
  \UnaryInfC{$\tau_{xq} \leadsto \tau_{xq} \subseteq^{A \to A} \tau_i$}
  \LeftLabel{$(mon)$}
  \BinaryInfC{$\tau_{xp}\leadsto \tau_{xp} \cap \tau_{xq} \leadsto \tau_{xq} \subseteq^{A \to A} \tau_i \concat \tau_i$}
  \LeftLabel{$(trans)$}
  \BinaryInfC{$\bigcap (\tau_{x} \leadsto \tau_{x}) \subseteq^{A \to A} \tau_i \concat \tau_i$}

  \AxiomC{}
  \UnaryInfC{$\tau_i \concat \tau_i \subseteq \tau_i$}
  \LeftLabel{$(\subseteq)$}
  \UnaryInfC{$\tau_i \concat \tau_i \subseteq^{A \to A} \tau_i$}
  \LeftLabel{$(trans)$}
  \BinaryInfC{$\bigcap (\tau_{x} \leadsto \tau_{x}) \subseteq^{A \to A} \tau_i$}
  \DisplayProof
\end{center}

\begin{center}
  \vskip 1.5em
  \AxiomC{}
  \UnaryInfC{$\tau_j \subseteq^A \tau_p \concat \tau_q$}

  \AxiomC{}
  \LeftLabel{$(IH)$}
  \UnaryInfC{$\tau_p \concat \subseteq^A \tau_{xp}$}
  \AxiomC{}
  \LeftLabel{$(IH)$}
  \UnaryInfC{$\tau_q \concat \subseteq^A \tau_{xq}$}
  \LeftLabel{$(mon)$}
  \BinaryInfC{$\tau_p \concat \tau_q \subseteq^A \tau_x$}
  \LeftLabel{$(trans)$}
  \BinaryInfC{$\tau_j \subseteq^A \tau_x$}
  \DisplayProof
  \vskip 1.5em
\end{center}

ii) Follows in a similar fashion.

##Proofs of subject expansion and reduction

An interesting property of the intersection types, is the fact that they admit both subject expansion and subject reduction, namely $\Vdash$ is closed under $\beta$-equality. Subject expansion and reduction are proved in two separate lemmas:

**Theorem** ($\Vdash$ closed under $=_\beta$)

i)    $\Gamma \Vdash_s m : \tau \implies m \Rightarrow_\beta m' \implies \Gamma \Vdash_s m' : \tau$
ii)   $\Gamma \Vdash m : \tau_i \implies m \Rightarrow_\beta m' \implies \Gamma \Vdash m' : \tau_i$
iii)  $\Gamma \Vdash_s m' : \tau \implies m \Rightarrow_\beta m' \implies \Gamma \Vdash_s m : \tau$
iv)   $\Gamma \Vdash m' : \tau_i \implies m \Rightarrow_\beta m' \implies \Gamma \Vdash m : \tau_i$

_Proof:_ By induction on $\Rightarrow_\beta$. The proofs in both directions follow by straightforward induction for all the rules except for $(Y)$ and $(beta)$. Note that the $(Y)$ rule here is not the typing rule, but rather the reduction rule $Y_A m \Rightarrow_\beta m(Y_A m)$.

i)
    $(Y)$: By assumption, we have $Y_A m \Rightarrow_\beta m(Y_A m)$ and $\Gamma \Vdash_s Y_A m : \tau$.
    By case analysis of the last rule applied in the derivation tree of $\Gamma \Vdash_s Y_A m : \tau$, we have two cases:
    - $(app)$ We have:

        \begin{center}
          \vskip 1em
          \AxiomC{$\vdots$}
          \UnaryInfC{$\Gamma \Vdash_s Y_A : \tau_i \leadsto \tau_j$}
          \AxiomC{$\vdots$}
          \UnaryInfC{$\Gamma \Vdash m_{A \to A} : \tau_i$}
          \LeftLabel{$(app)$}
          \RightLabel{$(\bigcap \tau \subseteq^A \tau_j)$}
          \BinaryInfC{$\Gamma \Vdash_s Y_{A} m : \tau$}
          \DisplayProof
          \vskip 1em
        \end{center}

        Then, by ($Y$-inv) we have some $\tau_x$ s.t $\bigcap (\tau_x \leadsto \tau_x) \subseteq^{A \to A} \tau_i \land \tau_j \subseteq^A \tau_x$.


    - $(\tocap)$ Then we have:

        \begin{center}
          \vskip 1em
          \AxiomC{$\vdots$}
          \UnaryInfC{$\Gamma \Vdash_s Y_{B \to C} m : \tau_i \leadsto \tau_j$}
          \AxiomC{$\vdots$}
          \UnaryInfC{$\Gamma \Vdash_s Y_{B \to C} m : \tau_i \leadsto \tau_k$}
          \LeftLabel{$(\tocap)$}
          \RightLabel{$(\tau_{jk} \subseteq^C \tau_j \concat \tau_k)$}
          \BinaryInfC{$\Gamma \Vdash_s Y_{B \to C} m : \tau_i \leadsto \tau_{jk}$}
          \DisplayProof
          \vskip 1em
        \end{center}

        Where $A \equiv B \to C$.

        By IH, we get $\Gamma \Vdash_s m (Y_{B \to C} m) : \tau_i \leadsto \tau_j$ and $\Gamma \Vdash_s m (Y_{B \to C} m) : \tau_i \leadsto \tau_k$, thus from $(\tocap)$ it follows that $\Gamma \Vdash_s m (Y_{B \to C} m) : \tau_i \leadsto \tau_{jk}$

 ----------------->


