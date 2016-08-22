#Methodology
\label{chap:method}

The idea of formalizing a functional language in multiple theorem provers and objectively assessing the merits and pitfalls of the different formalizations is definitely not a new idea. The most well known attempt to do so on a larger scale is the $\poplm$ challenge, proposed in the "Mechanized Metatheory for the Masses: The $\poplm$ Challenge" paper by @aydemir05.   
This paper prompted several formalizations of the benchmark typed $\lambda$-calculus, proposed by the authors of the challenge, in multiple theorem provers, such as Coq, Isabelle, Matita or Twelf. However, to the best of our knowledge, there has been no published follow-up work, drawing conclusions about the aptitude of different mechanizations, which would be useful in deciding on the best mechanization approach to take in formalizing the $\lamy$ calculus.   
This project definitely does not aim to answer the same question as the original challenge, namely: 

> "How close are we to a world where every paper on programming languages is accompanied by an electronic appendix with machine- checked proofs?" (@aydemir05)

Instead, it draws inspiration from the criteria for the "benchmark mechanization", specified by the challenge, to find the best mechanization approach as well as the right set of tools for our purpose of effectively mechanizing the theory underpinning HOMC.

Our comparison proceeded in two stages of elimination, where the first stage was a comparison of the two chosen mechanizations of binders for the $\lamy$ calculus (\cref{chap:compIsa}), namely nominal set and locally nameless representations of binders. The main reason for the fairly narrow selection of only two binder mechanizations was the limited time available for this project. In order to at least partially achieve the goal of mechanizing the intersection type theory for the $\lamy$ calculus, we decided to cut down the number of comparisons to the two (seemingly) most popular binder mechanizations (chosen by word of mouth and literature review of the field).   
After comparing and choosing the optimal mechanization of binders, \cref{chap:compAgda} then goes on to compare this mechanization in two different theorem provers, Isabelle and Agda (again, only two choices due to limited time).   
The "winning" theorem prover from this round was finally used to formalize intersection-types and the proofs of subject invariance.

##Evaluation criteria

The $\poplm$ challenge stated three main criteria for evaluating the submitted mechanizations of the benchmark calculus:

- Mechanization/implementation overheads
- Technology transparency
- Cost of entry

This project focuses mainly on the two criteria of mechanization overheads and technology transparency, since the focus of our comparison is to choose the best mechanization and theorem prover to use for implementing intersection types for the $\lamy$ calculus, rather than asses the viability of theorem provers in general, which was the original goal of the $\poplm$ challenge. These criteria are described in greater detail below:

###Technology transparency

Technology transparency, within the context of this work, is mostly concerned with the presentation of the theory inside a proof assistant, such as Isabelle or Agda. Whilst there is no direct measure of transparency, per se, it is almost always immediately obvious which presentation is more transparent, when one is presented with comparative examples. This work makes a case for transparency, or the lack thereof, by providing side-by-side snippets from different mechanizations of the same theory.

<div class="Example">
\label{Example:sqareOdd}
To demonstrate this, we examine the two different (though not completely distinct) styles of writing proofs in Isabelle, namely using apply-style proofs or the Isar proof language.
First, to demonstrate the Isar proof language and showcase the technology transparency it affords, we examine the proof that a square of an odd number is itself odd\footnotemark and then present the mechanized version of this proof in Isar.

<div class="Lemma" head="The square of an odd number is also odd">
<div class="proof">
By definition, if $n$ is an odd integer, it can be expressed as

\begin{center}
$n=2k+1$
\end{center}

for some integer $k$. Thus

\begin{center}
$\begin{aligned}
n^{2}&=(2k+1)^{2}\\
&=(2k+1)(2k+1)\\
&=4k^{2}+2k+2k+1\\
&=4k^{2}+4k+1\\
&=2(2k^{2}+2k)+1.
\end{aligned}$
\end{center}

Since $2k^2 + 2k$ is an integer, $n^2$ is also odd.
</div>
</div>

Now, the same (albeit slightly simplified) proof is presented using the Isar language:


~~~{.isabelle}
lemma sq_odd:
  fixes n and odd :: "nat ⇒ bool"
  defines "odd x ≡ ∃k. x = 2 * k + 1"
  assumes "odd n"
  shows "odd (n*n)"
proof -
  from assms obtain k where n_def: "n = 2 * k + 1" 
    unfolding odd_def by auto
  then have "n * n = (2 * k + 1) * (2 * k + 1)" by simp
  then have "n * n = (4 * k * k) + (4 * k) + 1" by simp
  hence     "n * n = 2 * ((2 * k * k) + (2 * k)) + 1" by simp
  thus "odd (n * n)" unfolding odd_def by blast
qed
~~~

Clearly, this mechanized proof reads much like the rigorous paper proof that precedes it.   
When the same proof is presented using the apply-style proof in Isabelle, it is immediately apparent that it is much less transparent, as we obfuscate the natural flow of the informal proof, hiding most of the reasoning in automation (the last line `by simp+`): 

~~~{.isabelle}
lemma sq_odd: "⋀n :: nat. (∃k. n = 2 * k + 1) ⟹ ∃k. n * n = 2 * k + 1"
apply (erule_tac P="λk. n = 2 * k + 1" in exE)
apply (rule_tac x="(2 * x * x) + (2 * x)" in exI)
apply (rule_tac s="(2 * x + 1) * (2 * x + 1)" in subst)
by simp+
~~~

While this example might be slightly exaggerated, it clearly demonstrates the relative lack of human readability, comapred to the Isar proof.    
$\ $
<div class="Note">The whole apply-style script can in fact just be substituted by the single line command: `by (auto, presburger)
`)</div>
</div>
\footnotetext{The informal proof was copied from \url{https://en.wikipedia.org/wiki/Direct_proof}}
<!--As the snippets from \cref{Example:commNat} demonstrate, Agda includes features, such as Unicode support for mathematical symbols like $\mathbb{N}$, to make the implementation look more "natural". Other features, like Isabelle's proof representation language Isar (discussed in \cref{proofAsProg}), are built into theorem provers to try to make the proofs and definitions look as close to conventional notation as possible.   -->
The example given above demonstrates, that transparency is a comparative measure, as it depends directly on some point of reference. As is also apparent from the example, transparency can often come at a cost of brevity. The reason why apply-style proofs exist and are used, even though Isar proofs are generally regarded as the better alternative, is the fact that they can be significantly faster to write, as they are a lot less verbose. Of course, relying more on automation, these proofs naturally tend to be harder to follow. However, much like in an informal setting, where we rarely write proofs in a completely rigorous detail, especially those which are "uninteresting" from point of the whole theory, so the different styles of proofs are used for different proofs. The short, "boring" ones are often written using apply-style scripts, whereas longer more interesting lemmas use the Isar language, to make the reasoning intuitive, i.e. transparent.   
This trade-off brings us to the second criterion, namely the mechanization overheads.

<!--The criterion of technology transparency is discussed mainly in \cref{chap:compAgda}, which deals with the comparison of Isabelle and Agda. The choice of the two theorem provers, but especially of Isabelle, was largely subjective. Having had previous experience with Isabelle, it was natural to use it initially, to lower the cost of entry. Initially only using Isabelle for both formalizations of binders also allowed for a more uniform comparison of the mechanization overheads.   
The choice of Agda as the second implementation language was motivated by Agda having a dependent-type system. As a result, the style of proofs in Agda seems quite different to Isabelle, since the distinction between proofs and programs is largely erased. Agda was chosen over Coq, which is also a dependently-typed language, because it is more "bare-bones" and thus seemed more accessible to a novice in dependently-typed languages. Agda also has a higher "cool"-factor than Coq, being a newer language.-->

###Mechanization/implementation overheads
\label{mechOverheads}

When talking about mechanization overheads, we usually mean the additional theory needed to translate the informal definitions we reason about on paper into the fully formal setting of a theorem prover. 

<div class="Example">
\label{Example:listITypes}
To demonstrate what we mean by this, we will take the definition of intersection types and its implmentation in Agda (further discussed in \cref{itypesAgda}). Taking the \cref{Definition:itypes} as a starting point, namely defining intersection types as:

\begin{center}
$\begin{aligned}
\mathcal{T}_s &::= \phi\ |\ \mathcal{T} \leadsto \mathcal{T}_s \\ 
\mathcal{T} &::= (\mathcal{T}_s \cap\hdots\cap \mathcal{T}_s)
\end{aligned}$
\end{center}

we translate the strict types $\mathcal{T}_s$ to a definition in Agda in a straightforward way, since we only need to translate$\mathcal{T}_s$ into a GADT (generalized algebraic datatype) definition:

~~~{.agda escapeinside=||}
data T|$_\texttt{s}$| where
  φ : T|$_\texttt{s}$|
  _~>_ : (τ : T) -> (ψ : T|$_\texttt{s}$|) -> T|$_\texttt{s}$|
~~~
$\ $
<div class="Remark">
The definition above is perhaps more obvious, when $\mathcal{T}_s$ is presented inductively as:
\begin{center}
  \AxiomC{}
  \UnaryInfC{$\phi \in \mathcal{T}_s$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\tau \in \mathcal{T}$}
  \AxiomC{$\psi \in \mathcal{T}_s$}
  \BinaryInfC{$\tau \leadsto \psi \in \mathcal{T}_s$}
  \DisplayProof
\end{center}
</div>

The informal definition of $\mathcal{T}$, however, is slightly more complicated, since intuitively, $\mathcal{T}_s \cap\hdots\cap \mathcal{T}_s$ represents a finite set of elements of $\mathcal{T}_s$. We can describe the set of intersection terms $\mathcal{T}$ with the following inductive definition:

\begin{center}
  \AxiomC{$\{\tau_1, \hdots, \tau_n\} \subset \mathcal{T}_s$}
  \UnaryInfC{$\tau_1 \cap\hdots\cap \tau_n \in \mathcal{T}$}
  \DisplayProof
\end{center}

In order to encode this definition in Agda, we will have to rely on some definition of a finite set (since the rule above assumes knowledge of finite sets and the subset relation $\subset$ in its precondition).   
Whilst the notion of a finite set is so trivial, we rarely bother axiomatizing it, Agda does not actually know about finite sets by default and its standard library only includes the definition of finite sets of natural numbers. We can instead use lists to "simulate" finite sets, as they are similar in many regards, i.e. the Agda implementation of lists includes the notion of subset inclusion for lists, so that one can write a proof of $[1,2] \subseteq [2,2,1]$ easily. Thus, for $\mathcal{T}$, we get:

~~~{.agda escapeinside=||}
data T where
  ∩ : List T|$_\texttt{s}$| -> T
~~~

Whilst this definition is now largely equivalent to the informal inductive definition, we have lost quite a bit of transparency as a result. Consider the strict type $\tau \cap \psi \leadsto \tau$, is written as `∩ (τ ∷ ψ ∷ [])  \textasciitilde > τ` in Agda. We can improve things somewhat by getting rid of the pointless constructor `∩` and merging the two definitions of $\mathcal{T}$ and $\mathcal{T}_s$ into a single definition, namely:

~~~{.agda escapeinside=||}
data T|$_\texttt{s}$| where
  φ : T|$_\texttt{s}$|
  _~>_ : (τ : List T|$_\texttt{s}$|) -> (ψ : T|$_\texttt{s}$|) -> T|$_\texttt{s}$|
~~~
$\ $
<div class="Remark">
This definition now corresponds to the merging of the two previously given inductive definitions of $\mathcal{T}$ and $\mathcal{T}_s$:
\begin{center}
  \AxiomC{}
  \UnaryInfC{$\phi \in \mathcal{T}_s$}
  \DisplayProof
  \hskip 1.5em
  \AxiomC{$\{\tau_1, \hdots, \tau_n\} \subset \mathcal{T}_s$}
  \AxiomC{$\psi \in \mathcal{T}_s$}
  \BinaryInfC{$\tau_1 \cap\hdots\cap \tau_n \leadsto \psi \in \mathcal{T}_s$}
  \DisplayProof
\end{center}
</div>
Now, $\tau \cap \psi \leadsto \tau$, corresponds to the Agda term `(τ ∷ ψ ∷ [])  \textasciitilde > τ`, which is still not ideal. We can, however, define some simple sugar notation:

~~~{.agda escapeinside=||}
_∩_ : T|$_\texttt{s}$| -> T|$_\texttt{s}$| -> List T|$_\texttt{s}$|
τ ∩ ψ = τ ∷ ψ ∷ []
~~~

Thus, we finally get the Agda term `τ ∩ ψ \textasciitilde > τ` which now clearly corresponds to $\tau\ \cap\ \psi \leadsto \tau$.
</div>

As the above example clearly shows, the first/simplest measure of the amount of implementation overheads, is simply the length of the code/proof scrips, defining the terms and lemmas of a theory.
Whilst the length of code might provide an indication of the possible level of implementation overheads, it is important to keep in mind, that brevity of code can often also depend on the level of transparency, as evidenced by both \cref{Example:sqareOdd} and the one above, where the shorter code turned out to also be the less transparent one. Depending on the priorities, we therefore often sacrifice either transparency for brevity or vice versa (which can greatly impact this simple metric for overheads).    
Therefore, instead of simply looking at the length of the produced document, we also compare the number of lemmas, disregarding the length of each one. Even though this measure also carries disadvantages (one could, for example, in-line the whole Church Rosser proof into one giant lemma) it is less sensitive in regard to transparency.

Another aspect which ties into both transparency and mechanization overheads is the level of automation. As was demonstrated by \cref{Example:sqareOdd}, wherein the lemma could in fact be proved automatically with almost no user input, having low implementation overheads (in proofs) is often tied to the level of automation the tool provides.  
More concretely, a tool with good automation will include a standard library of common definitions and theorems, so that the user does not have to re-define and re-prove basic mathematical object and properties and instead can focus on the specific theory she/he wants to implement.    
This is indeed largely the reason why we used Isabelle along with the [nominal sets library](http://www.inf.kcl.ac.uk/staff/urbanc/Nominal/), maintained by Christian Urban, where the theory was conveniently hidden away and managed for us by Isabelle's automatic provers, so that our mechanization overheads were minimal. However, there were several caveats to this, which we discuss in the next chapter.   
On the other hand, the choice of locally nameless encoding, as opposed to using pure de Bruijn indices, was motivated by the claim that locally nameless encoding largely mitigates the disadvantages of de Bruijn indices especially when it comes to technology transparency. The LN encoding is also a lot more bare-bones than the nominal set theory (if there was not library and one had to formalize the theory from scratch), carrying relatively manageable overheads.   
In order to keep our comparison balanced, we often didn't leverage Isabelle's automation to it's fullest, choosing instead to keep some lemmas (especially in the nominal implementation) deliberately verbose, so as to keep them both more transparent and easier to compare with the locally nameless versions. Another reason for this was the comparison between Isabelle and Agda, which doesn't include as much automation.
