#Methodology

##Comparison of formalizations

The idea of formalizing a functional language in multiple theorem provers and objectively assessing the merits and pitfalls of the different formalizations is definitely not a new idea. The most well known attempt to do so on a larger scale is the $\poplm$ challenge, proposed in the "Mechanized Metatheory for the Masses: The $\poplm$ Challenge" paper by @aydemir05.   
This paper prompted several formalizations of the benchmark typed $\lambda$-calculus, proposed by the authors of the challenge, in multiple theorem provers, such as Coq, Isabelle, Matita or Twelf. However, to the best of our knowledge, there has been no published follow-up work, drawing conclusions about the aptitude of different mechanizations, which would be useful in deciding the best mechanization approach to take in formalizing the $\lamy$ calculus.   
Whilst this project does not aim to answer the same question as the original challenge, namely: 

> "How close are we to a world where every paper on programming languages is accompanied by an electronic appendix with machine- checked proofs?" (@aydemir05)

It draws inspiration from the criteria for the "benchmark mechanization", specified by the challenge, to find the best mechanization approach as well as the right set of tools for our purpose of effectively mechanizing the theory underpinning HOMC.

Our comparison proceeded in two stages of elimination, where the first stage was a comparison of the two chosen mechanizations of binders for the $\lamy$ calculus (\cref{chap:compIsa}), namely nominal set and locally nameless representations of binders. The main reason for the fairly narrow selection of only two binder mechanizations, was the limited time available for this project. In order to at least partially achieve the goal of mechanizing the intersection type theory for the $\lamy$ calculus, we decided to cut down the number of comparisons to the two (seemingly) most popular binder mechanizations (chosen by word of mouth and literature review of the field).   
After comparing and choosing the optimal mechanization of binders, the \hyperref[chap:compAgda]{next chapter} then goes on to compare this mechanization in two different theorem provers, Isabelle and Agda.   
The "winning" theorem prover from this round was then used to formalize intersection-types and prove subject invariance.

###Evaluation criteria

The $\poplm$ challenge stated three main criteria for evaluating the submitted mechanizations of the benchmark calculus:

- Mechanization/implementation overheads
- Technology transparency
- Cost of entry

To this, we add another criterion: 

- Proof automation

This project focuses mainly on the three criteria of mechanization overheads, technology transparency and automation, since the focus of our comparison is to chose the best mechanization and theorem prover to use for implementing intersection types for the $\lamy$ calculus (and proving subject invariance). These criteria are described in greater detail below:

####Mechanization/implementation overheads
When talking about mechanization overheads, we usually mean the additional theory needed to translate the informal theory we reason about on paper into the fully formal setting of a theorem prover. Implementation overheads are usually things deemed too trivial to consider in a paper proof and a good mechanization will leverage automation and other language features to hide as much of these overheads as possible. The best example of a mechanization overhead in this project is the formalization of binders, discussed in \cref{binders} of the previous chapter.

<div class="Example">
\label{Example:commNat}
Another classic example of mechanization overheads, imposed by a fully formal setting of a theorem prover is something as trivial as the proof of commutativity of addition of natural numbers. In order to prove this property formally in Agda, we first have to define what is a natural number, using peano numbers where we have a `Z` zero constructor and a successor function `S`:

~~~{.agda}
data ℕ : Set where
  Z : ℕ
  S : ℕ -> ℕ
~~~

Then we can define the addition operation for natural numbers:

~~~{.agda}
_+_ : ℕ -> ℕ -> ℕ
Z + x = x
S x + y = S (x + y)
~~~

Finally, the proof of commutativity of addition may end up looking something like this:

~~~{.agda}
S-inj : ∀ {x y} -> x ≡ y -> S x ≡ S y
S-inj refl = refl

+-comm' : ∀ x -> x + Z ≡ x
+-comm' Z = refl
+-comm' (S x) = S-inj (+-comm' x)

+-comm'' : ∀ x y -> x + S y ≡ S (x + y)
+-comm'' Z y = refl
+-comm'' (S x) y = S-inj (+-comm'' x y)

+-comm : ∀ x y -> (x + y) ≡ (y + x)
+-comm Z y rewrite +-comm' y = refl
+-comm (S x) y rewrite +-comm'' y x = S-inj (+-comm x y)
~~~

As we see here, this proof is quite long for something seemingly so trivial. Proofs of this type are usually unavoidable in a theorem prover, especially when we want to use such lemmas in a more interesting result we wan to formalize. Having low implementation overheads thus usually depends on the automation of the tool, wherein the tool itself is able to prove these properties automatically. What is more likely, however, is that a "good" tool will include something such a base theory (of natural numbers) in its library, so that he user does not have to re-prove these basic properties and instead can focus on the specific theory she/he wants to prove. This is indeed largely what happened when we used the nominal library, where the theory was conveniently hidden away and managed for us by Isabelle's automatic provers.
</div>

For the scope of this project, binders are discussed and used for comparison often, since they are the "weak spot" where mechanization overheads are most apparent.    
In this project, we decided to use nominal sets and locally nameless representation for binders, due to several reasons. The choice of nominal sets was tied to the implementation language, namely Isabelle, which has a well developed [nominal sets library](http://www.inf.kcl.ac.uk/staff/urbanc/Nominal/), maintained by Christian Urban. The appeal of using nominal sets is of course the touted minimal overheads in comparison to the informal presentation.   
The choice of locally nameless encoding, as opposed to using pure de Bruijn indices, was motivated by the claim that locally nameless encoding largely mitigates the disadvantages of de Bruijn indices especially when it comes to technology transparency (i.e. theorems about locally nameless presentation are much closer in formulation to the informal presentation than theorems formulated for de Bruijn indices).   
Both of these choices were guided in part by the initial choice of implementation language, Isabelle, which had good support both mechanizations. Isabelle was also chosen due to previous experience in mechanizing similar proofs.   
The comparison between nominal and locally nameless versions of the $\lamy$ calculus, presented in \cref{chap:compIsa}, tries to highlight the differences in the two approaches in contrast to the usual informal reasoning.

####Technology transparency

Technology transparency, as discussed here, is usually concerned with the presentation of the theory inside a proof assistant, such as Isabelle or Agda. As the snippets from \cref{Example:commNat} demonstrate, Agda includes features, such as Unicode support for mathematical symbols like $\mathbb{N}$, to make the implementation look more "natural". Other features, like Isabelle's proof representation language Isar (discussed in \cref{proofAsProg}), are built into theorem provers to try to make the proofs and definitions look as close to conventional notation as possible.

<div class="Example"> To demonstrate the Isar proof language and showcase the technology transparency it affords, we take the proof that a square of an odd number is itself odd\footnotemark:

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
  then have "n * n = ( 2 * k + 1) * ( 2 * k + 1)" by simp
  then have "n * n = (4 * k * k) + (4 * k) + 1" by simp
  hence     "n * n = 2 * ((2 * k * k) + (2 * k)) + 1" by simp
  thus "odd (n * n)" unfolding odd_def by blast
qed
~~~

Clearly, this mechanized proof reads much like the rigorous paper proof that precedes it.
</div>

\footnotetext{The proof was copied from \url{https://en.wikipedia.org/wiki/Direct_proof}}

This criterion of technology transparency is discussed mainly in \cref{chap:compAgda}, which deals with the comparison of Isabelle and Agda. The choice of the two theorem provers, but especially of Isabelle, was largely subjective. Having had previous experience with Isabelle, it was natural to use it initially, to lower the cost of entry. Initially only using Isabelle for both formalizations of binders also allowed for a more uniform comparison of the mechanization overheads.   
The choice of Agda as the second implementation language was motivated by Agda having a dependent-type system. As a result, the style of proofs in Agda seems quite different to Isabelle, since the distinction between proofs and programs is largely erased. Agda was chosen over Coq, which is also a dependently-typed language, because it is more "bare-bones" and thus seemed more accessible to a novice in dependently-typed languages. Agda also has a higher "cool"-factor than Coq, being a newer language.

####Proof automation

Proof automation ties into both the mechanization overheads and transparency aspects of a formalization, since high degree of automation can often result in a more natural/transparent looking proof where the "menial" reasoning steps are taken care of by the theorem prover, and the user only sees the higher-level reasoning of informal proofs.

**maybe link to \cref{Lemma:opnSwap}**

Both following chapters discuss the automation features of Isabelle and Agda and try to draw comparisons by analyzing the same/equivalent lemmas in different mechanizations and theorem provers, in terms of automation. Whilst on paper, Isabelle includes a lot more automation, in the form of several tactics and automated theorem provers, whereas Agda comes with only very simple proof search tactics, Agda's more sophisticated type-system takes on and replicates at least some of the automation seen in Isabelle.
