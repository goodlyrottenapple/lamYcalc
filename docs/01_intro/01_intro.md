#Introduction

##Motivation

Formal verification of software is essential in a lot of safety critical systems in the industry and has been a field of active research in computer science. One of the main approaches to verification is model checking, wherein a system specification is checked against certain correctness properties, by generating a model of the system, encoding the desired correctness property as a logical formula and then exhaustively checking whether the given formula is satisfiable in the model of the system. Big advances in model checking of 1^st^ order (imperative) programs have been made, with techniques like abstraction refinement and SAT/SMT-solver use, allowing scalability.   
Aspects of functional programming, such as anonymous/$\lambda$ functions have gained prominence in mainstream languages, such as C++ or JavaScript and functional languages like Scala, F# or Haskell have garnered wider interest. With growing interest in using functional programming, interest in verifying higher-order functional programs has also grown. Current approaches to formal verification of such programs usually involve the use of (automatic) theorem provers, which usually require a lot of user interaction and as a result have not managed to scale as well as model checking in the 1^st^ order setting.    
Using type systems is another way to ensure program safety, but using expressive-enough types often requires explicit type annotations, since type checking/inference usually becomes undecidable, as is the case for dependent-type systems. Simpler type systems, where type inference is decidable, can instead prove too coarse, i.e. the required properties are difficult if not impossible to capture in such type systems.    
In recent years, advances in higher order model checking (HOMC) have been made (@ong06, @kobayashi13, @ramsay14, @tsukada14), but whilst a lot of theory has been developed for HOMC, there has been little done in implementing/mechanizing these results in a fully formal setting of a theorem prover.   


##Aims
The aim of this project is to make a start of mechanizing the proofs underpinning HOMC approaches using type-checking of higher-order recursion schemes, by formalizing and formally proving certain key properties about the $\lamy$ calculus with the intersection-type system described by **??which one...should I omit??**, which can be used to study HOMC as an alternative to higher order recursion schemes (HORS).    
The first part of this work focuses on the mechanization aspect of the simply typed $\lamy$ calculus in a theorem prover, in a fashion similar to the $\poplm$ challenge, by exploring different encodings of binders in a theorem prover and also the use of different theorem provers. The reason why we chose to do such a comparison was to evaluate and chose the best mechanization approach and implementation language for the $\lamy$ calculus, as there is little infomration available concerning the merits and disadvantages of different implementation approaches of $\lamy$ or indeed just the (simply typed) $\lambda$-calculus. The comparison of different mechanizations focuses on the engineering choices and formalization overheads which result from translating the informal definitions into a fully-formal setting of a theorem prover.
The project is roughly split into two main parts, with the first part exploring and evaluating the different formalizations of the simply-typed $\lamy$ calculus together with the proof of the Church Rosser Theorem. The reason why we chose to formalize the Church Rosser theorem was to to test the implementation of a non-trivial, but simple enough proof in a fully formal setting.   
The second part focuses on implementing the intersection-type system for the $\lamy$ calculus and formalizing the proof of subject invariance for this type system. The formalization and engineering choices made in the implementation of the intersection-type system reflect the survey and analysis of the different possible choices of mechanization, explored in the first part of the project.

##Main Achievements

**TODO: Expand on the points eventually....leaving for the end**

-	Formalization of the simply typed $\lamy$ calculus and proofs of confluence in Isabelle, using both Nominal sets and locally nameless encoding of binders.
-	Formalization of the simply typed $\lamy$ calculus and proofs of confluence in Agda, using a locally nameless encoding of binders
-	Analysis and comparison of binder encodings
-	Comparison of Agda and Isabelle
-	Formalization of an intersection-type system for the $\lamy$ calculus and proof of subject invariance for intersection-types

