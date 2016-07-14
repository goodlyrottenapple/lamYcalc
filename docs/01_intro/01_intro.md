#Introduction

##Motivation

Formal verification of software is essential in a lot of safety critical systems in the industry and has been a field of active research in computer science. One of the main approaches to verification is model checking, wherein a system specification is checked against certain correctness properties, by generating a model of the system, encoding the desired correctness property as a logical formula and then exhaustively checking whether the given formula is satisfiable in the model of the system. Big advances in model checking of 1\textsuperscript{st} order (imperative) programs have been made, with techniques like abstraction refinement and SAT/SMT-solver use, allowing scalability.   
Since aspects of functional programming, such as anonymous/$\lambda$ functions have gained prominence in mainstream languages such as C++ or JavaScript and functional languages like Scala, F# or Haskell have garnered wider interest, interest in verifying higher-order functional programs has also grown. Current approaches to formal verification of such programs usually involve the use of (automatic) theorem provers, which usually require a lot of user interaction and as a result have not managed to scale as well as model checking in the 1\textsuperscript{st} order setting. Using type systems is another way to ensure program safety, but using expressive-enough types often requires explicit type annotations, as is the case for dependent-type systems. Simpler type systems where type inference is decidable can instead prove too coarse, i.e. the required properties are difficult to capture in such type systems. In recent years, advances in higher order model checking (HOMC) have been made (@kobayashi13, @ramsay14, @tsukada14), but whilst a lot of theory has been developed for HOMC, there has been little done in implementing/mechanizing these results in a fully formal setting of a theorem prover.   


##Aims
The aim of this project is to make a start of mechanizing the proofs underpinning HOMC approaches using type-checking of higher-order recursion schemes, by formalizing the $\lamy$ calculus with the intersection-type system described by ? and formally proving certain key properties of the system.   
The first part of this work focuses on the mechanization aspect of the simply typed $\lamy$ calculus in a theorem prover, in a fashion similar to the $\poplm$ challenge, by exploring different encodings of binders in a theorem prover and also the use of different theorem provers. The project focuses on the engineering choices and formalization overheads which result from translating the informal definitions into a fully-formal setting of a theorem prover.
The project is split into roughly two main parts, witht he first part exploring and evaluating different formalizations of the simply-typed $\lamy$ calculus together with the proof of the Church Rosser Theorem. The second part focuses on implemnting the interestion-type system for the $\lamy$ calculus and formalizing the proof of subject invariance for this type system. The formalization and engineering choices made in the implementation of the intersection-type system reflect the survey and analysis of the different possible choices of mechanization, explored in the first part of the project.

##Main Achievements

-	Formalization of the simply typed $\lamy$ calculus and proofs of confluence in Isabelle, using both Nominal sets and locally nameless encoding of binders.
-	Formalization of the simply typed $\lamy$ calculus and proofs of confluence in Agda, using a locally nameless encoding of binders
-	Analysis and comparison of binder encodings
-	Comparison of Agda and Isabelle
-	Formalization of an intersection-type system for the $\lamy$ calculus and proof of subject invariance for intersection-types

