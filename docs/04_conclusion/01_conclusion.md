#Conclusion
\label{chap:concl}

This project has achieved two main goals, the first of which was to assess viable approaches and available tools for formalizing a typed $\lambda$-calculus inside a theorem prover. The second aim of this project was to create the basis for a full formalization of the HOMC theory, by implementing the $\lamy$ calculus with intersection types.    
Whilst, these two aims were successful, there is space for improvement and further work in both stated aims.

##Limitations of the current approach

A major limiting factor for doing a comparison more similar to the $\poplm$ challenge, was obviously the time constraint of this project. Due to the limited number of comparisons and theorem provers tested, this comparison cannot hope to give a wide overview of the current technology and techniques, used for similar mechanizations.    
Whilst the comparisons focus on transparency of definitions, there is less of a discussion of transparency of proofs. Even though \cref{chap:compAgda} describes the different approaches to mechanizing proofs in Isabelle and Agda, the question of which of these approaches is more transparent has not been explored to a great extent. This question is perhaps a slightly philosophical one, as it touches on what constitutes a proof, as well as what a proof should look like.     
Another point of concern is the previously discussed "porting" of the proofs from the nominal to the locally nameless version of the calculus. Whilst we chose to "port" the theory over, keeping as much structure identical as possible, this might have inadvertently created overheads in the locally nameless mechanization, which were not necessary (like having two versions of lemmas, one defined for substitution and one for the _open_ operation).    
However, the main drawback, in our view, is the relatively fragile implementation of intersection types and the proofs of subject invariance. Whilst this was not discussed at length, the mechanization at this stage proved to be a lot more difficult to formalize than the previously implemented proof of confluence, since the definitions of the intersection types and typing rules changed several times, breaking most of the proofs each time.    


##Future work

Having a solid basis for the theory of HOMC, underpinned by the $\lamy$ calculus, the wider scope of this mechanization would include the implementation of a decision procedure for the normalizability of $\lamy$ terms, which is an important result in the HOMC theory. As was mentioned in \cref{chap:compAgda}, the choice of Agda for the mechanization of intersection types and proofs of subject invariance was in fact motivated (in part) by the extension of the mechanization to this result.
