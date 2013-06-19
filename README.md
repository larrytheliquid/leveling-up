Leveling Up Dependent Types
===========================

Agda source code accompanying the draft paper (submitted to DTP 2013):

[Leveling Up Dependent Types - Generic programming over a predicative hierarchy of universes.](http://bit.ly/10chSXL)

Code from the paper
-------------------

* [`Paper.Background`](src/Paper/Background.agda)
  * A typical, small IR dependently typed universe.
  * Section 2 of the paper.
* [`Paper.FixedHierarchy`](src/Paper/FixedHierarchy.agda)
  * A dependently typed universe with some base types and a universe hierarchy.
  * The generic definition of [`show`](src/Paper/FixedHierarchy.agda#L99).
  * Sections 4 and 5 of the paper.
* [`Paper.HList`](src/Paper/HList.agda)
  * The hierarchical universe, extended with the large type [`Hlist`](src/Paper/HList.agda#L12).
  * The generic definition of [`show`](src/Paper/HList.agda#L96).
  * Section 6 of the paper.
* [`Paper.OriginalDesc`](src/Paper/OriginalDesc.agda)
  * The original [`Desc`](src/Paper/OriginalDesc.agda#L12) construction as given by [Chapman et al.](https://personal.cis.strath.ac.uk/pierreevariste.dagand/stuffs/levitation.pdf)
  * Uses the large argument `Set`.
  * Section 7.1 of the paper.
* [`Paper.ExtensibleHierarchy`](src/Paper/ExtensibleHierarchy.agda)
  * The hierarchical universe, extended with the [`Desc`](src/Paper/ExtensibleHierarchy.agda#L21) construction.
  * The generic definition of [`show`](src/Paper/ExtensibleHierarchy.agda#L100), [`double`](src/Paper/ExtensibleHierarchy.agda#L254), and [`δouble`](src/Paper/ExtensibleHierarchy.agda#L311).
  * The generic interfaces [`Generic`](src/Paper/ExtensibleHierarchy.agda#L370) and [`GenericΔ`](src/Paper/ExtensibleHierarchy.agda#L424).
  * Sections 7, 8, 9 and 10 of the paper.

The underlying type theory
--------------------------

* [`TT.DenotationalTerms`](src/TT/DenotationalTerms.agda)
  * A denotational semantics for terms, or terms with an implicit context.
* [`TT.OperationalTerms`](src/TT/OperationalTerms.agda)
  * An operational semantics for terms, or terms with an explicit context.   
  * This extends [McBride's type-safe syntax and evaluation](https://personal.cis.strath.ac.uk/conor.mcbride/pub/DepRep/DepRep.pdf) to include a universe hierarchy.
  * Compared to McBride's types and terms, here the types and terms (and descriptions) are in a single grammar/datatype.


