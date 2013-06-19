Leveling Up Dependent Types
===========================

Agda source code accompanying the draft paper (submitted to DTP 2013):

[Leveling Up Dependent Types - Generic programming over a predicative hierarchy of universes.](http://bit.ly/10chSXL)

Table of Contents
-----------------

* `Background`
  * A typical, small IR dependently typed universe.
  * Section 2 of the paper.
* `FixedHierarchy`
  * A dependently typed universe with some base types and a universe hierarchy.
  * The generic definition of `show`.
  * Sections 4 and 5 of the paper.
* `HList`
  * The hierarchical universe, extended with the large type `Hlist`.
  * The generic definition of `show`.
  * Section 6 of the paper.
* `OriginalDesc`
  * The original `Desc` definition as given by [Chapman et al.](https://personal.cis.strath.ac.uk/pierreevariste.dagand/stuffs/levitation.pdf)
  * Uses the large argument `Set`.
  * Section 7.1 of the paper.
* `ExtensibleHierarchy`
  * The hierarchical universe, extended with a `Desc`.
  * The generic definition of `show`, `double`, and `δouble`.
  * The generic interfaces `Generic` and `GenericΔ`.
  * Sections 7, 8, 9 and 10 of the paper.
