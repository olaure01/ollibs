# OLlibs
**Add-ons for the Rocq Standard Library**

Working with the `Rocq Prover 9.0`

[Opam](https://rocq-prover.org/docs/using-opam)-based installation procedure:

    $ opam repo add rocq-released https://rocq-prover.org/opam/released
    $ opam install rocq-ollibs

Manual installation procedure:

    $ ./configure
    $ make
    $ make install

## Extensions of Standard Library

* `Bool_more`       : add-ons for standard library Bool
* `Logic_Datatypes_more` : add-ons for core libraries Logic and Datatypes
* `Decidable_more` : add-ons for standard library Decidable
* `List_more`       : add-ons for standard library List
* `funtheory`       : properties of functions
* `dectype`         : types with decidable/Boolean equality (using records rather than modules)
* `infinite`        : infinite types
* `BOrders`         : `Orders` with output in `bool`
* `ComparisonOrder` : order structure on `comparison`
* `List_assoc`      : some operations on association lists
* `AFC`             : finite versions of the axiom of choice
* `nattree`         : nat-labelled trees and coding into nat
* `Wf_nat_more`     : well-founded order on products of `nat`
* `Vector_more`     : add-ons for standard library Vector
* `FinFun_more`     : add-ons for standard library FinFun (generalize finite sets to finite subsets)
* `SubList`         : sub-list of a list with no modification in order
* `Shuffle`         : shuffle predicate for pairs of lists
* `DecidableT`      : `Decidable` with output as a `sum` in `Type`
* `ListT`           : `List` with output in `Type`
* `inhabitedT`      : `inhabited` with output in `Type`
* `ShuffleT`        : `Shuffle` with output in `Type`

## Around Finite Multisets

* `fmsetlist`               : finite multisets with Rocq equality
* `fmsetoidlist`            : finite multisets as setoid
* `fmsetlistT`              : `fmsetlist` with output in `Type`
* `fmsetoidlistT`           : `fmsetoidlist` with output in `Type`

## Around Permutations

* `Permutation_more`        : add-ons for standard library Permutation
* `CPermutation_more`       : add-ons for standard library CPermutation
* `GPermutation`            : factorized common properties of
    * permutation and cyclic permutation
    * permutation and equality
    * permutation and cyclic permutation and equality
* `transp_perm`             : transpositions
* `PermutationT`            : `Permutation` with output in `Type`
* `PermutationT_more`       : `Permutation_more` with output in `Type`
* `CPermutationT`           : `CyclicPerm` with output in `Type`
* `GPermutationT`           : `genperm` with output in `Type`
* `Permutation_solve`       : automatic tactic for permutation goals
* `CPermutation_solve`      : automatic tactic for cyclic permutation goals
* `PermutationT_solve`      : `Permutation_solve` with output in `Type`
* `CPermutationT_solve`     : `CPermutation_solve` with output in `Type`

## Misc

* `flat_map_more`           : decomposition properties for `flat_map`
* `Dependent_ForallT`      : generalization of `Forall_inf` to dependent product
* `issue12394`              : work around for [Issue #12394](https://github.com/rocq-prover/rocq/issues/12394)

----

## Main contributors

* Olivier Laurent
* Christophe Lucas
