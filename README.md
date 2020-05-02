# ollibs
Add-ons for the Coq Standard Library

Working with `Coq 8.11.0`

## Misc

* `AFC`          : proofs of finite versions of the axiom of choice
* `Bool_more`    : add-ons for standard library Bool
* `dectype`      : types with decidable/Boolean equality (using records rather than modules)
* `fmsetlist`    : finite multisets with Coq equality
* `fmsetoidlist` : finite multisets as setoid
* `funtheory`    : properties of functions
* `infinite`     : infinite types
* `List_more`    : add-ons for standard library List
* `List_assoc`   : some operations on association lists
* `nattree`      : nat-labelled trees and coding into nat
* `Vector_more`  : add-ons for standard library Vector
* `Wf_nat_more`  : add-ons for standard library Wf_nat
* `wf_prod`      : well-founded order on product (application to `nat`)

## More About Permutations

* `CPermutation_solve` : automatic tactic for cyclic permutation goals
* `CyclicPerm`         : library for cyclic permutations
* `genperm`            : factorized common properties of
    * permutation and cyclic permutation
    * permutation and equality
* `Permutation_more`   : add-ons for standard library Permutation
* `Permutation_solve`  : automatic tactic for permutation goals

## Standard Library Adapted with output in `Type` (rather than `Prop`)

* `CEqualities`  : `Equalities` with output in `Type`
* `COrders`      : `Orders` with output in `Type`
* `List_Type`               : `List` with output in `Type`

## Around Permutations with output in `Type`

* `CPermutation_Type_solve` : `CPermutation_solve` with output in `Type`
* `CyclicPerm_Type`         : `CyclicPerm` with output in `Type`
* `genperm_Type`            : `genperm` with output in `Type`
* `Permutation_Type_more`   : `Permutation_more` with output in `Type`
* `Permutation_Type_solve`  : `Permutation_solve` with output in `Type`
* `Permutation_Type`        : `Permutation` with output in `Type`
* `PermutationPropify`      : turn `Permutation_Type` into `Permutation` for types with decidable equality
* `transp_perm`             : transpositions

## Misc with output in `Type`

* `Dependent_Forall_Type`   : generalization of `Forall_Type` to dependent product
* `flat_map_Type_more`      : decomposition properties for `flat_map`
* `fmsetlist_Type`          : `fmsetlist` with output in `Type`
* `fmsetoidlist_Type`       : `fmsetoidlist` with output in `Type`
* `List_Type_more`          : `List_more` with output in `Type`

