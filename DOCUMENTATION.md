# Short Description of Files Contents

## Extensions of [Standard Library](https://rocq-prover.org/refman-stdlib)

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
* `nattree`         : `nat`-labeled trees and coding into nat
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
* `CPermutationT`           : `CPermutation` with output in `Type`
* `GPermutationT`           : `GPermutation` with output in `Type`
* `Permutation_solve`       : automatic tactic for permutation goals
* `CPermutation_solve`      : automatic tactic for cyclic permutation goals
* `PermutationT_solve`      : `Permutation_solve` with output in `Type`
* `CPermutationT_solve`     : `CPermutation_solve` with output in `Type`

## Misc

* `flat_map_more`           : decomposition properties for `flat_map`
* `Dependent_ForallT`      : generalization of `ForallT` to dependent product
* `issue12394`              : work around for [Issue #12394](https://github.com/rocq-prover/rocq/issues/12394)


# Tactics

## Lists

Tactics for manipulating lists, equalities of lists, etc. are provided in `List_more`.

Below _l_ is a list, _p_ is a pattern, _H_ is an hypothesis, _t_ is any term, etc.

* `last_destruct` _l_ [`as` _p_]

  destructs the list _l_ into `nil` or `l' ++ a :: nil` (with _p_ = `[ | a l ']`)

  compare with `destruct l as [ | a l' ]` which destructs into `nil` or `a :: l'`

* `list_simpl` [`in` [_H_ | *]]

   flattens lists and also simplifies uses of `rev`, `map` and `flat_map` (`list_esimpl` is very similar, it might do a bit more job, but it might loop in presence of existential variables)

* `list_[e]reflexivity`

   reflexivity up to `list_[e]simpl`

* `cons2app` [`in` [_H_ | *]]

   constrains uses of `cons` (i.e. `::`): turn each `a :: l` into `[a] ++ l`

* `list_apply` _t_ [`in` _H_]

  similar to `apply` _t_ but the conclusion of _t_ is unified to the goal (resp. the hypothesis of _t_ is unified to _H_) up to `list_reflexivity` (which includes associativity, unit, etc. of list constructions)

* `decomp_nil_eq` _H_

   when _H_ is an equalty of the shape `nil = l` or `l = nil`, `l` is recursively analysed and decomposed into empty lists or a contradiction

* `decomp_unit_eq` _H_

   when _H_ is an equalty of the shape `[a] = l` or `l = [a]`, `l` is recursively analysed and decomposed into empty and singleton lists or a contradiction

* `decomp_app_eq_app` _H_

   when _H_ is an equalty of the shape `l1 ++ l2 = l3 ++ l4`, it is decomposed into the two possible cases: `l1` is a prefix of `l3` or `l3` is a prefix of `l1`

   (`decomp_app_eq_app_strict` is similar by giving three possible cases by distinguishing strict prefixes)

* `decomp_elt_eq_app` _H_

   when _H_ is an equalty of the shape `l1 ++ a ::  l2 = l3 ++ l4` (or `l3 ++ l4 = l1 ++ a ::  l2`), it is decomposed into the two possible cases: `a` is in `l3` or `a` is in `l4`

* `decomp_elt_eq_elt` _H_

   when _H_ is an equalty of the shape `l1 ++ a ::  l2 = l3 ++ b :: l4`, it is decomposed into the three possible cases: `a` is in `l3` (and `b` in `l2`) or `a` and `b` are the same occurrence or `a` is in `l4` (and `b` in `l1`)

* `decomp_elt_eq_app_app` _H_

   when _H_ is an equalty of the shape `l1 ++ a ::  l2 = l3 ++ l4 ++ l5` (or `l3 ++ l4 ++ l5 = l1 ++ a ::  l2`), it is decomposed into the three possible cases: `a` is in `l3` or `a` is in `l4` or `a` is in `l5`

* `decomp_map_eq` _H_

  when _H_ is an equalty of the shape `map f l1 = l2` (or `l2 = map f l1`), `l1` is decomposed to match the list structure (`cons`, `app`, etc.) of `l2`
  (the tactic might work better when the leaves of the list structure of `l2` are variables, so it might be useful to precook by using `remember` before applying `decomp_map_eq`) 

* `specialize_Forall` _H_ `with` _t_

  instantiate _H_ of type `Forall P l` with element _t_ (assuming an assumption `In t l` is in the context)

* `specialize_Forall_all` _t_

  apply `specialize_Forall` to all hypotheses of type `Forall _ _`

* `in_solve`

  automatic tactic for (an attempt of) solving statements about `In`

* `Forall[T]_solve`

  automatic tactic for (an attempt of) solving statements about `Forall[T]`


### Namings

* `nil` refers to the empty list
* `unit` refers to lists of the shape `[_]` (i.e. `_ :: nil`);
* `app` refers to lists of the shape `_ ++ _`;
* `elt` refers to lists of the shape `_ ++ _ :: _`;
* `app_app` refers to lists of the shape `_ ++ _ ++ _`;
* `map` refers to lists of the shape `map _ _`;
* `last` refers to the last element of a list or to a list of the shape `_ ++ [_]` (i.e. `_ ++ _ :: nil`);
* tactics `decomp_*_eq` and `decomp_*_eq_*` act on an equality hypothesis (with `*` describing the shapes on one or each side of the equality) and decompose it (most of such tactics work up to applying symmetry on the equality).

