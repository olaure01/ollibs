# Versions 2.1.x

## Version 2.1.0

Ongoing development.

* use names ending with `T` rather than `_Type` or `_inf` (for files and statements)
* add `DecidableT.v` with type `decidableT`
  * add results about decidable properties
  * more uniform naming
  * add `Decidable_more.v`
  * rename `decidable_image` into `decT_image`
* rename `Datatypes_more.v` into `Logic_Datatypes_more.v` containing extensions for both `Corelib.Logic` and `Corelib.Datatypes`
* more use of `iffT` for equivalence statements in `Type`
* more use of `notT` for negation in `Type`
* add new lemmas
  * `funtheory` : more about `ext_eq`
  * `List_more` : `Forall_impl`, `Forall_remove*`, `Forall_solve`, `incl_preorder`
  * `Logic_Datatypes_more` : `sum_*`, `prod_*`
  * `PermutationT` : `PermutationT_repeat`
  * `SubList` : `sublist_Add`, `sublist_preorder`, `sublist_antisym'`, `uniquify*_sublist`


# Versions 2.0.x

## Version 2.0.8

* fully compatible with name mangling
* add `SubList.v`
* add `Shuffle.v` and `ShuffleT.v`
* add `ext_eq` in `funtheory.v` for extensional equality of functions
* add `self_option_bijective` in `infinite.v`
* add new lemmas
  * `Datatypes_more` : `is_Some`
  * `Boole_more` : `dichot_bool_negb`, `Forall_inf_filter`
  * `List_more` : `list_sum_repeat`, `Forall_filter`, `incl_cons_cons`, `NoDup_unit`, `NoDup_app_remove`, `NoDup_remove_iff`, `last_cons_default`, `last_elt`, `in_last`
  * `Permutation_*` : `Permutation_*_concat`, `Permutation_*_forallb`, `Permutation_incl`
  * `CPermutation_*` : `CPermutation_*_concat`, `CPermutation_*_flat_map`, `CPermutation_*_length_3_inv`, `CPermutation_*_cons_cons_inv`
  * `Borders`: `Permutation_insert`
* renaming of some tactics
  * `nil_vs_elt_inv` becomes `decomp_nil_eq_elt`
  * `unit_vs_elt_inv` becomes `decomp_unit_eq_elt`
  * `dichot_app_exec` becomes `decomp_app_eq_app`
  * `dichot_elt_app_exec` becomes `decomp_elt_eq_app`
  * `trichot_elt_app_exec` becomes `decomp_elt_eq_app_app`
  * `trichot_elt_elt_exec` becomes `decomp_elt_eq_elt`
* renaming of lemmas using `_vs_` into `_eq_`
* remove useless property `elts_empty` in `FinMultiset`
* remove `PermutationPropify.v` (now possible to replace with setoid_rewriting)
* more uses of `crelation A` rather than `A -> A -> Type`
* more uses of `sigT2` rather than `sigT` with `prod` in `flat_map_more.v`
* cleaned statement of `transp_decomp` in `transp_perm.v`
* adapt to Rocq v9.0
  * turn `From Coq` into `From Stdlib`
  * use `:>` for coercion with `Class`
  * use `rocq makefile`

## Version 2.0.7

* adapt to Coq v8.20
  * rename some `_length` into `length_`

## Version 2.0.6

* changes on tactics in `List_more.v`
  * add `as`, `in` and `in *` extensions
  * try to preserve names in `decomp_map`
  * add symmetric cases for matching equalities
  * rename `Forall_inf_cbn_hyp` into `Forall_inf_simpl_hyp`
  * WARNING: this impacts automatically generated names (in a way which should be more stable)
* create dedicated file `Vector_more.v` for results using `Vector`
  * rename `AFCvec_incdep` into `AFCincdep` in `AFC.v`
  * move `AFCvec` from `AFC.v` to `Vector_more.v`
* add `Set Implicit Arguments` in most files
* more uses of `sigT2` rather than `sigT` with `prod` in `List_more.v`
* move `fold_id` to `List_more.v`
* adapt to Coq v8.19
  * remove uses of `auto with arith`

## Version 2.0.5

* rename `decomp_length_plus` into `decomp_length_add`
* more uses of `sig2` rather than `sig` with `/\` in `List_more.v`
* add tactics `nil_vs_elt_inv` and `last_destruct` for lists
* add `Forall2_rev` and `Forall2_inf_rev`
* remove statements already present in the standard library
* adapt to Coq v8.18
  * remove `Let` constructs in `Permutation_Type.v`

## Version 2.0.4

* rename `fresh_prop` into `fresh_spec`
* correct arguments in tactic `case_analysis`
* turn some `_ -> False` into `notT _`
* add `PCPermutation_Type_app_flat_map`, `injective_neq` and `section_coimage_option`
* add results on `filter` and `partition`
* add automatic tactics `in_solve` and `Forall_inf_cbn_hyp` for lists
* create `Datatypes_more.v`
    * add `iffT`, `prod_map` and `prod_map2`
* create `Bool_more.v`
    * add `reflectT` and associated results
	* add `reflect_neg`, `Forall_forallb_reflect` and some results from `ssr.ssrbool`
* integrate material for dealing with [Issue #12394](https://github.com/coq/coq/issues/12394) in file `issue12394.v`
* adapt to Coq v8.17
    * clean uses of tactic `intuition`
    * remove `Forall2_length` (integrated in the standard library in [PR #15986](https://github.com/coq/coq/pull/15986))

## Version 2.0.3

* `arrow`
    * do not export `Program.Basics` in `funtheory` anymore
    * rely on `Classes.CRelationClasses.arrow` rather than `Program.Basics.arrow` for `Proper` instances in `Type`
* turn `#[global]` instances into `#[export]` ones
* rename `wf_prod.v` into `Wf_nat_more.v`
    * use the non-dependent product order from Coq stdlib (introduced in [PR #14809](https://github.com/coq/coq/pull/14809))
* create separated file `inhabited_Type.v`
* add `option_test`, `Permutation_vs_elt_subst`, `decidable_image` (and associated properties), `in_inf_prod_inv` and `eqb_sym`
* simplify `cpair_surj` hypothesis in `nattree.v`
* adapt to Coq v8.16
    * setoid_rewriting is more powerful (not backward compatible)

## Version 2.0.2

* add function constructions for `Empty_set` and `option` in `funtheory`
* adapt to Coq v8.14 and v8.15
    * add locality attributes to `Instance` commands

## Version 2.0.1

* proof scripts more robust with respect to automatically generated names
* slightly more powerful `unit_vs_elt_inv` tactic
* adapt to Coq v8.13
    * remove statements about `repeat` (moved into Coq stdlib: [PR #12799](https://github.com/coq/coq/pull/12799))
    * add locality attributes to `Hint` commands

## Version 2.0.0

First Opam-released version.

It coincides with incorporation of part of previous content into the standard library of Coq v8.12.
