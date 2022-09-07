# Versions 2.0.x

## Version 2.0.3

Ongoing development.

* `arrow`
    * do not export `Program.Basics` in `funtheory` anymore
    * rely on `Classes.CRelationClasses.arrow` rather than `Program.Basics.arrow` for `Proper` instances in `Type`
* turn `#[global]` instances into `#[export]` ones
* rename `wf_prod.v` into `Wf_nat_more.v`
    * use the non-dependent product order from Coq stdlib (introduced in [PR #14809](https://github.com/coq/coq/pull/14809))

## Version 2.0.2

* add function constructions for `Empty_set` and `option` in `funtheory`
* adapt to Coq v8.14 and v8.15
    * add locality attributes to `Instance` commands

## Version 2.0.1

* proof scripts more robust with respect to automatically generated names
* slightly more powerful `unit_vs_elt_inv` tactic
* adapt to Coq v8.13.0
    * remove statements about `repeat` (moved into Coq stdlib: [PR #12799](https://github.com/coq/coq/pull/12799))
    * add locality attributes to `Hint` commands


## Version 2.0.0

First Opam-released version.

It coincides with incorporation of part of previous content into the standard library of Coq v8.12.0.
