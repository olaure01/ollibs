(* Bool_more Library *)

(** * Add-ons for Bool library *)

Require Export Bool.

Require Import Eqdep_dec.

(** * Uniqueness of Identity Proofs (UIP) at [bool] type *)
Definition UIP_bool2 := UIP_dec bool_dec.

(* alternative direct proof:)
(* begin hide *)
Lemma eq_refl_bool_ext : forall b1 b2 : bool, b1 = b2 -> b1 = b2.
Proof. destruct b1, b2; intros; ( reflexivity || assumption ). Defined.
(* end hide *)

Lemma UIP_bool : forall (b1 b2 : bool) (f1 f2 : b1 = b2), f1 = f2.
Proof.
intros b1 b2 f1 f2.
assert (forall f, f = eq_refl_bool_ext b1 b2 f1) as Heq
  by (destruct f; revert f1; destruct b1; reflexivity).
rewrite (Heq f1), (Heq f2); reflexivity.
Qed.
*)
