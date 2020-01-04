(* wf_prod Library *)

(** * Well-founded order on product and applications to products of nat *)

Require Import Relation_Definitions Relation_Operators Wellfounded Wf_nat Lia.


(** * Non-Dependant Product of two [well_founded] relations *)

Section Product.

Variable A B : Type.
Variable RA : relation A.
Variable RB : relation B.
Hypothesis WA : well_founded RA.
Hypothesis WB : well_founded RB.

Definition lt_prod v1 v2 := lexprod _ _ RA (fun _ => RB) v1 v2.
Definition wf_prod := wf_lexprod _ _ _ _ WA (fun _ => WB).

End Product.


(** * Well founded order on pairs of [nat] *)

Definition lt_nat_nat := lexprod _ _ lt (fun _ => lt).
Definition wf_nat_nat := wf_lexprod _ _ _ _ lt_wf (fun _ => lt_wf).

Ltac lt_nat_nat_solve :=
  match goal with
  | |- lt_nat_nat ?v1 ?v2 => try (left; simpl; lia);
                             try (right; split; simpl; lia);
                             fail
  | |- lt_prod _ _ lt lt ?v1 ?v2 => try (left; simpl; lia);
                                    try (right; split; simpl; lia);
                                    fail
  end.

(** * Well founded order on triples of [nat] *)

Definition lt_nat_nat_nat := lt_prod _ _ lt lt_nat_nat.
Definition wf_nat_nat_nat := wf_prod _ _ _ _ lt_wf wf_nat_nat.

Ltac lt_nat_nat_nat_solve :=
  match goal with 
  | |- lt_nat_nat_nat ?v1 ?v2 =>
     try (left; simpl; lia);
     try (right; split; [ | left ]; simpl; lia);
     try (right; split; [ | right; split ]; simpl; lia);
     fail
  | |- lt_prod _ _ lt lt_nat_nat ?v1 ?v2 =>
     try (left; simpl; lia);
     try (right; split; [ | left ]; simpl; lia);
     try (right; split; [ | right; split ]; simpl; lia);
     fail
  | |- lt_prod _ _ lt (lt_prod _ _ lt lt) ?v1 ?v2 =>
     try (left; simpl; lia);
     try (right; split; [ | left ]; simpl; lia);
     try (right; split; [ | right; split ]; simpl; lia);
     fail
  end.

