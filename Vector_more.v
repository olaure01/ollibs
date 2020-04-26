(* Vector_more Library *)

(** * Add-ons for Vector library
Usefull properties apparently missing in the Vector library. *)

(*
Require Export Vector.
Require Import PeanoNat Eqdep_dec.

Lemma inj_pairT2_nat : forall (P:nat -> Type) p x y,
  existT P p x = existT P p y -> x = y.
Proof. apply inj_pair2_eq_dec, Nat.eq_dec. Qed.
*)

(* TODO useless ?
Lemma case0_nil {A} : forall (v : t A 0) P, P (nil A) -> P v.
Proof. intros; now apply case0. Qed.
*)

(* TODO easy consequence of Forall_impl
Lemma inc_Forall A: forall (P : nat -> A -> Prop) n (v : t A n) i j,
  (forall i j a, P i a -> i <= j -> P j a) ->
  Forall (P i) v -> i <= j -> Forall (P j) v.
Proof.
intros P n v i j Hinc HP Hle.
now apply (Forall_impl _ (P i) (P j)); intuition (apply Hinc with i).
Qed.
(*
Proof.
intros P n v i j Hinc.
induction v; intros H Hv; constructor; inversion H.
- now apply Hinc with i.
- apply (inj_pair2_eq_dec _ Nat.eq_dec) in H2; subst; auto.
Qed.
*)
*)
