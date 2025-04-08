From Stdlib Require Export Decidable.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.

Lemma iff_dec P Q : (P <-> Q) -> decidable P -> decidable Q.
Proof.
intros [HPQ HQP] [HP|HnP]; [left|right].
- apply HPQ, HP.
- intros HP%HQP. contradiction HnP.
Qed.
