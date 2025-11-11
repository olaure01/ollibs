From Stdlib Require Export Decidable.
From OLlibs Require Import Logic_Datatypes_more.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.

Definition decidableP (P : Prop) := { P } + { ~ P }.

Lemma decP_dec P : decidableP P -> decidable P.
Proof. intros [|]; [left|right]; assumption. Qed.

Definition decidableT (P : Type) := (P + notT P)%type.

Lemma decP_decT (P : Prop) : decidableP P -> decidableT P.
Proof. intros [|]; [left|right]; assumption. Qed.

Lemma decT_decP (P : Prop) : decidableT P -> decidableP P.
Proof. intros [|]; [left|right]; assumption. Qed.

Lemma decT_decP_iffT (P : Prop) : iffT (decidableT P) (decidableP P).
Proof. split; [ apply decT_decP | apply decP_decT ]. Qed.

Lemma decT_dec (P : Prop) : decidableT P -> decidable P.
Proof. intros [|]; [left|right]; assumption. Qed.

Lemma decT_and (P Q : Prop) : decidableT P -> decidableT Q -> decidableT (P /\ Q).
Proof.
intros [HP|HnP] [HQ|HnQ]; [left|right; intros HPQ..].
- split; assumption.
- contradiction HnQ. apply HPQ.
- contradiction HnP. apply HPQ.
- contradiction HnQ. apply HPQ.
Qed.

Lemma decT_imp (P Q : Prop) : decidableT P -> decidableT Q -> decidableT (P -> Q).
Proof.
unfold decidableT. intros [HP|HnP] [HQ|HnQ]; [ auto | | auto | ].
- right. intros Himp. apply HnQ, Himp, HP.
- left. intros HP. contradiction.
Qed.

Lemma iff_decT P Q : (P <-> Q) -> decidableT P -> decidableT Q.
Proof.
intros [HPQ HQP] [HP|HnP]; [left|right].
- apply HPQ, HP.
- intros HP%HQP. contradiction HnP.
Qed.


(* TODO more use of [Stdlib.Classes.EquivDec], use class [EqDec _ eq]? *)
From Stdlib Require Import EquivDec.

Definition eq_decidableP A := forall x y : A, decidableP (x = y).

Section DecidableEquality.

Variable A B : Type.

Lemma eq_decT_eq_dec (eq_decT : forall x y : A, decidableT (x = y)) : eq_decidableP A.
Proof. intros x y. apply decT_decP, eq_decT. Qed.

Variable eq_decA : eq_decidableP A.

Lemma eq_dec_eq_decT (x y : A) : decidableT (x = y).
Proof using eq_decA. destruct (eq_decA x y) as [Heq | Hneq]; [ left | right ]; assumption. Qed.

#[deprecated(since="ollibs 2.1.1", use=Stdlib.Classes.EquivDec.option_eqdec)]
Lemma option_dec : eq_decidableP (option A).
Proof using eq_decA. apply option_eqdec. exact eq_decA. Qed.

#[deprecated(since="ollibs 2.1.1", use=Stdlib.Classes.EquivDec.list_eqdec)]
Lemma list_dec : eq_decidableP (list A).
Proof using eq_decA. apply list_eqdec. exact eq_decA. Qed.

Variable eq_decB : eq_decidableP B.

#[deprecated(since="ollibs 2.1.1", use=Stdlib.Classes.EquivDec.prod_eqdec)]
Lemma prod_dec : eq_decidableP (A * B).
Proof using eq_decA eq_decB. eapply prod_eqdec; assumption. Qed.

#[deprecated(since="ollibs 2.1.1", use=Stdlib.Classes.EquivDec.sum_eqdec)]
Lemma sum_dec : eq_decidableP (A + B).
Proof using eq_decA eq_decB. eapply sum_eqdec; assumption. Qed.

End DecidableEquality.
