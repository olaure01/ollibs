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


Section DecidableEquality.

Variable A B : Type.

Lemma eq_decT_eq_dec (eq_decT : forall x y : A, decidableT (x = y)) (x y : A) : decidableP (x = y).
Proof. apply decT_decP, eq_decT. Qed.

Variable eq_decA : forall x y : A, decidableP (x = y).

Lemma eq_dec_eq_decT (x y : A) : decidableT (x = y).
Proof using eq_decA. destruct (eq_decA x y) as [Heq | Hneq]; [ left | right ]; assumption. Qed.

Lemma option_dec (oa ob : option A) : decidableP (oa = ob).
Proof using eq_decA.
destruct oa as [a|], ob as [b|].
- destruct (eq_decA a b) as [-> | Hneq]; [ left; reflexivity| right ].
  intros [= ->]. contradiction Hneq. reflexivity.
- right. intros [=].
- right. intros [=].
- left. reflexivity.
Qed.

Variable eq_decB : forall x y : B, decidableP (x = y).

Lemma prod_dec (p q : A * B) : decidableP (p = q).
Proof using eq_decA eq_decB.
destruct p as (a1, b1), q as (a2, b2), (eq_decA a1 a2) as [ -> | HnA ], (eq_decB b1 b2) as [ -> | HnB ].
- left. reflexivity.
- right. intros Heq%(f_equal snd). cbn in Heq. contradiction.
- right. intros Heq%(f_equal fst). cbn in Heq. contradiction.
- right. intros Heq%(f_equal fst). cbn in Heq. contradiction.
Qed.

Lemma sum_dec (p q : A + B) : decidableP (p = q).
Proof using eq_decA eq_decB.
destruct p as [ p | p ], q as [ q | q ]; try (right; intros [=]; fail).
- destruct (eq_decA p q); [ left | right ]; [ subst p; reflexivity | intros [=]; contradiction ].
- destruct (eq_decB p q); [ left | right ]; [ subst p; reflexivity | intros [=]; contradiction ].
Qed.

End DecidableEquality.
