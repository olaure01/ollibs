From Stdlib Require Import List CMorphisms.
From Stdlib Require Export Bool.
From OLlibs Require Import Logic_Datatypes_more DecidableT ListT.
Import LogicNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


Lemma dichot_bool_negb b1 b2 : {b1 = b2} + {b1 = negb b2}.
Proof. destruct b1, b2; (left + right); reflexivity. Qed.


(* ssr.ssrbool.negPP *)
Lemma reflect_neg P b : reflect P b -> reflect (not P) (negb b).
Proof. intros H. now inversion H; constructor. Qed.

(* ssr.ssrbool.andPP *)
Lemma and_andb_reflect P1 b1 P2 b2 : reflect P1 b1 -> reflect P2 b2 -> reflect (P1 /\ P2) (b1 && b2).
Proof. intros Hspec1 Hspec2. destruct b1, b2; cbn; constructor; inversion Hspec1; inversion Hspec2; tauto. Qed.

(* ssr.ssrbool.orPP *)
Lemma or_orb_reflect P1 b1 P2 b2 : reflect P1 b1 -> reflect P2 b2 -> reflect (P1 \/ P2) (b1 || b2).
Proof. intros Hspec1 Hspec2. destruct b1, b2; cbn; constructor; inversion Hspec1; inversion Hspec2; tauto. Qed.

(* ssr.ssrbool.implyPP *)
Lemma impl_implb_reflect P1 b1 P2 b2 : reflect P1 b1 -> reflect P2 b2 -> reflect (P1 -> P2) (implb b1 b2).
Proof. intros Hspec1 Hspec2. destruct b1, b2; cbn; constructor; inversion Hspec1; inversion Hspec2; tauto. Qed.


(** * ReflectT *)

Variant reflectT P : bool -> Type :=
| ReflectTT : P -> reflectT P true
| ReflectTF : notT P -> reflectT P false.
#[global] Hint Constructors reflectT : bool.

Lemma reflectT_reflect (P : Prop) b : reflectT P b <=> reflect P b.
Proof. split; intros []; constructor; assumption. Qed.

(* TODO current choice for Hint cost is random... *)
#[export] Instance reflectT_iffT_compat : Proper (iffT ==> eq ==> iffT) reflectT | 10.
Proof. intros P Q [HPQ HQP] u v <-. split; (intros [ | HnP ]; constructor; [ | intro; apply HnP ]); auto. Qed.
#[export] Instance reflectT_CiffT_compat :
  Proper (CRelationClasses.iffT ==> eq ==> CRelationClasses.iffT) reflectT | 10.
Proof. intros P Q [HPQ HQP] u v <-. split; (intros [ | HnP ]; constructor; [ | intro; apply HnP ]); auto. Qed.

Lemma reflectT_iffT P b : reflectT P b -> iffT P (b = true).
Proof. now destruct 1; split; [ | | | discriminate ]. Qed.

Lemma iffT_reflectT P b : iffT P (b = true) -> reflectT P b.
Proof.
intros Hiff. destr_bool; constructor.
- apply Hiff. reflexivity.
- intros HP. apply Hiff in HP as [=].
Defined.

Lemma reflectT_decT P b : reflectT P b -> decidableT P.
Proof. intros [|]; [ left | right ]; assumption. Defined.

Lemma decT_reflectT P (HdecT : decidableT P) : reflectT P (if HdecT then true else false).
Proof. destruct HdecT; constructor; assumption. Qed.

Lemma eqb_specT b b' : reflectT (b = b') (eqb b b').
Proof. destruct b, b'; constructor; (constructor + intros [=]). Defined.

Lemma reflectT_neg P b : reflectT P b -> reflectT (notT P) (negb b).
Proof. intros H. now inversion H; constructor. Qed.

Lemma and_andb_reflectT P1 b1 P2 b2 : reflectT P1 b1 -> reflectT P2 b2 -> reflectT (P1 * P2) (b1 && b2).
Proof.
intros Hspec1 Hspec2.
destruct b1, b2; cbn; constructor; inversion Hspec1; inversion Hspec2; try intro; intuition.
Qed.

Lemma or_orb_reflectT P1 b1 P2 b2 : reflectT P1 b1 -> reflectT P2 b2 -> reflectT (P1 + P2) (b1 || b2).
Proof.
intros Hspec1 Hspec2.
destruct b1, b2; cbn; constructor; inversion Hspec1; inversion Hspec2; try intro; intuition.
Qed.

Lemma impl_implb_reflectT P1 b1 P2 b2 : reflectT P1 b1 -> reflectT P2 b2 -> reflectT (P1 -> P2) (implb b1 b2).
Proof.
intros Hspec1 Hspec2.
destruct b1, b2; cbn; constructor; inversion Hspec1; inversion Hspec2; try intro; intuition contradiction.
Qed.

Lemma ForallT_filter A f P (l : list A) :
  (forall a, reflectT (P a) (f a)) -> ForallT P (filter f l).
Proof.
intros Hspec. induction l as [|a l IHl]; cbn; [ constructor | ].
destruct (Hspec a); [ constructor | ]; assumption.
Qed.
