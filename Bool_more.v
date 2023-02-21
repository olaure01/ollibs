(* TODO submit to stdlib *)

From Coq Require Export Bool.
From OLlibs Require Import List_Type.

Lemma reflect_neg P b : reflect P b -> reflect (not P) (negb b).
Proof. intros H. now inversion H; constructor. Qed.


Inductive reflectT (P : Type) : bool -> Type :=
  | ReflectTT : P -> reflectT P true
  | ReflectTF : notT P -> reflectT P false.
#[global] Hint Constructors reflectT : bool.

Lemma reflectT_iffT P b : reflectT P b -> iffT P (b = true).
Proof. now destruct 1; split; [ | | | discriminate ]. Qed.

Lemma iffT_reflectT P b : iffT P (b = true) -> reflectT P b.
Proof.
intros Hiff. destr_bool; constructor.
- apply Hiff. reflexivity.
- intros HP. apply Hiff in HP as [=].
Defined.

Lemma reflectT_dec P b : reflectT P b -> P + notT P.
Proof. intros [|]; [ left | right ]; assumption. Defined.

Lemma eqb_specT b b' : reflectT (b = b') (eqb b b').
Proof. destruct b, b'; now constructor. Defined.

Lemma reflectT_neg P b : reflectT P b -> reflectT (notT P) (negb b).
Proof. intros H. now inversion H; constructor. Qed.
