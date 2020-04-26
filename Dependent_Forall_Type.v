(* Dependent_Forall_Type Library *)

(** * Generalization of Forall_Type to dependent product *)

Require Import List_more.
Require Export Eqdep_dec.

Set Implicit Arguments.

Inductive Dependent_Forall_inf A (P : A -> Type) (Pred : forall a, P a -> Type) :
   forall {l}, Forall_inf P l -> Type :=
| Dependent_Forall_inf_nil : Dependent_Forall_inf Pred (Forall_inf_nil P)
| Dependent_Forall_inf_cons : forall a {l} Pa (Fl : Forall_inf P l), (Pred a Pa) ->
           Dependent_Forall_inf Pred Fl -> Dependent_Forall_inf Pred (Forall_inf_cons a Pa Fl).

Section Eq_Dec.
  Context {A : Type}.
  Hypothesis eq_dec : forall (x y : A), {x = y} + {x <> y}.

  Lemma Dependent_Forall_inf_forall : forall (P : A -> Type) Pred,
    forall l a Pa (Fl : Forall_inf P l),
      Dependent_Forall_inf Pred Fl -> In_Forall_inf a Pa Fl -> Pred a Pa.
  Proof with try assumption.
    intros P Pred l a Pa Fl DFl; revert a Pa;
     induction DFl; intros a' Pa' Hin; inversion Hin.
    - inversion H; subst.
      apply inj_pair2_eq_dec in H2...
      rewrite H2...
    - apply IHDFl...
  Qed.

  Lemma forall_Dependent_Forall_inf : forall (P : A -> Type) Pred,
      forall {l} (Fl : Forall_inf P l),
        (forall a Pa, In_Forall_inf a Pa Fl -> Pred a Pa) ->
        Dependent_Forall_inf Pred Fl.
  Proof with try assumption.
    intros P Pred l Fl; induction Fl; intros f.
    - apply Dependent_Forall_inf_nil.
    - apply Dependent_Forall_inf_cons.
      + apply f.
        left; reflexivity.
      + apply IHFl.
        intros a Pa Hin.
        apply f.
        right...
  Qed.

  Lemma Dependent_Forall_inf_inv : forall (P : A -> Type) Pred a l Pa (Pl : Forall_inf P l),
    Dependent_Forall_inf Pred (Forall_inf_cons a Pa Pl) -> Pred a Pa.
  Proof with try assumption.
    intros P Pred a l Pa Pl DPl.
    inversion DPl; subst.
    replace Pa with Pa0...
    apply inj_pair2_eq_dec...
  Qed.

  Lemma Dependent_Forall_Type_dec : forall (P :A -> Type) Pred,
      (forall a Pa, Pred a Pa + (Pred a Pa -> False)) ->
      forall l (Fl : Forall_inf P l),
        Dependent_Forall_inf Pred Fl + (Dependent_Forall_inf Pred Fl -> False).
  Proof with try assumption.
    intros P Pred dec_Pred l Fl; induction Fl.
    - left.
      apply Dependent_Forall_inf_nil.
    - destruct IHFl as [HFl | HFl].
      + destruct dec_Pred with x p as [HPa | HnPa].
        * left.
          apply Dependent_Forall_inf_cons...
        * right.
          intro DFl; inversion DFl.
          apply HnPa.
          replace p with Pa...
          apply inj_pair2_eq_dec...
      + right.
        intro DFl; inversion DFl.
        apply inj_pair2_eq_dec in H3; [ | apply list_eq_dec]...
        apply HFl; subst...
  Qed.

  Lemma Dependent_Forall_inf_arrow : forall (P : A -> Type) Pred1 Pred2,
      (forall a Pa, Pred1 a Pa -> Pred2 a Pa) ->
      forall l (Fl : Forall_inf P l), Dependent_Forall_inf Pred1 Fl -> Dependent_Forall_inf Pred2 Fl.
  Proof with try assumption.
    intros P Pred1 Pred2 f l Fl DFl.
    induction DFl ; constructor...
    apply f...
  Qed.

  Lemma Dependent_Forall_inf_app : forall (P : A -> Type) Pred,
      forall l1 l2 (Fl1 : Forall_inf P l1) (Fl2 : Forall_inf P l2),
        Dependent_Forall_inf Pred Fl1 -> Dependent_Forall_inf Pred Fl2 ->
        {Fl : Forall_inf P (l1 ++ l2) & Dependent_Forall_inf Pred Fl}.
  Proof with try assumption.
    intros P Pred l1 l2 Fl1 Fl2 DFl1; revert Fl2; induction DFl1; intros Fl2 DFl2.
    - split with Fl2...
    - destruct IHDFl1 with Fl2 as (Fl0 & DFl)...
      split with (Forall_inf_cons a Pa Fl0).
      apply Dependent_Forall_inf_cons...
  Qed.

  Lemma Dependent_Forall_inf_app_inv : forall (P : A -> Type) Pred,
      forall l1 l2 (Fl : Forall_inf P (l1 ++ l2)), Dependent_Forall_inf Pred Fl ->
         {Fl1 : Forall_inf P l1 & Dependent_Forall_inf Pred Fl1}
       * {Fl2 : Forall_inf P l2 & Dependent_Forall_inf Pred Fl2}.
  Proof with try assumption.
    intros P Pred l1 l2 Fl; induction l1; intro DFl.
    - split.
      + split with (Forall_inf_nil P).
        apply Dependent_Forall_inf_nil.
      + split with Fl...
    - inversion DFl.
      destruct IHl1 with Fl0 as ((Fl1 & DFl1) & (Fl2 & DFl2))...
      split.
      + split with (Forall_inf_cons a Pa Fl1).
        apply Dependent_Forall_inf_cons...
      + split with Fl2...
  Qed.

  Lemma Dependent_Forall_Type_elt_inv : forall (P : A -> Type) Pred,
      forall l1 l2 a (Fl : Forall_inf P (l1 ++ a :: l2)),
        Dependent_Forall_inf Pred Fl -> {Pa : P a & Pred a Pa}.
  Proof with try assumption.
    intros P Pred l1 l2 a Fl DFl.
    apply Dependent_Forall_inf_app_inv in DFl.
    destruct DFl as [_ [Fl2 DFl2]].
    inversion DFl2; subst.
    exists Pa...
  Qed.

End Eq_Dec.
