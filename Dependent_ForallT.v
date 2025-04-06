(** Generalization of [ForallT] to dependent product *)

From Stdlib Require Export Eqdep_dec.
From Stdlib Require Import PeanoNat List.
From OLlibs Require Import List_Type.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


(** * [In_ForallT] *)

Section In_ForallT.
  Variable A : Type.
  Variable P : A -> Type.

  Fixpoint In_ForallT l (a : A) (Pa : P a) (Fl : ForallT P l) : Type :=
    match Fl with
    | ForallT_nil _ => False
    | ForallT_cons b Pb Fl => ((existT P a Pa) = (existT P b Pb)) + In_ForallT Pa Fl
    end.

  Lemma In_ForallT_elt l1 l2 a (Fl : ForallT P (l1 ++ a :: l2)) : { Pa : P a & In_ForallT Pa Fl }.
  Proof.
  induction l1 as [|b l1 IHl1] in l2, a, Fl |- *.
  - simpl in Fl.
    remember (a :: l2) eqn:Heql.
    destruct Fl as [|? ? p Fl]; inversion Heql; subst.
    exists p. left. reflexivity.
  - remember ((b :: l1) ++ a :: l2) eqn:Heql.
    destruct Fl as [|? ? p Fl]; inversion Heql; subst.
    destruct IHl1 with l2 a Fl as [Pa Hin].
    exists Pa. right. assumption.
  Qed.

  Lemma InT_In_ForallT l a (Fl : ForallT P l) : InT a l -> { Pa : P a & In_ForallT Pa Fl }.
  Proof.
  induction l as [|b l IHl] in a, Fl |- *; intros Hin; inversion Hin; subst.
  - remember (a :: l) as l' eqn:Heql'.
    destruct Fl as [|? ? p Fl]; inversion Heql'; subst.
    exists p. left. reflexivity.
  - remember (b :: l) as l' eqn:Heql'.
    destruct Fl as [|? ? p Fl]; inversion Heql'; subst.
    destruct IHl with a Fl as [Pa Hin']; [ assumption | ].
    exists Pa. right. assumption.
  Qed.

  Fixpoint ForallT_sum (f : forall a, P a -> nat) (l : list A) (Pl : ForallT P l) :=
    match Pl with
    | ForallT_nil _ => 0
    | ForallT_cons x Px Pl => (f x Px) + (ForallT_sum f Pl)
    end.

  Fixpoint ForallT_App l1 l2 Pl1 Pl2 :=
    match Pl1 with
    | ForallT_nil _ => Pl2
    | @ForallT_cons _ _ x l Px Pl => @ForallT_cons _ P x (l ++ l2) Px
                                                         (ForallT_App l l2 Pl Pl2)
    end.

  Lemma ForallT_sum_app f l1 l2 (Pl1 : ForallT P l1) (Pl2 : ForallT P l2) :
      ForallT_sum f (ForallT_App Pl1 Pl2)
    = ForallT_sum f Pl1 + ForallT_sum f Pl2.
  Proof. induction Pl1 as [| ? ? ? ? IHPl1]; [ reflexivity | ]. simpl. rewrite IHPl1. apply Nat.add_assoc. Qed.

  Lemma In_ForallT_InT l (L : list A) (p : P l) (PL : ForallT P L) : In_ForallT p PL -> InT l L.
  Proof.
  intros Hin. induction PL; [ inversion Hin | inversion Hin as [He|]]; [ left | right; auto ].
  injection He as [= ->]. reflexivity.
  Qed.

End In_ForallT.


(** * [Dependent_ForallT] *)

Inductive Dependent_ForallT A (P : A -> Type) (Pred : forall a, P a -> Type) :
   forall l, ForallT P l -> Type :=
| Dependent_ForallT_nil : Dependent_ForallT Pred (ForallT_nil P)
| Dependent_ForallT_cons a l Pa (Fl : ForallT P l) : (Pred a Pa) ->
           Dependent_ForallT Pred Fl -> Dependent_ForallT Pred (ForallT_cons a Pa Fl).

Section Eq_Dec.

  Variable A : Type.
  Hypothesis eq_dec : forall (x y : A), {x = y} + {x <> y}.

  Lemma Dependent_ForallT_forall (P : A -> Type) Pred l a Pa (Fl : ForallT P l) :
    Dependent_ForallT Pred Fl -> In_ForallT a Pa Fl -> Pred a Pa.
  Proof using eq_dec.
  intros DFl. revert a Pa; induction DFl as [|? ? ? ? ? ? IH]; intros a' Pa' Hin;
    [ inversion Hin | inversion Hin as [He|Heq] ].
  - injection He as [= -> He].
    apply inj_pair2_eq_dec in He as ->; assumption.
  - apply IH. assumption.
  Qed.

  Lemma forall_Dependent_ForallT (P : A -> Type) Pred l (Fl : ForallT P l) :
    (forall a Pa, In_ForallT a Pa Fl -> Pred a Pa) ->
    Dependent_ForallT Pred Fl.
  Proof.
  induction Fl as [|? ? ? ? IH]; intros f; constructor.
  - apply f. left. reflexivity.
  - apply IH. intros a Pa Hin.
    apply f. right. assumption.
  Qed.

  Lemma Dependent_ForallT_inv (P : A -> Type) Pred a l Pa : forall (Pl : ForallT P l),
    Dependent_ForallT Pred (ForallT_cons a Pa Pl) -> Pred a Pa.
  Proof using eq_dec.
  intros Pl DPl. inversion DPl as [| ? ? Pb]. subst.
  replace Pa with Pb; [ assumption | ].
  apply inj_pair2_eq_dec; assumption.
  Qed.

  Lemma Dependent_ForallT_decT (P :A -> Type) Pred (dec_Pred : forall a Pa, Pred a Pa + notT (Pred a Pa)) l
    (Fl : ForallT P l) : Dependent_ForallT Pred Fl + (Dependent_ForallT Pred Fl -> False).
  Proof using eq_dec.
  induction Fl as [|x l p ? [HFl|HFl]].
  - left. apply Dependent_ForallT_nil.
  - destruct dec_Pred with x p as [HPa | HnPa].
    + left. apply Dependent_ForallT_cons; assumption.
    + right. intro DFl. inversion DFl as [|? ? Pb].
      apply HnPa.
      replace p with Pb; [ assumption | ].
      apply inj_pair2_eq_dec; assumption.
  - right. intro DFl. inversion DFl as [|? ? ? ? ? ? Heq [He1 He2]].
    apply inj_pair2_eq_dec in He2; [ subst | apply list_eq_dec, eq_dec ].
    apply HFl. assumption.
  Qed.

  Lemma Dependent_ForallT_arrow (P : A -> Type) Pred1 Pred2 :
    (forall a Pa, Pred1 a Pa -> Pred2 a Pa) ->
    forall l (Fl : ForallT P l), Dependent_ForallT Pred1 Fl -> Dependent_ForallT Pred2 Fl.
  Proof. intros f l Fl DFl. induction DFl; constructor; auto. Qed.

  Lemma Dependent_ForallT_app (P : A -> Type) Pred l1 l2 (Fl1 : ForallT P l1) (Fl2 : ForallT P l2) :
    Dependent_ForallT Pred Fl1 -> Dependent_ForallT Pred Fl2 ->
    { Fl : ForallT P (l1 ++ l2) & Dependent_ForallT Pred Fl }.
  Proof.
  intros DFl1. induction DFl1 as [|a l Pa ? ? ? IH] in Fl2 |- *; intros DFl2.
  - exists Fl2. assumption.
  - destruct IH with Fl2 as [Fl0 DFl]; [ assumption | ].
    exists (ForallT_cons a Pa Fl0).
    apply Dependent_ForallT_cons; assumption.
  Qed.

  Lemma Dependent_ForallT_app_inv (P : A -> Type) Pred l1 l2 (Fl : ForallT P (l1 ++ l2)) :
     Dependent_ForallT Pred Fl ->
       { Fl1 : ForallT P l1 & Dependent_ForallT Pred Fl1 }
     * { Fl2 : ForallT P l2 & Dependent_ForallT Pred Fl2 }.
  Proof.
  induction l1 as [|a l1 IHl1]; intro DFl.
  - split.
    + exists (ForallT_nil P). apply Dependent_ForallT_nil.
    + exists Fl. assumption.
  - inversion DFl as [|b lb Pa Fl0].
    destruct IHl1 with Fl0 as [[Fl1 DFl1] [Fl2 DFl2]]; [ assumption | ].
    split.
    + exists (ForallT_cons a Pa Fl1).
      apply Dependent_ForallT_cons; assumption.
    + exists Fl2. assumption.
  Qed.

  Lemma Dependent_ForallT_elt_inv (P : A -> Type) Pred l1 l2 a (Fl : ForallT P (l1 ++ a :: l2)) :
    Dependent_ForallT Pred Fl -> { Pa : P a & Pred a Pa }.
  Proof.
  intros DFl. apply Dependent_ForallT_app_inv in DFl as [_ [Fl2 DFl2]].
  inversion_clear DFl2 as [|b l Pa]. exists Pa. assumption.
  Qed.

End Eq_Dec.


From OLlibs Require Import dectype.
From OLlibs Require issue12394. (* TODO remove when issue rocq#12394 solved *)

(* TODO dealing with issue rocq#12394 *)
(* Example:
  [ old code
         apply inj_pair2_eq_dec in H2; [ | apply list_eq_dec, (@eq_dt_dec Hdec)].
         apply inj_pair2_eq_dec in H3; [ | apply list_eq_dec, list_eq_dec (@eq_dt_dec Hdec)].
         subst.
    new code should be cbnified or old code back once rocq#12394 solved
         apply inj_pair2_eq_dec in H2;
           [ | apply (@list_eq_dec _ (@eqb (list_dectype Hdec))); apply eqb_eq ].
         assert (Pa = p) as Heq; subst.
         { apply issue12394.injection_list_ForallT_cons in H2 as [-> _]; [ reflexivity | ].
           apply (@list_eq_dec _ (@eqb Hdec)); apply eqb_eq. } *)
Ltac Dependent_ForallT_inversion Hdec H :=
  match type of H with
  | Dependent_ForallT _ _ =>
    let a := fresh in
    let b := fresh in
    let L := fresh "L" in
    let H1 := fresh H in
    let H2 := fresh H in
    let H3 := fresh H in
    let Heq1 := fresh in
    let Heq2 := fresh in
    let Heq := fresh "HeqD" in
    inversion H as [|a b L H1 H2 H3 [Heq1 Heq2] Heq]; subst a; subst b;
    apply inj_pair2_eq_dec in Heq;
      [ | apply (@list_eq_dec _ (@eqb (list_dectype Hdec))); apply eqb_eq ];
    apply issue12394.injection_list_ForallT_cons in Heq as [-> ->];
      [ | apply (@list_eq_dec _ (@eqb Hdec)); apply eqb_eq ]
  end.
