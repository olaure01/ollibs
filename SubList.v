From Stdlib Require Import PeanoNat Morphisms.
From Stdlib Require Decidable ListDec.
From OLlibs Require Import List_more.
Import ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.

Inductive sublist A : list A -> list A -> Prop :=
| sublist_nil : sublist nil nil
| sublist_cons a l1 l2 : sublist l1 l2 -> sublist (a :: l1) (a :: l2)
| sublist_drop a l1 l2 : sublist l1 l2 -> sublist l1 (a :: l2).

Lemma sublist_length A (l1 l2 : list A) : sublist l1 l2 -> length l1 <= length l2.
Proof.
intro Hsub. induction Hsub as [ | | ? ? l2 ?].
- reflexivity.
- cbn. apply -> Nat.succ_le_mono. assumption.
- transitivity (length l2); [ assumption | apply Nat.le_succ_diag_r ].
Qed.

Lemma sublist_nil_l A (l : list A) : sublist [] l.
Proof. induction l; constructor. assumption. Qed.

Lemma sublist_nil_r A (l : list A) : sublist l [] -> l = [].
Proof. intro Hsub. destruct l as [|a l]; inversion Hsub. reflexivity. Qed.

Lemma sublist_refl A (l : list A) : sublist l l.
Proof. induction l; constructor. assumption. Qed.

Lemma sublist_app_l A (l0 l1 l2 : list A) : sublist l1 l2 -> sublist l1 (l0 ++ l2).
Proof. induction l0 as [|a l0 IH]; intro Hsub; [ | apply sublist_drop, IH ]; assumption. Qed.

Lemma sublist_app_r A (l0 l1 l2 : list A) : sublist l1 l2 -> sublist l1 (l2 ++ l0).
Proof. intro Hsub. induction Hsub; [ apply sublist_nil_l | constructor; assumption .. ]. Qed.

Lemma sublist_app_app A (l1 l2 l3 l4 : list A) : sublist l1 l2 -> sublist l3 l4 -> sublist (l1 ++ l3) (l2 ++ l4).
Proof.
intro Hsub1. induction Hsub1 as [ | ? ? ? ? IHHsub1 | ? ? ? ? IHHsub1 ];
  intro Hsub2; [ assumption | constructor; apply IHHsub1, Hsub2 .. ].
Qed.

Lemma sublist_app_app_l A (l0 l1 l2 : list A) : sublist l1 l2 -> sublist (l0 ++ l1) (l0 ++ l2).
Proof. apply sublist_app_app, sublist_refl. Qed.

Lemma sublist_app_app_r A (l0 l1 l2 : list A) : sublist l1 l2 -> sublist (l1 ++ l0) (l2 ++ l0).
Proof. intro. apply sublist_app_app, sublist_refl. assumption. Qed.

Lemma sublist_incl A (l1 l2 : list A) : sublist l1 l2 -> incl l1 l2.
Proof.
intro Hsub. induction Hsub as [ | | ? ? ? ? IHHsub ].
- apply incl_nil_l.
- apply incl_cons_cons. assumption.
- intros x Hx. right. apply IHHsub, Hx.
Qed.

Lemma NoDup_sublist A (l1 l2 : list A) : sublist l1 l2 -> NoDup l2 -> NoDup l1.
Proof.
intro Hsub. induction Hsub as [ | ? ? ? Hsub IHHsub | ? ? ? ? IHHsub ]; intro Hnd.
- assumption.
- inversion_clear Hnd as [|? ? Hnin ?]. subst. constructor.
  + intro Hin. apply Hnin, (sublist_incl Hsub _ Hin).
  + apply IHHsub. assumption.
- apply IHHsub. inversion_clear Hnd. assumption.
Qed.

Lemma sublist_map A B (f : A -> B) l1 l2 : sublist l1 l2 -> sublist (map f l1) (map f l2).
Proof. intro Hsub. induction Hsub; constructor; assumption. Qed.

Lemma sublist_trans A (l1 l2 l3 : list A) : sublist l1 l2 -> sublist l2 l3 -> sublist l1 l3.
Proof.
intros Hsub1 Hsub2. induction Hsub2 as [ | ? ? ? ? IHHsub2 | ? ? ? ? IHHsub2 ] in l1, Hsub1 |- *.
- assumption.
- inversion_clear Hsub1; constructor; apply IHHsub2; assumption.
- apply IHHsub2 in Hsub1. apply sublist_drop. assumption.
Qed.

Lemma sublist_antisym A (l1 l2 : list A) : sublist l1 l2 -> sublist l2 l1 -> l1 = l2.
Proof.
intro Hsub1. induction Hsub1 as [ | ? l1 l2 Hsub1 IHHsub1 | ? l1 l2 Hsub1 _ ]; intro Hsub2.
- reflexivity.
- f_equal. apply IHHsub1. inversion_clear Hsub2 as [ | | ? ? ? Hsub Hsub' ]; [ assumption | exfalso ].
  apply sublist_length in Hsub1, Hsub.
  apply (Nat.nle_succ_diag_l (length l2)).
  transitivity (length l1); assumption.
- exfalso. apply sublist_length in Hsub1, Hsub2.
  apply (Nat.nle_succ_diag_l (length l2)).
  transitivity (length l1); assumption.
Qed.

#[export] Instance sublist_preorder A : PreOrder (@sublist A).
Proof. split; intro; [ apply sublist_refl | apply sublist_trans ]. Qed.

#[export] Instance sublist_antisym' A : Antisymmetric (list A) eq (@sublist A).
Proof. intro. apply sublist_antisym. Qed.

Lemma sublist_Add A (a : A) l1 l2 : Add a l1 l2 -> sublist l1 l2.
Proof. induction 1; constructor; [ apply sublist_refl | assumption ]. Qed.


(* with decidable equality *)

Lemma uniquify_map_sublist A B (eq_dec : forall x y:B, Decidable.decidable (x=y)) (f : A -> B) l :
 exists l', NoDup (map f l') /\ incl (map f l) (map f l') /\ sublist (map f l') (map f l).
Proof.
induction l as [ | a l IHl ].
- exists nil. simpl. split; [ | split ]; [ | red; trivial | ]; constructor.
- destruct IHl as [l' [Hnd [Hinc Hsub]]].
  destruct (ListDec.In_decidable eq_dec (f a) (map f l')).
  + exists l'. cbn. split; [ | split ]; [ assumption | | ].
    * intros x [|].
      -- now subst.
      -- now apply Hinc.
    * constructor. assumption.
  + exists (a :: l'). cbn. split; [ | split ].
    * now constructor.
    * intros x [|].
      -- subst. now left.
      -- right. now apply Hinc.
    * constructor. assumption.
Qed.

Lemma uniquify_sublist A (eq_dec : forall x y:A, Decidable.decidable (x=y)) (l:list A) :
  exists l', NoDup l' /\ incl l l' /\ sublist l' l.
Proof.
destruct (uniquify_map_sublist eq_dec id l) as [l' H].
exists l'. now rewrite !map_id in H.
Qed.
