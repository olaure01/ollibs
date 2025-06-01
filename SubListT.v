From Stdlib Require Import PeanoNat CMorphisms.
From OLlibs Require Import List_more SubList.
From OLlibs Require DecidableT.
Import ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.

Inductive sublistT A : crelation (list A) :=
| sublistT_nil : sublistT nil nil
| sublistT_cons a l1 l2 : sublistT l1 l2 -> sublistT (a :: l1) (a :: l2)
| sublistT_drop a l1 l2 : sublistT l1 l2 -> sublistT l1 (a :: l2).

Lemma sublistT_sublist A (l1 l2 : list A) : sublistT l1 l2 -> sublist l1 l2.
Proof. intro Hs. induction Hs; now constructor. Qed.

Lemma sublistT_nil_l A (l : list A) : sublistT [] l.
Proof. induction l; constructor. assumption. Qed.

Lemma sublistT_nil_r A (l : list A) : sublistT l [] -> l = [].
Proof. intro Hsub. destruct l as [|a l]; inversion Hsub. reflexivity. Qed.

Lemma sublistT_refl A (l : list A) : sublistT l l.
Proof. induction l; constructor. assumption. Qed.

Lemma sublistT_app_l A (l0 l1 l2 : list A) : sublistT l1 l2 -> sublistT l1 (l0 ++ l2).
Proof. induction l0 as [|a l0 IH]; intro Hsub; [ | apply sublistT_drop, IH ]; assumption. Qed.

Lemma sublistT_app_r A (l0 l1 l2 : list A) : sublistT l1 l2 -> sublistT l1 (l2 ++ l0).
Proof. intro Hsub. induction Hsub; [ apply sublistT_nil_l | constructor; assumption .. ]. Qed.

Lemma sublistT_app_app A (l1 l2 l3 l4 : list A) :
  sublistT l1 l2 -> sublistT l3 l4 -> sublistT (l1 ++ l3) (l2 ++ l4).
Proof.
intro Hsub1. induction Hsub1 as [ | ? ? ? ? IHHsub1 | ? ? ? ? IHHsub1 ];
  intro Hsub2; [ assumption | constructor; apply IHHsub1, Hsub2 .. ].
Qed.

Lemma sublistT_app_app_l A (l0 l1 l2 : list A) : sublistT l1 l2 -> sublistT (l0 ++ l1) (l0 ++ l2).
Proof. apply sublistT_app_app, sublistT_refl. Qed.

Lemma sublistT_app_app_r A (l0 l1 l2 : list A) : sublistT l1 l2 -> sublistT (l1 ++ l0) (l2 ++ l0).
Proof. intro. apply sublistT_app_app, sublistT_refl. assumption. Qed.

Lemma sublistT_inclT A (l1 l2 : list A) : sublistT l1 l2 -> inclT l1 l2.
Proof.
intro Hsub. induction Hsub as [ | | ? ? ? ? IHHsub ].
- apply inclT_nil_l.
- apply inclT_cons_cons. assumption.
- intros x Hx. right. apply IHHsub, Hx.
Qed.

Lemma NoDupT_sublistT A (l1 l2 : list A) : sublistT l1 l2 -> NoDupT l2 -> NoDupT l1.
Proof.
intro Hsub. induction Hsub as [ | ? ? ? Hsub IHHsub | ? ? ? ? IHHsub ]; intro Hnd.
- assumption.
- inversion_clear Hnd as [|? ? Hnin ?]. subst. constructor.
  + intro Hin. apply Hnin, (sublistT_inclT Hsub _ Hin).
  + apply IHHsub. assumption.
- apply IHHsub. inversion_clear Hnd. assumption.
Qed.

Lemma sublistT_map A B (f : A -> B) l1 l2 : sublistT l1 l2 -> sublistT (map f l1) (map f l2).
Proof. intro Hsub. induction Hsub; constructor; assumption. Qed.

Lemma sublistT_trans A (l1 l2 l3 : list A) : sublistT l1 l2 -> sublistT l2 l3 -> sublistT l1 l3.
Proof.
intros Hsub1 Hsub2. induction Hsub2 as [ | ? ? ? ? IHHsub2 | ? ? ? ? IHHsub2 ] in l1, Hsub1 |- *.
- assumption.
- inversion_clear Hsub1; constructor; apply IHHsub2; assumption.
- apply IHHsub2 in Hsub1. apply sublistT_drop. assumption.
Qed.

Lemma sublistT_antisym A (l1 l2 : list A) : sublistT l1 l2 -> sublistT l2 l1 -> l1 = l2.
Proof.
intro Hsub1. induction Hsub1 as [ | ? l1 l2 Hsub1 IHHsub1 | ? l1 l2 Hsub1 _ ]; intro Hsub2.
- reflexivity.
- f_equal. apply IHHsub1. inversion_clear Hsub2 as [ | | ? ? ? Hsub Hsub' ]; [ assumption | exfalso ].
  apply sublistT_sublist, sublist_length in Hsub1, Hsub.
  apply (Nat.nle_succ_diag_l (length l2)).
  transitivity (length l1); assumption.
- exfalso. apply sublistT_sublist, sublist_length in Hsub1, Hsub2.
  apply (Nat.nle_succ_diag_l (length l2)).
  transitivity (length l1); assumption.
Qed.

#[export] Instance sublistT_preorder A : PreOrder (@sublistT A).
Proof. split; intro; [ apply sublistT_refl | apply sublistT_trans ]. Qed.

#[export] Instance sublistT_antisym' A : Antisymmetric eq (@sublistT A).
Proof. intro. apply sublistT_antisym. Qed.

Lemma sublistT_cons_inv A (a : A) l1 l2 : sublistT (a :: l1) (a :: l2) -> sublistT l1 l2.
Proof.
intro Hs. inversion Hs; subst; [ | transitivity (a :: l1); [ constructor; reflexivity | ] ]; assumption.
Qed.

Lemma sublistT_AddT A (a : A) l1 l2 : AddT a l1 l2 -> sublistT l1 l2.
Proof. induction 1; constructor; [ apply sublistT_refl | assumption ]. Qed.


(* with decidable equality *)

Lemma uniquify_map_sublistT A B (eq_dec : forall x y:B, DecidableT.decidableP (x=y)) (f : A -> B) l :
 { l' & (NoDupT (map f l') * inclT (map f l) (map f l'))%type & sublistT (map f l') (map f l) }.
Proof.
induction l as [ | a l IHl ].
- exists nil; cbn; [ split | ]; [ | red; trivial | ]; constructor.
- destruct IHl as [l' [Hnd Hinc] Hsub].
  destruct (inT_decT eq_dec (f a) (map f l')).
  + exists l'; cbn; [ split | ]; [ assumption | | ].
    * intros x [|].
      -- now subst.
      -- now apply Hinc.
    * constructor. assumption.
  + exists (a :: l'); cbn; [ split | ].
    * now constructor.
    * intros x [|].
      -- subst. now left.
      -- right. now apply Hinc.
    * constructor. assumption.
Qed.

Lemma uniquify_sublistT A (eq_dec : forall x y:A, DecidableT.decidableP (x=y)) (l:list A) :
  { l' & (NoDupT l' * inclT l l')%type & sublistT l' l }.
Proof.
destruct (uniquify_map_sublistT eq_dec id l) as [l' H].
now exists l'; rewrite !map_id in *.
Qed.
