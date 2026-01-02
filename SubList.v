From Stdlib Require Import PeanoNat Relations Morphisms Permutation.
From Stdlib Require Decidable ListDec.
From OLlibs Require Import List_more.
Import ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


Inductive sublist A : relation (list A) :=
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

Lemma sublist_cons_inv A (a : A) l1 l2 : sublist (a :: l1) (a :: l2) -> sublist l1 l2.
Proof.
intro Hs. inversion Hs; subst; [ | transitivity (a :: l1); [ constructor; reflexivity | ] ]; assumption.
Qed.

Lemma sublist_elt_l_inv A (a : A) l1' l1'' l2 :
  sublist (l1' ++ a :: l1'') l2 -> exists l2' l2'', l2 = l2' ++ a :: l2'' /\ sublist l1' l2' /\ sublist l1'' l2''.
Proof.
intro Hs.
remember (l1' ++ a :: l1'') as l1 eqn:Hl1.
induction Hs as [ | b l1 l2 Hs' IH | b l1 l2 Hs' IH ] in l1', l1'', Hl1 |- *.
- decomp_list_eq Hl1.
- decomp_list_eq Hl1; subst.
  + specialize (IH _ _ eq_refl) as [l2' [l2'' [-> [Hs2 Hs2']]]].
    exists (b :: l2'), l2''. repeat split.
    * constructor. assumption.
    * assumption.
  + exists nil, l2. now repeat split.
- subst.
  specialize (IH _ _ eq_refl) as [l2' [l2'' [-> [Hs2 Hs2']]]].
  exists (b :: l2'), l2''. repeat split.
  * constructor. assumption.
  * assumption.
Qed.

Lemma sublist_cons_l_inv A (a : A) l1 l2 :
  sublist (a :: l1) l2 -> exists l2' l2'', l2 = l2' ++ a :: l2'' /\ sublist l1 l2''.
Proof.
intros [l2' [l2'' [-> [Hs Hs']]]]%(sublist_elt_l_inv _ nil).
exists l2', l2''. repeat split. assumption.
Qed.

Lemma sublist_sgt A (a : A) l : sublist [a] l <-> In a l.
Proof.
split.
- intros Hs%sublist_incl. apply Hs, in_eq.
- intros [l1 [l2 ->]]%in_split.
  apply sublist_app_l. constructor. apply sublist_nil_l.
Qed.

Lemma sublist_Add A (a : A) l1 l2 : Add a l1 l2 -> sublist l1 l2.
Proof. induction 1; constructor; [ apply sublist_refl | assumption ]. Qed.

Lemma sublist_in_extend A (a : A) l1 l2 : sublist l1 l2 -> In a l2 ->
  exists l1', sublist l1' l2 /\ incl (a :: l1) l1' /\ incl l1' (a :: l1).
Proof.
intro Hsub. induction Hsub as [ | b l1 l2 Hsub IH | b l1 l2 Hsub IH ]; intro Hin.
- destruct Hin.
- destruct Hin as [[= ->] | Hin].
  + exists (a :: l1); split; [ | split ].
    * now constructor.
    * apply incl_cons; [ apply in_eq | apply incl_refl ].
    * apply incl_cons_cons, incl_tl, incl_refl.
  + destruct (IH Hin) as [l1' [Hsub' [Hin' Hincl']]].
    exists (b :: l1'); split; [ | split ].
    * now constructor.
    * apply incl_cons_inv in Hin'.
      apply incl_cons.
      -- apply in_cons, (proj1 Hin').
      -- apply incl_cons_cons, Hin'.
    * intros c [[= ->] | Hinc%Hincl'].
      -- apply in_cons, in_eq.
      -- destruct Hinc as [[= ->] | Hinc].
         ++ apply in_eq.
         ++ apply in_cons, in_cons. assumption.
- destruct Hin as [[= ->] | Hin].
  + exists (a :: l1); split; [ | split ].
    * now constructor.
    * apply incl_refl.
    * apply incl_refl.
  + destruct (IH Hin) as [l1' [Hsub' [Hin' Hincl']]].
    exists l1'; split; [ | split ].
    * now constructor.
    * assumption.
    * assumption.
Qed.

Lemma sublist_filter A f (l : list A) : sublist (filter f l) l.
Proof. induction l as [ | a l IH ]; cbn; try destruct (f a); now constructor. Qed.


(* with decidable equality *)

Lemma uniquify_map_sublist A B (eq_dec : forall x y:B, Decidable.decidable (x=y)) (f : A -> B) l :
  exists l', NoDup (map f l') /\ incl (map f l) (map f l') /\ sublist (map f l') (map f l).
Proof.
induction l as [ | a l IHl ].
- exists nil. cbn. split; [ | split ]; [ | red; trivial | ]; constructor.
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


Lemma sublist_Permutation A (l1 l2 l2' : list A) :
  sublist l1 l2 -> Permutation l2 l2' -> exists l1', Permutation l1 l1' /\ sublist l1' l2'.
Proof.
intros Hs HP. induction HP as [ | x l l' ? IH | x y | ? ? ? ? IH1 ? IH2 ] in l1, Hs |- *.
- inversion Hs. subst.
  exists nil. split; constructor.
- inversion Hs as [ | ? ? ? Hs' HP' IHs | ? ? ? Hs' HP' IHs ]; subst.
  + apply IH in Hs' as [l1' [Hs1' HP1']].
    exists (x :: l1'). split; constructor; assumption.
  + apply IH in Hs' as [l1' [Hs1' HP1']].
    exists l1'. split.
    * assumption.
    * constructor; assumption.
- inversion Hs as [ | ? l0 ? Hs' HP IHs | ? ? ? Hs' HP IHs ]; subst.
  + inversion Hs' as [ | ? l1 ? Hs'' HP' IHs' | ? ? ? Hs'' HP' IHs' ]; subst.
    * exists (x :: y :: l1). split.
      -- constructor.
      -- do 2 constructor; assumption.
    * exists (y :: l0). split.
      -- reflexivity.
      -- do 2 constructor; assumption.
  + inversion Hs' as [ | ? l0 ? Hs'' HP' IHs' | ? ? ? Hs'' HP' IHs' ]; subst.
    * exists (x :: l0). split.
      -- reflexivity.
      -- do 2 constructor; assumption.
    * exists l1. split.
      -- reflexivity.
      -- do 2 constructor; assumption.
- apply IH1 in Hs. destruct Hs as [l1' [HP1' Hs1']].
  apply IH2 in Hs1'. destruct Hs1' as [l2' [HP2' Hs2']].
  exists l2'. split; [ transitivity l1' | ]; assumption.
Qed.

Lemma Permutation_sublist A (l1 l1' l2' : list A) :
  Permutation l1 l1' -> sublist l1' l2' -> exists l2, sublist l1 l2 /\ Permutation l2 l2'.
Proof.
intro HP. induction HP as [ | x ? ? ? IH | x y | ? ? ? ? IH1 ? IH2 ] in l2' |- *; intro Hs.
- exists l2'. now split.
- apply sublist_cons_l_inv in Hs as [l2'' [l2''' [-> Hs]]].
  apply IH in Hs as [l2' [Hs HP']].
  exists (x :: l2'' ++ l2'). split.
  + constructor. apply sublist_app_l. assumption.
  + rewrite HP'. apply Permutation_middle.
- apply sublist_cons_l_inv in Hs as [l2'' [l2''' [-> Hs]]].
  apply sublist_cons_l_inv in Hs as [l3'' [l3''' [-> Hs]]].
  exists (y :: x :: l2'' ++ l3'' ++ l3'''). split.
  + do 2 constructor. apply sublist_app_l, sublist_app_l. assumption.
  + rewrite (app_comm_cons l3'' _ x), (app_assoc _ _ (y :: _)).
    apply Permutation_cons_app. list_simpl. apply Permutation_middle.
- apply IH2 in Hs as [l2 [HP2' Hs2']].
  apply IH1 in HP2' as [l1' [HP1' Hs1']].
  exists l1'. split; [ | transitivity l2 ]; assumption.
Qed.

(*
Lemma Permutation_app_sublist A (l1 l2 l3 : list A) :
  Permutation (l1 ++ l2) l3 -> exists l', Permutation l1 l' /\ sublist l' l3.
Proof. apply sublist_Permutation, sublist_app_r. reflexivity. Qed.
*)

Lemma sublist_as_Permutation A (l1 l2 : list A) :
  sublist l1 l2 -> exists l, Permutation (l1 ++ l) l2.
Proof.
intro Hs. induction Hs as [ | ? ? ? ? [l HP] | a ? ? ? [l HP] ].
- exists nil. reflexivity.
- exists l. constructor. assumption.
- exists (a :: l). rewrite <- HP. symmetry. apply Permutation_middle.
Qed.

Lemma NoDup_sublist A (l1 l2 : list A) : sublist l1 l2 -> NoDup l2 -> NoDup l1.
Proof.
intros [m HP]%sublist_as_Permutation Hnd.
symmetry in HP. apply Permutation_NoDup in HP; [ | assumption ].
apply (NoDup_app_remove_r _ _ HP).
Qed.
