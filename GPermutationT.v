(** Factorized statements for different notions of permutation *)

From Stdlib Require Import List CMorphisms.
From OLlibs Require Import funtheory ComparisonOrder List_more
                           PermutationT_more PermutationT_solve
                           CPermutationT CPermutationT_solve.
From OLlibs Require GPermutation.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


Section GPermutationT.

  Variable A : Type.
  Variable c : comparison.
  Variable b : bool.

  (** * Definitions
   parametrized by a trilean or a boolean. *)

  (** Permutation or cyclic permutation or equality *)

  Definition PCEPermutationT :=
  match c with
  | Lt => @eq (list A)
  | Eq => @CPermutationT A
  | Gt => @PermutationT A
  end.

  (** Permutation or cyclic permutation *)
  Definition PCPermutationT := if b then @PermutationT A else @CPermutationT A.

  (** Permutation or equality *)
  Definition PEPermutationT := if b then @PermutationT A else @eq (list A).

  Ltac case_perm_tri := unfold PCEPermutationT; destruct c.
  Ltac case_perm := unfold PCPermutationT, PEPermutationT; destruct b.

  Lemma PCEPermutationT_PCEPermutation l1 l2 :
    PCEPermutationT l1 l2 -> GPermutation.PCEPermutation c l1 l2.
  Proof.
  now case_perm_tri; [ apply CPermutationT_CPermutation | | apply PermutationT_Permutation ].
  Qed.

  Lemma PCPermutationT_PCPermutation l1 l2 :
    PCPermutationT l1 l2 -> GPermutation.PCPermutation b l1 l2.
  Proof. case_perm; [ apply PermutationT_Permutation | apply CPermutationT_CPermutation ]. Qed.

  Lemma PEPermutationT_PEPermutation l1 l2 :
    PEPermutationT l1 l2 -> GPermutation.PEPermutation b l1 l2.
  Proof. now case_perm; [ apply PermutationT_Permutation | ]. Qed.

  #[export] Instance PEPermutation_PCPermutationT :
    Proper (PEPermutationT ==> PCPermutationT) id.
  Proof.  now case_perm; cbn; intros l l' HP; [ | subst ]. Qed.

  #[export] Instance PCEPermutation_PermutationT :
    Proper (PCEPermutationT ==> (@PermutationT A)) id.
  Proof.
  case_perm_tri; intros l1 l2 HP; [ apply CPermutationT_PermutationT | subst | ]; auto.
  Qed.

  #[export] Instance PCPermutation_PermutationT :
    Proper (PCPermutationT ==> (@PermutationT A)) id.
  Proof. now case_perm; [ | apply CPermutationT_PermutationT ]. Qed.

  #[export] Instance PEPermutation_PermutationT :
    Proper (PEPermutationT ==> (@PermutationT A)) id.
  Proof. case_perm; cbn; intros l l' HP; now subst. Qed.

  #[export] Instance CPermutationT_PCPermutationT :
    Proper (@CPermutationT A ==> PCPermutationT) id.
  Proof. now case_perm; [ apply CPermutationT_PermutationT | ]. Qed.

  #[export] Instance eq_PCEPermutationT : Proper (eq ==> PCEPermutationT) id.
  Proof. case_perm_tri; repeat intro; subst; reflexivity. Qed.

  #[export] Instance eq_PEPermutationT : Proper (eq ==> PEPermutationT) id.
  Proof. case_perm; repeat intro; subst; reflexivity. Qed.


  (** ** Properties of [PCEPermutationT] *)

  #[export] Instance PCEPermutationT_refl : Reflexive PCEPermutationT.
  Proof. case_perm_tri; intros l; reflexivity. Qed.

  #[export] Instance PCEPermutationT_sym : Symmetric PCEPermutationT.
  Proof. case_perm_tri; intros l l'; now symmetry. Qed.

  #[export] Instance PCEPermutationT_trans : Transitive PCEPermutationT.
  Proof. case_perm_tri; intros l l' l''; now transitivity l'. Qed.

  #[export] Instance PCEPermutationT_equiv : Equivalence PCEPermutationT.
  Proof.
  split;
  [ apply PCEPermutationT_refl
  | apply PCEPermutationT_sym
  | apply PCEPermutationT_trans ].
  Qed.

  Lemma PCEPermutationT_nil l : PCEPermutationT nil l -> l = nil.
  Proof.
  now case_perm_tri; [ apply CPermutationT_nil | subst | apply PermutationT_nil ].
  Qed.

  Lemma PCEPermutationT_nil_cons l a : PCEPermutationT nil (a :: l) -> False.
  Proof.
  case_perm_tri;
    [ apply CPermutationT_nil_cons
    | intros Heq; inversion Heq | apply PermutationT_nil_cons ].
  Qed.

  Lemma PCEPermutationT_length_1_inv a l : PCEPermutationT (a :: nil) l -> l = a :: nil.
  Proof.
  now case_perm_tri;
    [ apply CPermutationT_length_1_inv | subst | apply PermutationT_length_1_inv ].
  Qed.

  Lemma PCEPermutationT_vs_elt_subst a l l1 l2 :
    PCEPermutationT l (l1 ++ a :: l2) ->
      {'(l', l'') & forall l0, PCEPermutationT (l' ++ l0 ++ l'') (l1 ++ l0 ++ l2)
                  & l = l' ++ a :: l'' }.
  Proof.
  case_perm_tri; intros HP.
  - apply CPermutationT_vs_elt_subst; assumption.
  - exists (l1, l2); [ reflexivity | assumption ].
  - apply PermutationT_vs_elt_subst; assumption.
  Qed.

  #[export] Instance PCEPermutationT_in a : Proper (PCEPermutationT ==> Basics.impl) (In a).
  Proof.
  now case_perm_tri; intros l l' HP Hin;
    [ apply CPermutationT_in with l | subst | apply PermutationT_in with l ].
  Qed.

  #[export] Instance PCEPermutationT_Forall (P : A -> Prop) :
    Proper (PCEPermutationT ==> Basics.impl) (Forall P).
  Proof.
  now case_perm_tri;
    [ apply CPermutationT_Forall | intros ? ? -> | apply PermutationT_Forall ].
  Qed.

  #[export] Instance PCEPermutationT_Exists (P : A -> Prop) :
    Proper (PCEPermutationT ==> Basics.impl) (Exists P).
  Proof.
  now case_perm_tri;
    [ apply CPermutationT_Exists | intros ? ? -> | apply PermutationT_Exists ].
  Qed.

  #[export] Instance PCEPermutationT_ForallT (P : A -> Type) :
    Proper (PCEPermutationT ==> arrow) (ForallT P).
  Proof.
  now case_perm_tri;
    [ apply CPermutationT_ForallT | intros ? ? -> | apply PermutationT_ForallT ].
  Qed.

  #[export] Instance PCEPermutationT_ExistsT (P : A -> Type) :
    Proper (PCEPermutationT ==> arrow) (ExistsT P).
  Proof.
  now case_perm_tri;
    [ apply CPermutationT_ExistsT | intros ? ? -> | apply PermutationT_ExistsT ].
  Qed.


  (** ** Properties of [PCPermutationT] *)

  #[export] Instance PCPermutationT_refl : Reflexive PCPermutationT.
  Proof. case_perm; intros l; reflexivity. Qed.

  #[export] Instance PCPermutationT_sym : Symmetric PCPermutationT.
  Proof. case_perm; intros l l'; now symmetry. Qed.

  #[export] Instance PCPermutationT_trans : Transitive PCPermutationT.
  Proof. case_perm; intros l l' l''; now transitivity l'. Qed.

  #[export] Instance PCPermutationT_equiv : Equivalence PCPermutationT.
  Proof.
  split;
  [ apply PCPermutationT_refl | apply PCPermutationT_sym | apply PCPermutationT_trans ].
  Qed.


  Lemma PCPermutationT_swap a1 a2 :
    PCPermutationT (a1 :: a2 :: nil) (a2 :: a1 :: nil).
  Proof. case_perm; [ intros; apply PermutationT_swap | apply CPermutationT_swap ]. Qed.

  Lemma PCPermutationT_cons_append a l : PCPermutationT (a :: l) (l ++ a :: nil).
  Proof.
  case_perm; intros; rewrite <- (app_nil_l l), app_comm_cons;
    [ apply PermutationT_cons_append | apply CPermutationT_cons_append ].
  Qed.

  Lemma PCPermutationT_app_comm l l' : PCPermutationT (l ++ l') (l' ++ l).
  Proof. case_perm; [ apply PermutationT_app_comm | apply cpermT ]. Qed.

  Lemma PCPermutationT_app_rot l1 l2 l3 : PCPermutationT (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
  Proof. case_perm; [ apply PermutationT_app_rot | apply CPermutationT_app_rot ]. Qed.

  Lemma PCPermutationT_nil l : PCPermutationT nil l -> l = nil.
  Proof. now case_perm; [ apply PermutationT_nil | apply CPermutationT_nil ]. Qed.

  Lemma PCPermutationT_nil_cons l a : PCPermutationT nil (a :: l) -> False.
  Proof. now case_perm; [ apply PermutationT_nil_cons | apply CPermutationT_nil_cons ]. Qed.

  Lemma PCPermutationT_length_1_inv a l : PCPermutationT (a :: nil) l -> l = a :: nil.
  Proof.
  now case_perm; [ apply PermutationT_length_1_inv | apply CPermutationT_length_1_inv ].
  Qed.

  Lemma PCPermutationT_length_2_inv a1 a2 l :
    PCPermutationT (a1 :: a2 :: nil) l -> { l = a1 :: a2 :: nil } + { l = a2 :: a1 :: nil }.
  Proof.
  now case_perm; [ apply PermutationT_length_2_inv | apply CPermutationT_length_2_inv ].
  Qed.

  Lemma PCPermutationT_vs_elt_subst a l l1 l2 :
    PCPermutationT l (l1 ++ a :: l2) ->
      {'(l', l'') & forall l0, PCPermutationT (l' ++ l0 ++ l'') (l1 ++ l0 ++ l2)
                  & l = l' ++ a :: l'' }.
  Proof.
  case_perm; intros HP;
    [ apply PermutationT_vs_elt_subst | apply CPermutationT_vs_elt_subst ]; assumption.
  Qed.

  #[export] Instance PCPermutationT_in a : Proper (PCPermutationT ==> Basics.impl) (In a).
  Proof.
  now case_perm; intros l l' HP Hin;
    [ apply PermutationT_in with l | apply CPermutationT_in with l ].
  Qed.

  #[export] Instance PCPermutationT_Forall (P : A -> Prop) :
    Proper (PCPermutationT ==> Basics.impl) (Forall P).
  Proof. case_perm; [ apply PermutationT_Forall | apply CPermutationT_Forall ]. Qed.

  #[export] Instance PCPermutationT_Exists (P : A -> Prop) :
    Proper (PCPermutationT ==> Basics.impl) (Exists P).
  Proof. now case_perm; [ apply PermutationT_Exists | apply CPermutationT_Exists ]. Qed.

  #[export] Instance PCPermutationT_ForallT (P : A -> Type) :
    Proper (PCPermutationT ==> arrow) (ForallT P).
  Proof. case_perm; [ apply PermutationT_ForallT | apply CPermutationT_ForallT ]. Qed.

  #[export] Instance PCPermutationT_ExistsT (P : A -> Type) :
    Proper (PCPermutationT ==> arrow) (ExistsT P).
  Proof.
  now case_perm; [ apply PermutationT_ExistsT | apply CPermutationT_ExistsT ].
  Qed.


  (** ** Properties of [PEPermutationT] *)

  #[export] Instance PEPermutationT_refl : Reflexive PEPermutationT.
  Proof. now case_perm. Qed.

  #[export] Instance PEPermutationT_sym : Symmetric PEPermutationT.
  Proof. now case_perm. Qed.

  #[export] Instance PEPermutationT_trans : Transitive PEPermutationT.
  Proof. now case_perm; intros l l' l''; transitivity l'. Qed.

  #[export] Instance PEPermutationT_equiv : Equivalence PEPermutationT.
  Proof.
  split;
  [ apply PEPermutationT_refl | apply PEPermutationT_sym | apply PEPermutationT_trans ].
  Qed.

  #[export] Instance PEPermutationT_cons :
    Proper (eq ==> PEPermutationT ==> PEPermutationT) cons.
  Proof. now case_perm; intros x y -> l1 l2 HP; [ apply PermutationT_cons | rewrite HP ]. Qed.

  #[export] Instance PEPermutationT_app :
    Proper (PEPermutationT ==> PEPermutationT ==> PEPermutationT) (@app A).
  Proof. now case_perm; cbn; intros l m HP1 l' m' HP2; [ apply PermutationT_app | subst ]. Qed.

  Lemma PEPermutationT_app_tail l l' tl :
    PEPermutationT l l' -> PEPermutationT (l ++ tl) (l' ++ tl).
  Proof. now case_perm; cbn; intros HP; [ apply PermutationT_app_tail | subst ]. Qed.

  Lemma PEPermutationT_app_head l tl tl' :
    PEPermutationT tl tl' -> PEPermutationT (l ++ tl) (l ++ tl').
  Proof. now case_perm; cbn; intros HP; [ apply PermutationT_app_head | subst ]. Qed.

  Lemma PEPermutationT_add_inside a l l' tl tl' :
    PEPermutationT l l' -> PEPermutationT tl tl' ->
    PEPermutationT (l ++ a :: tl) (l' ++ a :: tl').
  Proof. now case_perm; cbn; intros HP1 HP2; [ apply PermutationT_add_inside | subst ]. Qed.

  Lemma PEPermutationT_nil l : PEPermutationT nil l -> l = nil.
  Proof. now case_perm; [ apply PermutationT_nil | symmetry ]. Qed.

  Lemma PEPermutationT_nil_cons l a : notT (PEPermutationT nil (a :: l)).
  Proof. case_perm; intro HP; [ apply (PermutationT_nil_cons HP) | inversion HP ]. Qed.

  Lemma PEPermutationT_length_1_inv a l : PEPermutationT (a :: nil) l -> l = a :: nil.
  Proof. now case_perm; [ apply PermutationT_length_1_inv | symmetry ]. Qed.

  Lemma PEPermutationT_length_2_inv a1 a2 l :
    PEPermutationT (a1 :: a2 :: nil) l -> { l = a1 :: a2 :: nil } + { l = a2 :: a1 :: nil }.
  Proof. now case_perm; [ apply PermutationT_length_2_inv | left; symmetry ]. Qed.

  Lemma PEPermutationT_vs_elt_subst a l l1 l2 :
    PEPermutationT l (l1 ++ a :: l2) ->
      {'(l', l'') & forall l0, PEPermutationT (l' ++ l0 ++ l'') (l1 ++ l0 ++ l2)
                  & l = l' ++ a :: l'' }.
  Proof.
  case_perm; intros HP.
  - apply PermutationT_vs_elt_subst; assumption.
  - exists (l1, l2); [ reflexivity | assumption ].
  Qed.

  Lemma PEPermutationT_vs_elt_inv a l l1 l2 :
    PEPermutationT l (l1 ++ a :: l2) ->
      {'(l', l'') & PEPermutationT (l' ++ l'') (l1 ++ l2) & l = l' ++ a :: l'' }.
  Proof.
  intros HP; apply PEPermutationT_vs_elt_subst in HP as [(l', l'') HP ->].
  exists (l', l''); [ apply (HP nil) | reflexivity ].
  Qed.

  Lemma PEPermutationT_vs_cons_inv a l l1 :
    PEPermutationT l (a :: l1) ->
      {'(l2, l3) & PEPermutationT (l2 ++ l3) l1 & l = l2 ++ a :: l3 }.
  Proof.
  intros HP; rewrite <- (app_nil_l l1).
  now apply PEPermutationT_vs_elt_inv.
  Qed.

  #[export] Instance PEPermtutationT_in a : Proper (PEPermutationT ==> Basics.impl) (In a).
  Proof.
  now case_perm; cbn; intros l l' HP HIn; subst; [ apply PermutationT_in with l | ].
  Qed.

  #[export] Instance PEPermtutationT_inT a : Proper (PEPermutationT ==> arrow) (InT a).
  Proof.
  now case_perm; cbn; intros l l' HP HIn; subst; [ apply PermutationT_inT with l | ].
  Qed.

  #[export] Instance PEPermutationT_Forall (P : A -> Prop) :
    Proper (PEPermutationT ==> Basics.impl) (Forall P).
  Proof.
  now case_perm; cbn; intros l1 l2 HP HF; subst; [ apply PermutationT_Forall with l1 | ].
  Qed.

  #[export] Instance PEPermutationT_Exists (P : A -> Prop) :
    Proper (PEPermutationT ==> Basics.impl) (Exists P).
  Proof.
  now case_perm; cbn; intros l1 l2 HP HF; subst; [ apply PermutationT_Exists with l1 | ].
  Qed.

  #[export] Instance PEPermutationT_ForallT (P : A -> Type) :
    Proper (PEPermutationT ==> arrow) (ForallT P).
  Proof.
  now case_perm; cbn; intros l1 l2 HP HF; subst; [ apply PermutationT_ForallT with l1 | ].
  Qed.

  #[export] Instance PEPermutationT_ExistsT (P : A -> Type) :
    Proper (PEPermutationT ==> arrow) (ExistsT P).
  Proof.
  now case_perm; cbn; intros l1 l2 HP HF; subst; [ apply PermutationT_ExistsT with l1 | ].
  Qed.

  #[export] Instance PEPermutationT_rev :
    Proper (PEPermutationT ==> PEPermutationT) (@rev A).
  Proof. now case_perm; intros l1 l2 HP; [ apply PermutationT_rev' | subst ].  Qed.


  (** * From [PEPermutationT] to [PCPermutationT] *)

  #[export] Instance PEPermutation_PCPermutationT_cons :
    Proper (eq ==> PEPermutationT ==> PCPermutationT) cons.
  Proof.
  intros x y -> l1 l2 HP.
  apply PEPermutation_PCPermutationT.
  now rewrite HP.
  Qed.

  #[export] Instance PEPermutation_PCPermutationT_app :
  Proper (PEPermutationT ==> PEPermutationT ==> PCPermutationT) (@app A).
  Proof.
  intros l1 l1' HPhd l2 l2' HPtl.
  apply PEPermutation_PCPermutationT.
  now rewrite HPhd, HPtl.
  Qed.

  Lemma PCPermutationT_vs_elt_inv a l l1 l2 :
    PCPermutationT l (l1 ++ a :: l2) ->
      {'(l', l'') & PEPermutationT (l2 ++ l1) (l'' ++ l') & l = l' ++ a :: l'' }.
  Proof.
  case_perm; intros HP.
  - destruct (PermutationT_vs_elt_inv _ _ _ HP) as ((l',l'') & ->).
    exists (l', l''); auto.
    apply PermutationT_app_inv in HP.
    symmetry in HP.
    etransitivity ; [ eapply PermutationT_app_comm | ].
    etransitivity ; [ eassumption | apply PermutationT_app_comm ].
  - destruct (CPermutationT_vs_elt_inv _ _ _ HP) as [(l',l'') Heq ->].
    exists (l', l''); auto.
  Qed.

  Lemma PCPermutationT_vs_cons_inv a l l1 :
    PCPermutationT l (a :: l1) ->
      {'(l', l'') & PEPermutationT l1 (l'' ++ l') & l = l' ++ a :: l'' }.
  Proof.
  intros HP; rewrite <- app_nil_l in HP.
  apply PCPermutationT_vs_elt_inv in HP as [(l', l'') HP ->].
  exists (l', l''); auto.
  now rewrite app_nil_r in HP.
  Qed.

  Lemma PCPermutationT_cons_cons_inv a1 a2 l1 l2 :
    PCPermutationT (a1 :: l1) (a2 :: l2) ->
      (a1 = a2) * PEPermutationT l1 l2
    + {'(l3, l4) & PEPermutationT l1 (l4 ++ a2 :: l3) & l2 = l3 ++ a1 :: l4 }.
  Proof.
  intros HP; symmetry in HP.
  apply PCPermutationT_vs_cons_inv in HP.
  destruct HP as [(l1',l2') HP' Heq].
  destruct l1' as [|a' l1']; inversion Heq; subst.
  - left; split; auto.
    now rewrite app_nil_r in HP'.
  - right; exists (l1', l2'); auto.
  Qed.

  Lemma PCPermutationT_cons_cons_notin_inv a l l1 :
    ~ In a l -> PCPermutationT (a :: l) (a :: l1) -> PEPermutationT l l1.
  Proof.
  intros Hin HP.
  apply PCPermutationT_cons_cons_inv in HP as [[Heq HP] | [(l3, l4) HP Heq]]; auto.
  exfalso.
  apply Hin, PermutationT_in with (l4 ++ a :: l3), in_elt.
  now symmetry in HP; apply PEPermutation_PermutationT.
  Qed.

End GPermutationT.

Section MultiGPermutationT.

  Variable A B : Type.
  Variable c : comparison.
  Variable b : bool.

  Lemma PCEPermutationT_Forall2T (P : A -> B -> Type) l1 l1' l2 :
    PCEPermutationT c l1 l1' -> Forall2T P l1 l2 ->
      { l2' & PCEPermutationT c l2 l2' & Forall2T P l1' l2' }.
  Proof.
  destruct c; [ apply CPermutationT_Forall2T | | apply PermutationT_Forall2T ].
  now cbn; intros -> HF; exists l2.
  Qed.

  Lemma PCPermutationT_Forall2T (P : A -> B -> Type) l1 l1' l2 :
    PCPermutationT b l1 l1' -> Forall2T P l1 l2 ->
      { l2' & PCPermutationT b l2 l2' & Forall2T P l1' l2' }.
  Proof.
  destruct b; [ apply PermutationT_Forall2T | apply CPermutationT_Forall2T ].
  Qed.

  Lemma PEPermutationT_Forall2T (P : A -> B -> Type) l1 l1' l2 :
    PEPermutationT b l1 l1' -> Forall2T P l1 l2 ->
      { l2' & PEPermutationT b l2 l2' & Forall2T P l1' l2' }.
  Proof.
  destruct b; [ apply PermutationT_Forall2T | cbn; intros; subst; now exists l2 ].
  Qed.

  Variable f : A -> B.

  #[export] Instance PCEPermutationT_map :
    Proper (PCEPermutationT c ==> PCEPermutationT c) (map f).
  Proof. now destruct c; intros l1 l2 ->. Qed.

  #[export] Instance PCPermutationT_map :
    Proper (PCPermutationT b ==> PCPermutationT b) (map f).
  Proof. now destruct b; intros l1 l2 ->. Qed.

  #[export] Instance PEPermutationT_map :
    Proper (PEPermutationT b ==> PEPermutationT b) (map f).
  Proof. now destruct b; cbn; intros l1 l2 HP; [ apply PermutationT_map | subst ]. Qed.

  Lemma PCEPermutationT_map_inv l1 l2 :
    PCEPermutationT c l1 (map f l2) -> { l3 & l1 = map f l3 & PCEPermutationT c l2 l3 }.
  Proof.
  destruct c; [ apply CPermutationT_map_inv | | apply PermutationT_map_inv ].
  now cbn; intros ->; exists l2.
  Qed.

  Lemma PCPermutationT_map_inv l1 l2 :
    PCPermutationT b l1 (map f l2) -> { l3 & l1 = map f l3 & PCPermutationT b l2 l3 }.
  Proof. destruct b; [ apply PermutationT_map_inv | apply CPermutationT_map_inv ]. Qed.

  Lemma PEPermutationT_map_inv l1 l2 :
    PEPermutationT b l1 (map f l2) -> { l3 & l1 = map f l3 & PEPermutationT b l2 l3 }.
  Proof. now destruct b; [ apply PermutationT_map_inv | exists l2 ]. Qed.

  Lemma PCEPermutationT_map_inv_inj (Hinj : injective f) l1 l2 :
    PCEPermutationT c (map f l1) (map f l2) -> PCEPermutationT c l1 l2.
  Proof.
  now destruct c;
  [ apply CPermutationT_map_inv_inj | apply map_injective | apply PermutationT_map_inv_inj ].
  Qed.

  Lemma PCPermutationT_map_inv_inj (Hinj : injective f) l1 l2 :
    PCPermutationT b (map f l1) (map f l2) -> PCPermutationT b l1 l2.
  Proof.
  now destruct b; [ apply PermutationT_map_inv_inj | apply CPermutationT_map_inv_inj ].
  Qed.

  Lemma PEPermutationT_map_inv_inj (Hinj : injective f) l1 l2 :
    PEPermutationT b (map f l1) (map f l2) -> PEPermutationT b l1 l2.
  Proof. now destruct b; [ apply PermutationT_map_inv_inj | apply map_injective ]. Qed.

  Lemma PCEPermutationT_image a l l' :
    PCEPermutationT c (a :: l) (map f l') -> { a' | a = f a' }.
  Proof.
  destruct c; [ apply CPermutationT_image | | apply PermutationT_image ].
  now cbn; intros Heq; destruct l' as [|a' l']; inversion Heq; subst; exists a'.
  Qed.

  Lemma PCPermutationT_image a l l' :
    PCPermutationT b (a :: l) (map f l') -> { a' | a = f a' }.
  Proof. destruct b; [ apply PermutationT_image | apply CPermutationT_image ]. Qed.

  Lemma PEPermutationT_image a l l' :
    PEPermutationT b (a :: l) (map f l') -> { a' | a = f a' }.
  Proof.
  destruct b ; [ apply PermutationT_image | ].
  now cbn; intros HP; destruct l' as [|a' l']; inversion HP; subst; exists a'.
  Qed.

  Variable c' : comparison.
  Variable b' : bool.

  Lemma PCEPermutationT_monot (Hle : ComparisonOrder.le c c') (l1 l2 : list A) :
    PCEPermutationT c l1 l2 -> PCEPermutationT c' l1 l2.
  Proof.
  destruct c, c'; cbn; try (now inversion Hle); try (now intros; subst).
  apply CPermutationT_PermutationT.
  Qed.

  Lemma PCPermutationT_monot (Hle : Bool.le b b') (l1 l2 : list A) :
    PCPermutationT b l1 l2 -> PCPermutationT b' l1 l2.
  Proof. destruct b, b'; try (now inversion Hle); apply CPermutationT_PermutationT. Qed.

  Lemma PEPermutationT_monot (Hle : Bool.le b b') (l1 l2 : list A) :
    PEPermutationT b l1 l2 -> PEPermutationT b' l1 l2.
  Proof. now destruct b, b'; try (now inversion Hle); cbn; intros ->. Qed.

End MultiGPermutationT.


(** * Solvinc tactics *)

(** unfolding into [PermutationT], [CPermutationT] or [eq] *)
Ltac hyps_GPermutationT_unfold :=
  match goal with
  | H : PCEPermutationT _ _ _ |- _ => unfold PCEPermutationT in H; hyps_GPermutationT_unfold
  | H : PCPermutationT _ _ _ |- _ => unfold PCPermutationT in H; hyps_GPermutationT_unfold
  | H : PEPermutationT _ _ _ |- _ => unfold PEPermutationT in H; hyps_GPermutationT_unfold
  | _ => idtac
  end.

(** automatic solving *)
Ltac GPermutationT_solve :=
  hyps_GPermutationT_unfold; cbn;
  match goal with
  | |- PCEPermutationT ?c _ _ => unfold PCEPermutationT; destruct c; cbn; GPermutationT_solve
  | |- PCPermutationT ?b _ _ => unfold PCPermutationT; destruct b; cbn; GPermutationT_solve
  | |- PEPermutationT ?b _ _ => unfold PEPermutationT; destruct b; cbn; GPermutationT_solve
  | |- PermutationT _ _  => PermutationT_solve
  | |- CPermutationT _ _  => CPermutationT_solve
  | |- eq _ _  => reflexivity
  end.
