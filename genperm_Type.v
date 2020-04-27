(** * Factorized statements for different notions of permutation *)

Require Import List CMorphisms.
Require Import funtheory Permutation_Type_more Permutation_Type_solve
               CPermutation_Type CPermutation_Type_solve.

Set Implicit Arguments.

(** ** Definitions
 parametrized by a boolean. *)

(** Permutation or cyclic permutation *)
Definition PCperm_Type A (b : bool) :=
  if b then @Permutation_Type A else @CPermutation_Type A.

(** Permutation or equality *)
Definition PEperm_Type A (b : bool) :=
  if b then @Permutation_Type A else @eq (list A).


(** ** Permutation or cyclic permutation *)

(** unfolding into [Permutation] or [CPermutation] *)
Ltac hyps_PCperm_Type_unfold :=
  match goal with
  | H : PCperm_Type _ _ _ |- _ => unfold PCperm_Type in H ; hyps_PCperm_Type_unfold
  | _ => idtac
  end.

(** automatic solving *)
Ltac PCperm_Type_solve :=
  hyps_PCperm_Type_unfold ;
  simpl ;
  match goal with
  | |- PCperm_Type ?b _ _ => unfold PCperm_Type ; destruct b ;
                        simpl ; PCperm_Type_solve
  | |- Permutation_Type _ _  => perm_Type_solve
  | |- CPermutation_Type _ _  => cperm_Type_solve
  end.

(** *** Properties *)

Instance PCperm_perm_Type A b : Proper (PCperm_Type b ==> (@Permutation_Type A)) id.
Proof.
destruct b; intros l l' HP; auto.
now apply cperm_perm_Type.
Qed.

Instance cperm_PCperm_Type A b : Proper (@CPermutation_Type A ==> PCperm_Type b) (@id (list A)).
Proof.
destruct b; intros l l' HC; auto.
now apply cperm_perm_Type.
Qed.

Lemma PCperm_Type_monot A : forall b1 b2, Bool.leb b1 b2 ->
  forall l1 l2 : list A, PCperm_Type b1 l1 l2 -> PCperm_Type b2 l1 l2.
Proof.
intros b1 b2 Hleb l1 l2.
destruct b1; destruct b2; try (now inversion Hleb).
apply cperm_perm_Type.
Qed.

Instance PCperm_Type_refl A b : Reflexive (@PCperm_Type A b).
Proof.
destruct b; intros l.
- apply Permutation_Type_refl.
- apply cperm_Type_refl.
Qed.

Instance PCperm_Type_sym A b : Symmetric (@PCperm_Type A b).
Proof.
destruct b; intros l l' H.
- now apply Permutation_Type_sym.
- now apply cperm_Type_sym.
Qed.

Instance PCperm_Type_trans A b : Transitive (@PCperm_Type A b).
Proof.
destruct b ; intros l l' l'' H1 H2.
- now apply Permutation_Type_trans with l'.
- now apply cperm_Type_trans with l'.
Qed.

Instance PCperm_Type_equiv A b : Equivalence (@PCperm_Type A b).
Proof.
split.
- apply PCperm_Type_refl.
- apply PCperm_Type_sym.
- apply PCperm_Type_trans.
Qed.

Lemma PCperm_Type_swap A b : forall a1 a2 : A,
  PCperm_Type b (a1 :: a2 :: nil) (a2 :: a1 :: nil).
Proof.
destruct b ; intros.
- apply Permutation_Type_swap.
- apply cperm_Type_swap.
Qed.

Lemma PCperm_Type_last A b : forall (a : A) l,
  PCperm_Type b (a :: l) (l ++ a :: nil).
Proof.
destruct b; intros; rewrite <- (app_nil_l l), app_comm_cons.
- apply Permutation_Type_cons_append.
- apply cperm_Type_last.
Qed.

Lemma PCperm_Type_app_comm A b : forall l l',
  @PCperm_Type A b (l ++ l') (l' ++ l).
Proof.
destruct b; intros.
- apply Permutation_Type_app_comm.
- apply cperm_Type.
Qed.

Lemma PCperm_Type_app_rot A b : forall l1 l2 l3,
  @PCperm_Type A b  (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof.
destruct b; intros.
- apply Permutation_Type_app_rot.
- apply cperm_Type_app_rot.
Qed.

Lemma PCperm_Type_nil A b : forall l,
  @PCperm_Type A b nil l -> l = nil.
Proof.
destruct b; intros.
- now apply Permutation_Type_nil.
- now apply cperm_Type_nil.
Qed.

Lemma PCperm_Type_nil_cons A b : forall l (a : A),
  PCperm_Type b nil (a :: l) -> False.
Proof.
destruct b; intros l a.
- now apply Permutation_Type_nil_cons.
- now apply cperm_Type_nil_cons.
Qed.

Lemma PCperm_Type_length_1_inv A b : forall (a : A) l,
  PCperm_Type b (a :: nil) l -> l = a :: nil.
Proof.
destruct b; intros.
- now apply Permutation_Type_length_1_inv.
- now apply cperm_Type_one_inv.
Qed.

Lemma PCperm_Type_length_2_inv A b : forall (a1 : A) a2 l,
  PCperm_Type b (a1 :: a2 :: nil) l -> { l = a1 :: a2 :: nil } + { l = a2 :: a1 :: nil }.
Proof.
destruct b; intros.
- now apply Permutation_Type_length_2_inv.
- now apply cperm_Type_two_inv.
Qed.

Lemma PCperm_Type_vs_elt_inv A b : forall (a : A) l l1 l2,
  PCperm_Type b l (l1 ++ a :: l2) ->
  {' (l1',l2') : _ & l = l1' ++ a :: l2' & PEperm_Type b (l2 ++ l1) (l2' ++ l1') }.
Proof.
destruct b ; intros a l l1 l2 HC.
- assert (Heq := HC).
  apply Permutation_Type_vs_elt_inv in Heq.
  destruct Heq as ((l' & l'') & Heq) ; subst.
  exists (l',l''); auto.
  simpl in HC ; simpl.
  apply Permutation_Type_app_inv in HC.
  apply Permutation_Type_sym in HC.
  eapply Permutation_Type_trans ; [ eapply Permutation_Type_app_comm | ].
  eapply Permutation_Type_trans ; [ eassumption | ].
  apply Permutation_Type_app_comm.
- apply cperm_Type_vs_elt_inv in HC.
  destruct HC as [(l' & l'') Heq1 Heq2] ; subst.
  now exists (l',l'').
Qed.

Lemma PCperm_Type_vs_cons_inv A b : forall (a : A) l l1,
  PCperm_Type b l (a :: l1) ->
  {' (l1',l2') : _ & l = l1' ++ a :: l2' & PEperm_Type b l1 (l2' ++ l1') }.
Proof.
intros a l l1 HP.
rewrite <- app_nil_l in HP.
apply PCperm_Type_vs_elt_inv in HP.
destruct HP as [(l' & l'') HP Heq] ; subst.
rewrite app_nil_r in Heq.
now exists (l',l'').
Qed.

Lemma PCperm_Type_cons_vs_cons A B : forall (a b : A) la lb,
  PCperm_Type B (b :: lb) (a :: la) ->
    ( prod (a = b) (PEperm_Type B lb la) )
  + { '(l1,l2) : _ & lb = l1 ++ a :: l2 & PEperm_Type B la (l2 ++ b :: l1) }.
Proof.
intros a b l1 l2 HP.
apply PCperm_Type_vs_cons_inv in HP.
destruct HP as [(l1',l2') Heq HP'].
destruct l1' ; inversion Heq ; subst.
- left; split; auto.
  rewrite app_nil_r in HP'.
  destruct B; symmetry; apply HP'.
- right; exists (l1', l2'); auto.
Qed.

Instance PCperm_Type_map A B (f : A -> B) b :
  Proper (PCperm_Type b ==> PCperm_Type b) (map f).
Proof.
destruct b; intros l1 l2 HC.
- now apply Permutation_Type_map.
- now apply cperm_Type_map.
Qed.

Lemma PCperm_Type_map_inv A B b : forall (f : A -> B) l1 l2,
  PCperm_Type b l1 (map f l2) ->
  { l : _ & l1 = map f l & (PCperm_Type b l2 l) }.
Proof.
destruct b; intros.
- now apply Permutation_Type_map_inv.
- now apply cperm_Type_map_inv.
Qed.

Instance PCperm_Type_in A b (a : A) : Proper (PCperm_Type b ==> Basics.impl) (In a).
Proof.
destruct b; intros l l' HP HIn.
- now apply Permutation_Type_in with l.
- now apply cperm_Type_in with l.
Qed.

Instance PCperm_Type_Forall A b (P : A -> Prop) :
  Proper (PCperm_Type b ==> Basics.impl) (Forall P).
Proof.
destruct b; intros l1 l2 HP HF.
- now apply Permutation_Type_Forall with l1.
- now apply cperm_Type_Forall with l1.
Qed.

Instance PCperm_Type_Exists A b (P : A -> Prop) :
  Proper (PCperm_Type b ==> Basics.impl) (Exists P).
Proof.
destruct b; intros l1 l2 HP HE.
- now apply Permutation_Type_Exists with l1.
- now apply cperm_Type_Exists with l1.
Qed.

Lemma PCperm_Type_Forall2 A B b (P : A -> B -> Type) :
  forall l1 l1' l2, PCperm_Type b l1 l1' -> Forall2_inf P l1 l2 ->
    { l2' : _ & PCperm_Type b l2 l2' & Forall2_inf P l1' l2' }.
Proof.
destruct b; [ apply Permutation_Type_Forall2 | apply cperm_Type_Forall2 ].
Qed.

Lemma PCperm_Type_image A B b : forall (f : A -> B) a l l',
  PCperm_Type b (a :: l) (map f l') -> { a' | a = f a' }.
Proof.
destruct b; intros.
- now apply Permutation_Type_image with l l'.
- now apply cperm_Type_image with l l'.
Qed.

Instance PCperm_Type_Forall_Type A b (P : A -> Type) :
  Proper (PCperm_Type b ==> Basics.arrow) (Forall_inf P).
Proof.
destruct b; intros l1 l2 HP.
- now apply Permutation_Type_Forall_Type.
- now apply cperm_Type_Forall_Type.
Qed.

Instance PCperm_Type_Exists_Type A b (P : A -> Type) :
  Proper (PCperm_Type b ==> Basics.arrow) (Exists_inf P).
Proof.
destruct b; intros l1 l2 HP.
- now apply Permutation_Type_Exists_Type.
- now apply cperm_Type_Exists_Type.
Qed.


(** ** Permutation or equality *)

(** unfolding into [Permutation] or [eq] and automatic solving *)
Ltac hyps_PEperm_Type_unfold :=
  match goal with
  | H : PEperm_Type _ _ _ |- _ => unfold PEperm_Type in H ; hyps_PEperm_Type_unfold
  | _ => idtac
  end.

(** automatic solving *)
Ltac PEperm_Type_solve :=
  hyps_PEperm_Type_unfold ;
  simpl ;
  match goal with
  | |- PEperm_Type ?b _ _ => unfold PEperm_Type ; destruct b ;
                        simpl ; PEperm_Type_solve
  | |- Permutation_Type _ _  => perm_Type_solve
  | |- eq _ _  => reflexivity
  end.

(** *** Properties *)

Instance PEperm_perm_Type A b : Proper (PEperm_Type b ==> (@Permutation_Type A)) id.
Proof. destruct b; intros l l' HP; simpl in HP; now subst. Qed.

Lemma PEperm_Type_monot A : forall b1 b2, Bool.leb b1 b2 ->
  forall l1 l2 : list A, PEperm_Type b1 l1 l2 -> PEperm_Type b2 l1 l2.
Proof.
intros b1 b2 Hleb l1 l2.
destruct b1; destruct b2; try (now inversion Hleb).
now simpl; intros HP; subst.
Qed.

Instance PEperm_Type_refl A b : Reflexive (@PEperm_Type A b).
Proof. destruct b ; intros l; reflexivity. Qed.

Instance PEperm_Type_sym A b : Symmetric (@PEperm_Type A b).
Proof. destruct b; intros l l' HP; now symmetry. Qed.

Instance PEperm_Type_trans A b : Transitive (@PEperm_Type A b).
Proof.
destruct b; intros l l' l''.
- now apply Permutation_Type_trans.
- now transitivity l'.
Qed.

Instance PEperm_Type_equiv A b : Equivalence (@PEperm_Type A b).
Proof.
split.
- apply PEperm_Type_refl.
- apply PEperm_Type_sym.
- apply PEperm_Type_trans.
Qed.

Instance eq_PEperm_Type A b : Proper (eq ==> PEperm_Type b) (@id (list A)).
Proof. destruct b; intros l l' Heq; subst; reflexivity. Qed.

Instance PEperm_Type_cons A b :
  Proper (eq ==> PEperm_Type b ==> PEperm_Type b) (@cons A).
Proof.
destruct b; intros x y Heq l1 l2 HP; subst.
- now apply Permutation_Type_cons.
- now rewrite HP.
Qed.

Instance PEperm_Type_app A b : Proper (PEperm_Type b ==> PEperm_Type b ==> PEperm_Type b) (@app A).
Proof.
destruct b; simpl; intros l m HP1 l' m' HP2.
- now apply Permutation_Type_app.
- now subst.
Qed.

Lemma PEperm_Type_app_tail A b : forall l l' tl : list A,
  PEperm_Type b l l' -> PEperm_Type b (l ++ tl) (l' ++ tl).
Proof.
destruct b; simpl; intros l l' tl HP.
- now apply Permutation_Type_app_tail.
- now subst.
Qed.

Lemma PEperm_Type_app_head A b : forall l tl tl' : list A,
  PEperm_Type b tl tl' -> PEperm_Type b (l ++ tl) (l ++ tl').
Proof.
destruct b; simpl; intros l tl tl' HP.
- now apply Permutation_Type_app_head.
- now subst.
Qed.

Lemma PEperm_Type_add_inside A b : forall (a : A) l l' tl tl',
  PEperm_Type b l l' -> PEperm_Type b tl tl' -> PEperm_Type b (l ++ a :: tl) (l' ++ a :: tl').
Proof.
destruct b; simpl; intros a l l' tl tl' HP1 HP2.
- now apply Permutation_Type_add_inside.
- now subst.
Qed.

Lemma PEperm_Type_nil A b : forall l, @PEperm_Type A b nil l -> l = nil.
Proof.
destruct b; intros.
- now apply Permutation_Type_nil.
- now symmetry.
Qed.

Lemma PEperm_nil_cons A b : forall l (a : A),
  PEperm_Type b nil (a :: l) -> False.
Proof.
destruct b; intros l a H.
- now apply Permutation_Type_nil_cons with _ l a.
- inversion H.
Qed.

Lemma PEperm_Type_length_1_inv A b : forall (a : A) l,
  PEperm_Type b (a :: nil) l -> l = a :: nil.
Proof.
destruct b; intros.
- now apply Permutation_Type_length_1_inv.
- now symmetry.
Qed.

Lemma PEperm_Type_length_2_inv A b : forall (a1 : A) a2 l,
  PEperm_Type b (a1 :: a2 :: nil) l -> { l = a1 :: a2 :: nil } + { l = a2 :: a1 :: nil }.
Proof.
destruct b; intros.
- now apply Permutation_Type_length_2_inv.
- now left; symmetry.
Qed.

Lemma PEperm_Type_vs_elt_inv A b : forall (a : A) l l1 l2,
  PEperm_Type b l (l1 ++ a :: l2) ->
  {'(l1', l2') & l = l1' ++ a :: l2' & PEperm_Type b (l1 ++ l2) (l1' ++ l2') }.
Proof.
destruct b; simpl; intros a l l1 l2 HP; subst.
- destruct (Permutation_Type_vs_elt_inv _ _ _ HP) as ((l',l'') & Heq) ; subst.
  apply Permutation_Type_app_inv, Permutation_Type_sym in HP.
  now exists (l', l'').
- now exists (l1, l2).
Qed.

Lemma PEperm_Type_vs_cons_inv A b : forall (a : A) l l1,
  PEperm_Type b l (a :: l1) ->
  {'(l1', l2') : _ & l = l1' ++ a :: l2' & PEperm_Type b l1 (l1' ++ l2') }.
Proof.
intros a l l1 HP.
rewrite <- (app_nil_l l1).
now apply PEperm_Type_vs_elt_inv.
Qed.

Instance PEperm_Type_in A b (a : A) : Proper (PEperm_Type b ==> Basics.impl) (In a).
Proof.
destruct b; simpl; intros l l' HP HIn; subst; auto.
now apply Permutation_Type_in with l.
Qed.

Instance PEperm_Type_Forall A b (P : A -> Prop) :
  Proper (PEperm_Type b ==> Basics.impl) (Forall P).
Proof.
destruct b; simpl; intros l1 l2 HP HF; subst; auto.
now apply Permutation_Type_Forall with l1.
Qed.

Instance PEperm_Type_Exists A b (P : A -> Prop) :
  Proper (PEperm_Type b ==> Basics.impl) (Exists P).
Proof.
destruct b; simpl; intros l1 l2 HP HF; subst; auto.
now apply Permutation_Type_Exists with l1.
Qed.

Lemma PEperm_Type_Forall2 A B b (P : A -> B -> Prop) :
  forall l1 l1' l2, PEperm_Type b l1 l1' -> Forall2_inf P l1 l2 ->
    { l2' : _ & PEperm_Type b l2 l2' & Forall2_inf P l1' l2' }.
Proof.
destruct b; [ apply Permutation_Type_Forall2 | ].
intros l1 l1' l2 HE HF; simpl in HE; subst.
now exists l2.
Qed.

Instance PEperm_Type_map A B (f : A -> B) b :
  Proper (PEperm_Type b ==> PEperm_Type b) (map f).
Proof.
destruct b; intros l l' HP; simpl in HP; subst.
- now apply Permutation_Type_map.
- reflexivity.
Qed.

Instance PEperm_Type_Forall_Type A b (P : A -> Type) :
  Proper (PEperm_Type b ==> Basics.arrow) (Forall_inf P).
Proof.
destruct b; simpl; intros l1 l2 HP HF; subst; auto.
now apply Permutation_Type_Forall_Type with l1.
Qed.

Instance PEperm_Type_Exists_Type A b (P : A -> Type) :
  Proper (PEperm_Type b ==> Basics.arrow) (Exists_inf P).
Proof.
destruct b; simpl; intros l1 l2 HP HF; subst; auto.
now apply Permutation_Type_Exists_Type with l1.
Qed.

Lemma PEperm_Type_map_inv A B b : forall (f : A -> B) l1 l2,
  PEperm_Type b l1 (map f l2) ->
  { l : _ & l1 = map f l & (PEperm_Type b l2 l) }.
Proof.
destruct b; simpl; intros f l1 l2 HP.
- now apply Permutation_Type_map_inv.
- now subst; exists l2.
Qed.

Instance PEperm_Type_rev A b : Proper (PEperm_Type b ==> PEperm_Type b) (@rev A).
Proof.
destruct b ; intros l1 l2 HP.
- now apply Permutation_Type_rev'.
- now (simpl in HP ; subst).
Qed.

Lemma PEperm_Type_map_inv_inj A B b : forall f : A -> B, injective f ->
  forall l1 l2, PEperm_Type b (map f l1) (map f l2) -> PEperm_Type b l1 l2.
Proof.
destruct b; intros f Hi l1 l2 HP.
- now apply Permutation_Type_map_inv_inj in HP.
- now apply map_injective in HP.
Qed.

Lemma PEperm_Type_image A B b : forall (f : A -> B) a l l',
  PEperm_Type b (a :: l) (map f l') -> { a' | a = f a' }.
Proof.
destruct b ; intros f a l l' H.
- now apply Permutation_Type_image with l l'.
- destruct l'; inversion H; subst.
  now exists a0.
Qed.


(** ** From PEperm to PCperm *)

Instance PEperm_PCperm_Type A b : Proper (PEperm_Type b ==> PCperm_Type b) (@id (list A)).
Proof.
destruct b; simpl; intros l l' HP; auto.
subst ; apply cperm_Type_refl.
Qed.

Instance PEperm_PCperm_Type_cons A b :
  Proper (eq ==> PEperm_Type b ==> PCperm_Type b) (@cons A).
Proof.
intros x y Heq l1 l2 HP ; subst.
apply PEperm_PCperm_Type.
now apply PEperm_Type_cons.
Qed.

Instance PEperm_PCperm_Type_app A b :
  Proper (PEperm_Type b ==> PEperm_Type b ==> PCperm_Type b) (@app A).
Proof.
intros l1 l1' HPhd l2 l2' HPtl.
apply PEperm_PCperm_Type.
now rewrite HPhd, HPtl.
Qed.
