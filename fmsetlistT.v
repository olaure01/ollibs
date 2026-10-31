(** Finite Multiset over Lists relying on [PermutationT]

We define an axiomatization of finite multisets through their relation with lists.
Equality is required to be Rocq equality.
Permutation are with output in [Type].
An implementation of the axioms is provided by sorted lists
for every type equiped with a Boolean-valued total order relation. *)

From Stdlib Require Import Bool List CMorphisms.
From OLlibs Require Import BOrders PermutationT_more.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


(** * Axiomatization *)

(** A finite multiset with elements in [A] is a type [M]
    related with [list A] as follows: *)
Class FinMultiset M A := {
  empty : M;
  add : A -> M -> M;
  elts : M -> list A;
  elts_add a m : PermutationT (elts (add a m)) (a :: elts m);
  elts_retract m : fold_right add empty (elts m) = m;
  perm_eq l1 l2 : PermutationT l1 l2 -> fold_right add empty l1 = fold_right add empty l2 }.

Coercion FinMultiset_carrier M A : FinMultiset M A -> Type := fun _ => M.

(** [Mst] and [Elt] define a finite multiset construction over a type [K]
    if for any [A] in [K], [Mst A] is a finite multiset with elements [Elt A]. *)
Definition FMConstructor K Mst Elt := forall A : K, FinMultiset (Mst A) (Elt A).


(** * Constructions and properties over finite multisets *)

Section FMSet2List.

  Variable M A : Type.
  Variable fm : FinMultiset M A.

  Definition list2fm := fold_right add empty.

  #[export]
  Instance list2fm_perm : Proper (@PermutationT A ==> eq) list2fm := perm_eq.

  Lemma list2fm_retract m : list2fm (elts m) = m.
  Proof. exact (elts_retract m). Qed.

  Lemma list2fm_nil : list2fm nil = empty.
  Proof. reflexivity. Qed.

  Lemma list2fm_elt l1 l2 a :
    list2fm (l1 ++ a :: l2) = add a (list2fm (l1 ++ l2)).
  Proof.
  symmetry.
  change (add a (list2fm (l1 ++ l2)))
    with (list2fm (a :: l1 ++ l2)).
  apply perm_eq, PermutationT_middle.
  Qed.

  Lemma list2fm_cons l a : list2fm (a :: l) = add a (list2fm l).
  Proof. now rewrite <- (app_nil_l (a :: l)), list2fm_elt. Qed.

  Lemma elts_perm_empty l : PermutationT (elts (list2fm l)) (l ++ elts empty).
  Proof. induction l as [|a l IHl]; [ | cbn; rewrite elts_add, IHl ]; reflexivity. Qed.

  Lemma elts_empty : elts empty = nil.
  Proof.
  apply PermutationT_nil, (PermutationT_app_inv_l (elts empty)).
  rewrite app_nil_r, <- list2fm_retract at 1.
  apply elts_perm_empty.
  Qed.

  Lemma elts_sgt a : elts (add a empty) = a :: nil.
  Proof.
  assert (HP := elts_add a empty). rewrite elts_empty in HP.
  destruct (elts (add a empty)) as [ | b [ | c l ] ].
  - apply PermutationT_nil in HP as [=].
  - apply PermutationT_length_1 in HP as ->. reflexivity.
  - apply PermutationT_length in HP as [=].
  Qed.

  Lemma elts_perm l : PermutationT (elts (list2fm l)) l.
  Proof. rewrite <- (app_nil_r l) at 2. rewrite <- elts_empty. apply elts_perm_empty. Qed.

  #[export]
  Instance elts_perm' : Proper (eq ==> @PermutationT A) elts.
  Proof. intros m1 m2 ->. reflexivity. Qed.

  Lemma elts_eq_nil m : elts m = nil -> m = empty.
  Proof. intro Heq. now assert (Hr := elts_retract m); rewrite Heq in Hr; simpl in Hr; subst. Qed.

  Lemma PermutationT_elts_eq m1 m2 : PermutationT (elts m1) (elts m2) -> m1 = m2.
  Proof. intros HP%perm_eq. rewrite ! elts_retract in HP. assumption. Qed.

  Lemma add_swap m a b : add a (add b m) = add b (add a m).
  Proof.
  rewrite <- list2fm_retract. rewrite <- list2fm_retract at 1.
  apply list2fm_perm. rewrite ! elts_add. apply PermutationT_swap.
  Qed.

  Lemma add_inj m1 m2 a : add a m1 = add a m2 -> m1 = m2.
  Proof.
  intro Heq.
  apply PermutationT_elts_eq, (@PermutationT_cons_inv _ _ _ a).
  rewrite <- ! elts_add, Heq. reflexivity.
  Qed.

  Definition sum m1 m2 := list2fm (elts m1 ++ elts m2).

  Lemma elts_sum m1 m2 : PermutationT (elts (sum m1 m2)) (elts m1 ++ elts m2).
  Proof. apply elts_perm. Qed.

  Lemma sum_empty_left m : sum empty m = m.
  Proof. unfold sum; rewrite elts_empty; apply elts_retract. Qed.

  Lemma sum_empty_right m : sum m empty = m.
  Proof. unfold sum; rewrite elts_empty, app_nil_r; apply elts_retract. Qed.

  Lemma sum_comm m1 m2 : sum m1 m2 = sum m2 m1.
  Proof. apply list2fm_perm, PermutationT_app_comm. Qed.

  Lemma sum_ass m1 m2 m3 : sum (sum m1 m2) m3 = sum m1 (sum m2 m3).
  Proof.
  unfold sum. apply perm_eq.
  transitivity ((elts m1 ++ elts m2) ++ elts m3).
  - apply PermutationT_app_tail, elts_perm.
  - rewrite <- app_assoc; symmetry.
    apply PermutationT_app_head, elts_perm.
  Qed.

  Lemma sum_add_comm m1 m2 a : sum (add a m1) m2 = add a (sum m1 m2).
  Proof.
  unfold sum.
  change (add a (list2fm (elts m1 ++ elts m2))) with (list2fm (a :: elts m1 ++ elts m2)).
  apply list2fm_perm. rewrite elts_add. reflexivity.
  Qed.

  Lemma list2fm_app l1 l2 : list2fm (l1 ++ l2) = sum (list2fm l1) (list2fm l2).
  Proof.
  unfold sum. apply perm_eq.
  transitivity (elts (list2fm l1) ++ l2); symmetry.
  - apply PermutationT_app_tail, elts_perm.
  - apply PermutationT_app_head, elts_perm.
  Qed.

End FMSet2List.

Arguments list2fm {_ _ _} _.
Arguments sum {_ _ _} _ _.


Section Fmmap.

 Variable M A N B : Type.
 Variable fm : FinMultiset M A.
 Variable fm' : FinMultiset N B.
 Variable f : A -> B.

  Definition fmmap (m : M) := list2fm (map f (elts m)).

  Lemma list2fm_map l : list2fm (map f l) = fmmap (list2fm l).
  Proof. symmetry. apply perm_eq, PermutationT_map, elts_perm. Qed.

  Lemma elts_fmmap m : PermutationT (elts (fmmap m)) (map f (elts m)).
  Proof.
  rewrite <- (elts_retract m).
  remember (elts m) as l eqn:Heql; clear m Heql; induction l; simpl.
  - unfold fmmap; rewrite elts_empty; simpl.
    now rewrite elts_empty.
  - apply elts_perm.
  Qed.

End Fmmap.

Arguments fmmap {_ _ _ _ _ _} _ _.


Section Induction.

  Variable M A : Type.
  Variable fm : FinMultiset M A.

  Lemma fm_rect (P : M -> Type) :
    P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
  Proof.
  intros He Ha m.
  remember (elts m) as l eqn:Heql.
  apply PermutationT_refl' in Heql; unfold id in Heql.
  revert m Heql; induction l as [|a l IHl]; intros m Heql.
  - apply PermutationT_nil in Heql.
    now apply elts_eq_nil in Heql; subst.
  - assert (Hr := elts_retract m).
    symmetry in Heql; rewrite (perm_eq Heql) in Hr; simpl in Hr; subst.
    apply Ha, IHl.
    symmetry.
    change (fold_right add empty l) with (list2fm l).
    apply elts_perm.
  Defined.

  Lemma fm_ind (P : M -> Prop) :
    P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
  Proof. intros. apply fm_rect; assumption. Defined.

  Lemma fm_rec (P : M -> Set) :
    P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
  Proof. intros. apply fm_rect; assumption. Defined.

End Induction.


Section Flatten.

  Variable A M MM : Type.
  Variable fm : FinMultiset M A.
  Variable fmfm : FinMultiset MM M.

  Definition flatten mm := (fold_right sum empty) (elts mm).

  Lemma flatten_empty : flatten empty = empty.
  Proof. unfold flatten. rewrite elts_empty. reflexivity. Qed.

  Lemma flatten_add m mm : flatten (add m mm) = sum m (flatten mm).
  Proof.
  unfold flatten.
  change (sum m (fold_right sum empty (elts mm)))
    with (fold_right sum empty (m :: elts mm)).
  apply PermutationT_fold_right, elts_add.
  intros. rewrite <- !sum_ass. f_equal. apply sum_comm.
  Qed.

  Lemma flatten_sgt a : flatten (add a empty) = a.
  Proof. rewrite flatten_add, flatten_empty, sum_empty_right. reflexivity. Qed.

  Lemma flatten_map_sgt l : flatten (list2fm (map (fun x => add x empty) l)) = list2fm l.
  Proof.
  induction l as [ | m l IH ]; [ apply flatten_empty | cbn ].
  rewrite flatten_add, IH, sum_add_comm, sum_empty_left. reflexivity.
  Qed.

End Flatten.


(** * Notations *)

Module FMSetNotations.
  Infix ":::" := add (at level 60, right associativity).
  Infix "+++" := sum (right associativity, at level 60).
  Notation " [[ ]] " := empty.
  Notation " [[ x ]] " := (add x empty).
  Notation " [[ x ; .. ; y ]] " := (add x .. (add y empty) ..).
End FMSetNotations.


(** ** Sorted lists as finite multisets
  Sorted lists provide a finite multisets construction for [BOrder]. *)

Definition fmslist_empty B : SortedList B := exist _ nil eq_refl.

Lemma fmslist_add B : @car B -> SortedList B -> SortedList B.
Proof. intros a m. exists (insert a (proj1_sig m)). apply (insert_sorted a m). Defined.

Lemma insert_add B (a : @car B) l :
  proj1_sig (fmslist_add a l) = insert a (proj1_sig l).
Proof. reflexivity. Qed.

Theorem FMConstr_slist : FMConstructor SortedList (@car).
Proof.
intro A.
split with (fmslist_empty A) (@fmslist_add A) (@proj1_sig _ _).
- intros a [l Hsort]. induction l as [ |a' l IHl ] in Hsort |- * ; [ reflexivity | cbn ].
  destruct (leb a a'); [ reflexivity | ].
  change (a :: a' :: l) with ((a :: nil) ++ a' :: l).
  apply PermutationT_cons_app.
  apply is_sorted_tail in Hsort.
  apply (IHl Hsort).
- intros [l Hsort].
  induction l as [ | a l IHl ] in Hsort |- *.
  + now apply sortedlist_equality.
  + destruct l as [ | a' l ]; apply sortedlist_equality; cbn; [ reflexivity | ].
    apply andb_true_iff in Hsort as [Ha Hsort].
    assert (H' := IHl Hsort).
    apply (f_equal (@proj1_sig _ _)) in H'.
    cbn in H'. rewrite H'. cbn. rewrite Ha. reflexivity.
- intros l1 l2 HP. induction HP as [| ? ? ? ? IHP | | ? ? ? ? IHP ];
    [ | cbn; rewrite IHP | | cbn; rewrite IHP ]; [ reflexivity .. | | assumption ].
  apply sortedlist_equality, insert_insert.
Defined.

Definition FMConstr_slist_slist B := FMConstr_slist (border_slist B).
