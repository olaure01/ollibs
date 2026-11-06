(** Finite Set over Lists

We define an axiomatization of finite sets through their relation with lists.
Equality is required to be Rocq equality.
An implementation of the axioms is provided by sorted lists with no duplicate
for every type equiped with a Boolean-valued total order relation. *)

(** TODO
  - intersection
  - lattice structure
*)

From Stdlib Require Import Bool Morphisms.
From OLlibs Require Import dectype BOrders List_more.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


(** * Axiomatization *)

(** ** Double Inclusion of Lists *)

Definition set_equiv T (l1 l2 : list T) := incl l1 l2 /\ incl l2 l1.

#[export]
Instance set_equiv_equiv T : Equivalence (@set_equiv T).
Proof.
split.
- split; reflexivity.
- intros x y [Hxy Hyx]. split; assumption.
- intros x y z [Hxy Hyx] [Hyz Hzy]. split; etransitivity; eassumption.
Qed.

#[export]
Instance set_equiv_cons T : Proper (eq ==> @set_equiv T ==> @set_equiv T) cons.
Proof. intros x y <- l1 l2 [H12 H21]. split; apply incl_cons_cons; assumption. Qed.

#[export]
Instance set_equiv_app T : Proper (@set_equiv T ==> @set_equiv T ==> @set_equiv T) (@app T).
Proof.
intros l1 l2 [H12 H21] l1' l2' [H12' H21'].
split; (apply incl_app; [ apply incl_appl | apply incl_appr ]); assumption.
Qed.

#[export]
Instance set_equiv_in T : Proper (eq ==> @set_equiv T ==> iff) (@In T).
Proof. intros a b <- l1 l2 [H12 H21]. split; [ apply H12 | apply H21 ]. Qed.

#[export]
Instance set_equiv_remove T Hdec : Proper (eq ==> @set_equiv T ==> @set_equiv T) (remove Hdec).
Proof. intros a b <- l1 l2 [H12 H21]. split; apply remove_incl; assumption. Qed.


(** A finite set with elements in [A] is a type [M]
    related with [list A] as follows: *)
Class FinSet M A := {
  empty : M;
  add : A -> M -> M;
  elts : M -> list A;
  elts_empty : elts empty = nil;
  elts_add a m : set_equiv (elts (add a m)) (a :: elts m);
  elts_retract m : fold_right add empty (elts m) = m;
  set_equiv_eq l1 l2 : set_equiv l1 l2 -> fold_right add empty l1 = fold_right add empty l2 }.

Coercion FinSet_carrier M A : FinSet M A -> Type := fun _ => M.

(** [St] and [Elt] define a finite set construction over a type [K]
    if for any [A] in [K], [Set A] is a finite set with elements [Elt A]. *)
Definition FSConstructor K St Elt := forall A : K, FinSet (St A) (Elt A).


(** * Constructions and properties over finite sets *)

Section FSet2List.

  Variable M A : Type.
  Variable fm : FinSet M A.

  Definition list2fs := fold_right add empty.

  #[export]
  Instance list2fs_set_equiv : Proper (@set_equiv A ==> eq) list2fs := set_equiv_eq.

  Lemma list2fs_retract m : list2fs (elts m) = m.
  Proof. exact (elts_retract m). Qed.

  Lemma list2fs_nil : list2fs nil = empty.
  Proof. reflexivity. Qed.

  Lemma list2fs_elt l1 l2 a :
    list2fs (l1 ++ a :: l2) = add a (list2fs (l1 ++ l2)).
  Proof.
  symmetry.
  change (add a (list2fs (l1 ++ l2)))
    with (list2fs (a :: l1 ++ l2)).
  apply set_equiv_eq. split.
  - intros z [-> | [Hz|Hz]%in_app_or].
    + apply in_elt.
    + apply in_or_app. left. assumption.
    + apply in_or_app. right. apply in_cons. assumption.
  - intros z [Hz|[->|Hz]]%in_app_or.
    + apply in_cons, in_or_app. left. assumption.
    + apply in_eq.
    + apply in_cons, in_or_app. right. assumption.
  Qed.

  Lemma list2fs_cons l a : list2fs (a :: l) = add a (list2fs l).
  Proof. now rewrite <- (app_nil_l (a :: l)), list2fs_elt. Qed.

  Lemma elts_set_equiv l : set_equiv (elts (list2fs l)) l.
  Proof.
  induction l as [ | a l IH ]; cbn.
  - rewrite elts_empty. reflexivity.
  - rewrite elts_add, IH. reflexivity.
  Qed.

  #[export]
  Instance elts_set_equiv' : Proper (eq ==> @set_equiv A) elts.
  Proof. intros m1 m2 ->. reflexivity. Qed.

  Lemma elts_eq_nil m : elts m = nil -> m = empty.
  Proof. intro Heq. now assert (Hr := elts_retract m); rewrite Heq in Hr; simpl in Hr; subst. Qed.

  Lemma set_equiv_elts_eq m1 m2 : set_equiv (elts m1) (elts m2) -> m1 = m2.
  Proof. intros HP%set_equiv_eq. rewrite ! elts_retract in HP. assumption. Qed.

  Lemma add_swap m a b : add a (add b m) = add b (add a m).
  Proof.
  rewrite <- list2fs_retract. rewrite <- list2fs_retract at 1.
  apply list2fs_set_equiv. rewrite ! elts_add. split.
  - intros z [ -> | [ -> | Hz ] ]; [ apply in_cons, in_eq | apply in_eq | ].
    apply in_cons, in_cons. assumption.
  - intros z [ -> | [ -> | Hz ] ]; [ apply in_cons, in_eq | apply in_eq | ].
    apply in_cons, in_cons. assumption.
  Qed.

  Definition union m1 m2 := list2fs (elts m1 ++ elts m2).

  Lemma elts_union m1 m2 : set_equiv (elts (union m1 m2)) (elts m1 ++ elts m2).
  Proof. apply elts_set_equiv. Qed.

  Lemma union_empty_left m : union empty m = m.
  Proof. unfold union; rewrite elts_empty; apply elts_retract. Qed.

  Lemma union_empty_right m : union m empty = m.
  Proof. unfold union; rewrite elts_empty, app_nil_r; apply elts_retract. Qed.

  Lemma union_comm m1 m2 : union m1 m2 = union m2 m1.
  Proof.
  apply list2fs_set_equiv. split; (apply incl_app; [ apply incl_appr | apply incl_appl ]; reflexivity).
  Qed.

  Lemma union_ass m1 m2 m3 : union (union m1 m2) m3 = union m1 (union m2 m3).
  Proof.
  unfold union. apply set_equiv_eq.
  transitivity ((elts m1 ++ elts m2) ++ elts m3).
  - split.
    + apply incl_app; [ apply incl_appl | apply incl_appr ]; [ | reflexivity ].
      apply elts_set_equiv.
    + apply incl_app; [ apply incl_appl | apply incl_appr ]; [ | reflexivity ].
      apply elts_set_equiv.
  - rewrite <- app_assoc; symmetry.
    split.
    + apply incl_app; [ apply incl_appl | apply incl_appr ]; [ reflexivity | ].
      apply elts_set_equiv.
    + apply incl_app; [ apply incl_appl | apply incl_appr ]; [ reflexivity | ].
      apply elts_set_equiv.
  Qed.

  Lemma union_idem m : union m m = m.
  Proof.
  unfold union. rewrite <- (list2fs_retract m) at 3. apply list2fs_set_equiv. split.
  - intros z [Hz|Hz]%in_app_or; assumption.
  - apply incl_appl. reflexivity.
  Qed.

  Lemma union_add_comm m1 m2 a : union (add a m1) m2 = add a (union m1 m2).
  Proof.
  unfold union.
  change (add a (list2fs (elts m1 ++ elts m2))) with (list2fs (a :: elts m1 ++ elts m2)).
  apply list2fs_set_equiv. rewrite elts_add. reflexivity.
  Qed.

  Lemma list2fs_app l1 l2 : list2fs (l1 ++ l2) = union (list2fs l1) (list2fs l2).
  Proof.
  unfold union. apply set_equiv_eq.
  transitivity (elts (list2fs l1) ++ l2); symmetry.
  - rewrite elts_set_equiv. reflexivity.
  - rewrite !elts_set_equiv. reflexivity.
  Qed.

  Definition elt x m := In x (elts m).

  Lemma not_elt_empty x : ~ elt x empty.
  Proof. unfold elt. rewrite elts_empty. intros []. Qed.

  Lemma elt_add x m : elt x (add x m).
  Proof. unfold elt. rewrite elts_add. apply in_eq. Qed.

  Lemma elt_add_idem x m : elt x m -> add x m = m.
  Proof.
  intro Hin. apply set_equiv_elts_eq. rewrite elts_add. split.
  - intros a [->|Ha]; assumption.
  - intros a Ha. apply in_cons. assumption.
  Qed.

  Lemma elt_union x m1 m2 : elt x (union m1 m2) <-> elt x m1 \/ elt x m2.
  Proof.
  unfold elt. rewrite elts_union. split; intro Hin.
  - apply in_app_or in Hin as [Hin|Hin]; [ left | right ]; assumption.
  - apply in_or_app. assumption.
  Qed.

End FSet2List.

Arguments list2fs {_ _ _} _.
Arguments union {_ _ _} _ _.
Arguments elt {_ _ _} _ _.

Section DecidableEq.

  Variable A : DecType.
  Variable M : Type.
  Variable fm : FinSet M A.

  Definition card m := length (nodup eq_dt_dec (elts m)).

  Lemma card_empty : card empty = 0.
  Proof. unfold card. rewrite elts_empty. reflexivity. Qed.

  Definition rem x m := list2fs (remove eq_dt_dec x (elts m)).

  Lemma rem_sgt x : rem x (add x empty) = empty.
  Proof.
  unfold rem.
  (* Fail rewrite elts_add. *)
  rewrite <- (elts_retract empty) at 2.
  apply list2fs_set_equiv. rewrite elts_add. cbn. rewrite elts_empty, if_eq_dt_dec_refl. reflexivity.
  Qed.

  Lemma rem_elt x m : elt x m -> add x (rem x m) = m.
  Proof.
  intros [l1 [l2 Hin]]%in_split.
  unfold rem. rewrite Hin, remove_app. cbn. rewrite if_eq_dt_dec_refl, <- list2fs_elt.
  apply (set_equiv_elts_eq fm). rewrite Hin, elts_set_equiv.
  split.
  - apply incl_app.
    + apply incl_appl. intros a Hin1%in_remove. apply Hin1.
    + apply incl_appr. apply incl_cons_cons. intros a Hin2%in_remove. apply Hin2.
  - apply incl_app.
    + cons2app. rewrite app_assoc. apply incl_appl.
      intros a Ha. apply in_or_app.
      destruct (eq_dt_dec a x) as [-> | Hneq].
      * right. apply in_eq.
      * left. apply in_in_remove; assumption.
    + apply incl_appr.
      intros a [-> | Ha]; [ apply in_eq | ].
      destruct (eq_dt_dec a x) as [-> | Hneq].
      * apply in_eq.
      * apply in_cons. apply in_in_remove; assumption.
  Qed.

  Lemma rem_not_elt x m : ~ elt x m -> rem x m = m.
  Proof.
  intro Hnin.
  unfold rem, list2fs. rewrite <- elts_retract. f_equal.
  apply notin_remove. assumption.
  Qed.

  Lemma rem_union x m1 m2 : rem x (union m1 m2) = union (rem x m1) (rem x m2).
  Proof.
  unfold rem, union. apply list2fs_set_equiv.
  rewrite list2fs_app, elts_union, remove_app.
  apply set_equiv_app; rewrite !elts_set_equiv; reflexivity.
  Qed.

End DecidableEq.

Arguments card {_ _ _} _.
Arguments rem {_ _ _} _ _.

Section FSmap.

  Variable M A N B : Type.
  Variable fm : FinSet M A.
  Variable fm' : FinSet N B.
  Variable f : A -> B.

  Definition fsmap (m : M) := list2fs (map f (elts m)).

  Lemma list2fs_map l : list2fs (map f l) = fsmap (list2fs l).
  Proof. symmetry. apply set_equiv_eq. split; apply incl_map, elts_set_equiv. Qed.

  Lemma elts_fsmap m : set_equiv (elts (fsmap m)) (map f (elts m)).
  Proof.
  rewrite <- (elts_retract m).
  remember (elts m) as l eqn:Heql; clear m Heql; induction l; simpl.
  - unfold fsmap; rewrite elts_empty; simpl.
    now rewrite elts_empty.
  - apply elts_set_equiv.
  Qed.

End FSmap.

Arguments fsmap {_ _ _ _ _ _} _ _.


Section Induction.

  Variable M A : Type.
  Variable fm : FinSet M A.

  Lemma fs_rect (P : M -> Type) :
    P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
  Proof.
  intros He Ha m.
  remember (elts m) as l eqn:Heql'.
  assert (set_equiv l (elts m)) as Heql by (rewrite Heql'; reflexivity). clear Heql'.
  revert m Heql; induction l as [|a l IHl]; intros m Heql.
  - destruct (elts m) as [ | x l ] eqn:Hm; [ | destruct (proj2 Heql x (in_eq _ _)) ].
    apply elts_eq_nil in Hm; subst. assumption.
  - assert (Hr := elts_retract m).
    symmetry in Heql; rewrite (set_equiv_eq Heql) in Hr; simpl in Hr; subst.
    apply Ha, IHl.
    symmetry.
    change (fold_right add empty l) with (list2fs l).
    apply elts_set_equiv.
  Defined.

  Lemma fs_ind (P : M -> Prop) :
    P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
  Proof. intros. apply fs_rect; assumption. Defined.

  Lemma fs_rec (P : M -> Set) :
    P empty -> (forall a m, P m -> P (add a m)) -> forall m, P m.
  Proof. intros. apply fs_rect; assumption. Defined.

End Induction.


(** * Notations *)

Module FSetNotations.
  Infix ":::" := add (at level 60, right associativity).
  Infix "+++" := union (at level 60, right associativity).
  Notation " [[ ]] " := empty (at level 0).
  Notation " [[ x ]] " := (add x empty) (at level 0).
  Notation " [[ x ; .. ; y ]] " := (add x .. (add y empty) ..) (at level 0).
End FSetNotations.


(** ** Sorted lists with no duplicate as finite sets
  Sorted lists with no duplicate provide a finite sets construction for [BOrder]. *)

Lemma set_equiv_sorted_neq B (l : list (@car B)) : set_equiv l (fold_right insert_neq nil l).
Proof.
induction l as [ | x l IH ]; [ reflexivity | cbn; rewrite IH at 1 ].
split; [ apply insert_neq_incl_r | apply insert_neq_incl_l ].
Qed.

Definition NDSortedList B := { s : SortedList B | nodup_sortedb _ (proj1_sig s) = true }.

Lemma nd_sortedlist_equality B (m1 m2 : NDSortedList B) :
  proj1_sig (proj1_sig m1) = proj1_sig (proj1_sig m2) -> m1 = m2.
Proof.
destruct m1 as [m1 Hnd1], m2 as [m2 Hnd2]. cbn. intros ->%sortedlist_equality.
f_equal. apply (Eqdep_dec.UIP_dec bool_dec).
Qed.


Definition fsslist_empty B : NDSortedList B.
Proof. exists (exist (fun x => is_sorted x = true) nil eq_refl). reflexivity. Defined.

Lemma fmslist_add B : @car B -> SortedList B -> SortedList B.
Proof. intros a m. exists (insert_neq a (proj1_sig m)). apply (insert_neq_sorted a m). Defined.

Lemma fsslist_add B : @car B -> NDSortedList B -> NDSortedList B.
Proof.
intros a m. exists (fmslist_add a (proj1_sig m)). 
destruct m as [m Hnd]. cbn in *.
destruct (nodup_sortedb_spec _ _ (proj1 (insert_neq_sorted a m))) as [ | Hd ]; [ reflexivity | ].
exfalso. apply Hd.
destruct m as [m Hs]; cbn in *.
apply NoDup_insert_neq; [ assumption | ].
destruct (nodup_sortedb_spec _ _ Hs); [ assumption | discriminate Hnd ].
Defined.

Lemma insert_neq_add B (a : @car B) l :
  proj1_sig (proj1_sig (fsslist_add a l)) = insert_neq a (proj1_sig (proj1_sig l)).
Proof. reflexivity. Qed.

Lemma proj1_sorted_neq B l :
  proj1_sig (proj1_sig (fold_right (@fsslist_add B) (@fsslist_empty _) l)) = fold_right insert_neq nil l.
Proof. induction l as [ | x l IH ]; [ | cbn; rewrite IH ]; reflexivity. Qed.

Theorem FSConstr_slist : FSConstructor NDSortedList (@car).
Proof.
intro A.
split with (fsslist_empty A) (@fsslist_add A) (fun z => (@proj1_sig _ _ (@proj1_sig _ _ z))).
- reflexivity.
- intros a m. split; [ apply insert_neq_incl_l | apply insert_neq_incl_r ].
- intros [[l Hs] Hnd].
  induction l as [ | a l IHl ] in Hs, Hnd |- *.
  + now apply nd_sortedlist_equality.
  + destruct l as [ | a' l ]; apply nd_sortedlist_equality; cbn; [ reflexivity | ].
    simpl proj1_sig in Hnd.  rewrite nodup_sortedb_cons_cons in Hnd.
    apply andb_true_iff in Hnd as [Ha'a%negb_true_iff Hnd].
    apply andb_true_iff in Hs as [Haa' Hs].
    assert (H' := IHl Hs Hnd).
    apply (f_equal (@proj1_sig _ _)) in H'.
    apply (f_equal (@proj1_sig _ _)) in H'.
    cbn in H'. rewrite H'. cbn. rewrite Haa', Ha'a. reflexivity.
- intros l1 l2 Heq.
  rewrite (set_equiv_sorted_neq _ l1), (set_equiv_sorted_neq _ l2) in Heq.
  remember (fold_right insert_neq nil l1) as m1 eqn:H1.
  remember (fold_right insert_neq nil l2) as m2 eqn:H2.
  assert (is_sorted m1 = true) as Hs1 by (subst; apply is_sorted_sorted_neq).
  assert (is_sorted m2 = true) as Hs2 by (subst; apply is_sorted_sorted_neq).
  assert (nodup_sortedb _ m1 = true) as Hnd1 by (subst; apply nodup_sorted_neq).
  assert (nodup_sortedb _ m2 = true) as Hnd2 by (subst; apply nodup_sorted_neq).
  enough (m1 = m2) as Heq'.
  { apply nd_sortedlist_equality. rewrite !proj1_sorted_neq. subst. assumption. }
  clear l1 l2 H1 H2.
  induction m1 as [ | a1 m1 IH1 ] in m2, Hs1, Hs2, Hnd1, Hnd2, Heq |- *; cbn.
  + destruct Heq as [_ Heq]. apply incl_l_nil in Heq as ->. reflexivity.
  + destruct m2 as [ | a2 m2 ].
    { destruct Heq as [Heq _]. apply incl_l_nil in Heq as [=]. }
    destruct Heq as [H12 H21].
    apply incl_cons_inv in H12 as [H12a H12].
    apply incl_cons_inv in H21 as [H21a H21].
    assert (a1 = a2) as <-.
    { destruct H12a as [-> | H12a]; [reflexivity | ].
      destruct H21a as [-> | H21a]; [reflexivity | ].
      apply (is_sorted_in _ _ _ _ Hs2) in H12a.
      apply (is_sorted_in _ _ _ _ Hs1) in H21a.
      apply (asym H21a H12a). }
    f_equal. apply IH1.
    * split.
      -- intros z Hz.
         destruct (H12 z Hz) as [ -> | ]; [ exfalso | assumption ].
         destruct (nodup_sortedb_spec _ _ Hs1) as [ Hnd | ]; [ | discriminate Hnd1 ].
         inversion Hnd. contradiction.
      -- intros z Hz.
         destruct (H21 z Hz) as [ -> | ]; [ exfalso | assumption ].
         destruct (nodup_sortedb_spec _ _ Hs2) as [ Hnd | ]; [ | discriminate Hnd2 ].
         inversion Hnd. contradiction.
    * apply (is_sorted_tail _ _ _ Hs1).
    * apply (is_sorted_tail _ _ _ Hs2).
    * cbn in Hnd1. destruct m1 as [ | b1 m1 ]; [ reflexivity | ].
      apply andb_true_iff in Hnd1. apply Hnd1.
    * cbn in Hnd2. destruct m2 as [ | b2 m2 ]; [ reflexivity | ].
      apply andb_true_iff in Hnd2. apply Hnd2.
Defined.
