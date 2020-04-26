(* BOrders Library *)

(** * Class of Boolean-valued total orders *)

Require Import Bool PeanoNat Wf_nat Lia List Orders.
Require Import funtheory.

Definition BRelation A := A -> A -> bool.

Class BOrder := {
  carrier : Type ;
  leqb : BRelation carrier ;
  total : forall a b, leqb a b = false -> leqb b a = true ;
  asym :  forall a b, leqb a b = true -> leqb b a = true -> a = b ;
  trans : forall a b c, leqb a b = true -> leqb b c = true -> leqb a c = true
}.

(** Equivalence with UsualOrderedTypeFull. *)
Module BOrder_to_UsualOrderedTypeFull : UsualOrderedTypeFull.

  Parameter B : BOrder.

  Definition t := @carrier B.
  Definition eq := @eq (@carrier B).
  Definition eq_equiv : Equivalence eq := eq_equivalence.
  Local Coercion is_true : bool >-> Sortclass.
  Definition lt x y := @leqb B x y /\ x <> y.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
  split.
  - intros a.
    unfold complement.
    intros [Hleq Hneq].
    apply Hneq ; reflexivity.
  - intros a b c [Hleq1 Hneq1] [Hleq2 Hneq2] ; split.
    + eapply trans ; eassumption.
    + intros Heq ; subst.
      case_eq (leqb b c) ; intros Heqbb ;
        [ case_eq (leqb c b) ; intros Heqbb2 | ].
      * apply asym in Heqbb ; try assumption ; subst.
        apply Hneq1 ; reflexivity.
      * rewrite Heqbb2 in Hleq1 ; inversion Hleq1.
      * rewrite Heqbb in Hleq2 ; inversion Hleq2.
  Qed.

  Lemma lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
  intros a b H1 c d H2 ; unfold eq in H1 ; unfold eq in H2 ;
    subst; reflexivity.
  Qed.

  Definition compare x y :=
    if @leqb B x y then (if leqb y x then Eq else Lt) else Gt.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
  intros.
  unfold compare.
  case_eq (leqb x y).
  - case_eq (leqb y x) ; constructor.
    + apply asym ; assumption.
    + split ; try assumption.
      intros Heq ; subst.
      rewrite H0 in H ; inversion H.
  - constructor.
    assert (Ht := total _ _ H).
    split ; try assumption.
    intros Heq ; subst.
    rewrite Ht in H ; inversion H.
  Qed.

  Lemma eq_dec : forall x y, {eq x y} + {eq x y -> False}.
  Proof.
  intros.
  case_eq (leqb x y) ; case_eq (leqb y x) ; intros Heq1 Heq2.
  - apply asym in Heq1 ; try assumption ; subst.
    left ; reflexivity.
  - right ; intros Heq ; unfold eq in Heq ; subst.
    rewrite Heq1 in Heq2 ; inversion Heq2.
  - right ; intros Heq ; unfold eq in Heq ; subst.
    rewrite Heq1 in Heq2 ; inversion Heq2.
  - apply total in Heq1.
    rewrite Heq1 in Heq2 ; inversion Heq2.
  Qed.

  Definition le x y := is_true (@leqb B x y).

  Lemma le_lteq : forall x y, le x y <-> lt x y \/ eq x y.
  Proof.
  intros x y; split.
  - intros Hle.
    destruct (eq_dec x y).
    + right ; assumption.
    + left ; split ; assumption.
  - intros [[Hle Heq] | Heq]; auto.
    rewrite Heq.
    case_eq (leqb y y) ; intros Heq2.
    + unfold le.
      rewrite Heq2 ; reflexivity.
    + exfalso.
      assert (Heq3 := total _ _ Heq2).
      rewrite Heq2 in Heq3 ; inversion Heq3.
  Qed.

End BOrder_to_UsualOrderedTypeFull.

Module UsualOrderedTypeFull_to_BOrder (T : UsualOrderedTypeFull).

  Definition leb x y :=
  match T.compare x y with
  | Gt => false
  | _  => true
  end.

  Lemma leb_le : forall x y, leb x y = true -> T.le x y.
  Proof.
  unfold leb.
  intros.
  apply T.le_lteq.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt] ;
    try reflexivity.
  - right ; assumption.
  - left ; assumption.
  - discriminate.
  Qed.

  Lemma le_leb : forall x y, T.le x y -> leb x y = true.
  Proof.
  intros x y H.
  unfold leb.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt] ;
    intros ; try reflexivity.
  destruct (StrictOrder_Irreflexive x).
  apply T.le_lteq in H.
  destruct H as [ Hlt | Heq ].
  - transitivity y ; assumption.
  - rewrite <- Heq in Hgt ; assumption.
  Qed.

  Lemma nleb_lt : forall x y, leb x y = false -> T.lt y x.
  Proof.
  unfold leb.
  intros.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt] ;
    try reflexivity ; try discriminate ; try assumption.
  Qed.

  Lemma lt_nleb : forall x y, T.lt y x -> leb x y = false.
  Proof.
  intros x y H.
  unfold leb.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt] ;
    intros ; try reflexivity ; subst.
  - apply StrictOrder_Irreflexive in H.
    destruct H.
  - apply (StrictOrder_Transitive _ _ _ H) in Hlt.
    apply StrictOrder_Irreflexive in Hlt.
    destruct Hlt.
  Qed.

  Lemma to_BOrder : BOrder.
  Proof.
  split with T.t leb.
  - intros a b Hf.
    apply nleb_lt in Hf.
    apply le_leb.
    apply T.le_lteq.
    left ; assumption.
  - intros a b H1 H2.
    apply leb_le in H1.
    apply leb_le in H2.
    apply T.le_lteq in H1.
    apply T.le_lteq in H2.
    destruct H1 as [H1|H1], H2 as [H2|H2]; auto.
    apply (StrictOrder_Transitive _ _ _ H2) in H1.
    apply StrictOrder_Irreflexive in H1.
    destruct H1.
  - intros a b c H1 H2.
    apply le_leb ; apply T.le_lteq.
    apply leb_le in H1.
    apply leb_le in H2.
    apply T.le_lteq in H1.
    apply T.le_lteq in H2.
    destruct H1 ; destruct H2 ; subst.
    + left ; transitivity b ; assumption.
    + left ; assumption.
    + left ; assumption.
    + right ; reflexivity.
  Qed.

End UsualOrderedTypeFull_to_BOrder.

(** * [BOrder] structure over [nat]. *)
Instance border_nat : BOrder.
Proof.
split with nat Nat.leb; intros.
- case (Nat.compare_spec a b); intros Ho; apply Nat.leb_le; try lia.
  exfalso.
  eapply or_introl, Nat.le_lteq, Nat.leb_le in Ho.
  rewrite Ho in H; inversion H.
- apply Nat.leb_le in H.
  apply Nat.leb_le in H0; lia.
- apply Nat.leb_le in H.
  apply Nat.leb_le in H0.
  apply Nat.leb_le; lia.
Defined.

Lemma border_inj {A B} (f : A -> @carrier B) (Hi : injective f) : BOrder.
Proof with try eassumption.
split with A (fun x y => leqb (f x) (f y)) ; intros.
- apply total...
- apply Hi.
  apply asym...
- eapply trans...
Defined.




(** * Sorted lists over [BOrder] *)

(** ** Insertion sort *)

Fixpoint insert {B} (a : @carrier B) (l : list (@carrier B)) :=
match l with
| nil => a :: nil
| b :: t => if (leqb a b) then a :: b :: t
                          else b :: (insert a t)
end.

Lemma insert_insert {B} : forall (x y : @carrier B) l,
  insert y (insert x l) = insert x (insert y l).
Proof with try reflexivity.
induction l ; simpl.
- case_eq (leqb x y) ; intros Heqbb1 ;
  case_eq (leqb y x) ; intros Heqbb2...
  + apply (asym _ _ Heqbb1) in Heqbb2 ; subst...
  + apply total in Heqbb1.
    rewrite Heqbb1 in Heqbb2 ; now discriminate Heqbb2.
- case_eq (leqb x a) ; intros Heqbb1 ;
  case_eq (leqb y a) ; intros Heqbb2 ; simpl ;
    try rewrite Heqbb1 ; try rewrite Heqbb2...
  + case_eq (leqb x y) ; intros Heqbb ;
    case_eq (leqb y x) ; intros Heqbb' ;
      try rewrite Heqbb1 ; try rewrite Heqbb2...
    * apply (asym _ _ Heqbb) in Heqbb' ; subst...
    * apply total in Heqbb.
      rewrite Heqbb in Heqbb' ; now discriminate Heqbb'.
  + case_eq (leqb y x) ; intros Heqbb' ;
      try rewrite Heqbb1 ; try rewrite Heqbb2...
    apply (trans _ _ _ Heqbb') in Heqbb1.
    rewrite Heqbb1 in Heqbb2 ; now discriminate Heqbb2.
  + case_eq (leqb x y) ; intros Heqbb ;
      try rewrite Heqbb1 ; try rewrite Heqbb2...
    apply (trans _ _ _ Heqbb) in Heqbb2.
    rewrite Heqbb1 in Heqbb2 ; now discriminate Heqbb2.
  + rewrite IHl...
Qed.

(** ** Sorted lists *)

Fixpoint is_sorted {B} (l : list (@carrier B)) :=
match l with
| nil => true
| a :: nil => true
| a :: (b :: _) as r => leqb a b && is_sorted r
end.

Lemma is_sorted_tail {B} : forall a l,
  @is_sorted B (a :: l) = true -> is_sorted l = true.
Proof.
intros a l Hs.
destruct l.
- reflexivity.
- apply andb_true_iff in Hs.
  apply Hs.
Qed.

Definition SortedList B := { m | @is_sorted B m = true }.

Lemma sortedlist_equality : forall B (m1 m2 : SortedList B),
  proj1_sig m1 = proj1_sig m2 -> m1 = m2.
Proof.
intros B em1 em2 Heq.
destruct em1 as [m1 B1].
destruct em2 as [m2 B2].
simpl in Heq ; subst.
f_equal.
apply (Eqdep_dec.UIP_dec bool_dec).
Qed.

Lemma insert_sorted {B} : forall s a (m : SortedList B),
  length (proj1_sig m) = s ->
  let l := insert a (proj1_sig m) in
    is_sorted l = true /\ l <> nil
 /\ forall c, In c l -> In c (proj1_sig m) \/ c = a.
Proof with try reflexivity ; try assumption.
induction s as [s IH] using (well_founded_induction lt_wf).
intros a m Hlen l.
destruct m as [l0 Hsort].
destruct l0 ; (split ; [ | split ])...
- intro Heq ; discriminate Heq.
- intros c Hc.
  inversion Hc.
  + right ; rewrite H...
  + inversion H.
- unfold l ; simpl.
  case_eq (leqb a c) ; intros Heqbb.
  + apply andb_true_iff ; split...
  + destruct s ; inversion Hlen.
    destruct (IH s (le_n _) a (exist _ l0 (is_sorted_tail _ _ Hsort)) H0)
      as [Hsort' _].
    apply total in Heqbb.
    destruct l0 ; try (apply andb_true_iff ; split)...
    simpl.
    simpl in Hsort'.
    destruct (leqb a c0) ; apply andb_true_iff ; split...
    clear Hlen l.
    simpl in Hsort.
    apply andb_true_iff in Hsort.
    apply Hsort.
- intro Heq.
  unfold l in Heq.
  simpl in Heq.
  destruct (leqb a c) ; discriminate Heq.
- intros d Hd.
  unfold l in Hd.
  simpl in Hd.
  destruct (leqb a c).
  + inversion Hd ; [ right ; rewrite H | left ]...
  + inversion Hd.
    * left ; left...
    * destruct s ; inversion Hlen.
      destruct (IH s (le_n _) a (exist _ l0 (is_sorted_tail _ _ Hsort)) H1)
        as [_ Hin].
      apply Hin in H.
      destruct H ; [ left ; apply in_cons | right ]...
Qed.
