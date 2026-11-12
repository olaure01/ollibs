(** Boolean-valued total orders as a [Class] *)

From Stdlib Require Import Bool PeanoNat Wf_nat Lia Permutation Orders.
From OLlibs Require Import funtheory dectype List_more.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Proof Using Clear Unused.
Set Implicit Arguments.

(* TODO make closer to [DecType] *)


(** * Class of Boolean-valued total orders *)

Definition brelation A := A -> A -> bool.

Class BOrder := {
  car :> Type;
  leb : brelation car;
  total a b : leb a b = false -> leb b a = true;
  asym a b : leb a b = true -> leb b a = true -> a = b;
  trans a b c : leb a b = true -> leb b c = true -> leb a c = true }.
Arguments total [_ _ _] _.
Arguments asym [_ _ _] _ _.
Arguments trans [_ _ _ _] _ _, [_ _ _] _ _ _, [_] _ _ _ _ _.

Section Properties.

Variable B : BOrder.

Lemma refl (x : @car B) : leb x x = true.
Proof.
destruct (leb x x) eqn:Hx; [ reflexivity | ].
assert (Hnx := total Hx). rewrite <- Hx, <- Hnx. reflexivity.
Qed.

Definition BOrder_dec : DecType.
Proof using B.
split with car
           (fun a b => leb a b && leb b a).
intros x y. split.
- intros [Heq1 Heq2]%andb_true_iff.
  apply (asym Heq1 Heq2).
- intros <-. rewrite refl. reflexivity.
Defined.

End Properties.

Coercion BOrder_dec : BOrder >-> DecType.


(** ** Equivalence with [UsualOrderedTypeFull] *)
Module Type ModBOrder.
  Parameter t : BOrder.
End ModBOrder.

Module ModBOrder_as_UsualOrderedTypeFull (B : ModBOrder) : UsualOrderedTypeFull.

  Definition t := @car B.t.
  Definition eq := @eq B.t.
  Definition eq_equiv : Equivalence eq := eq_equivalence.
  #[local] Coercion is_true : bool >-> Sortclass.
  Definition lt x y := @leb B.t x y /\ x <> y.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
  split.
  - intros a [Hleq Hneq]. apply Hneq. reflexivity.
  - intros a b c [Hleq1 Hneq1] [Hleq2 Hneq2]. split.
    + eapply trans; eassumption.
    + intros ->.
      destruct (leb b c) eqn: Heqbb1; [ destruct (leb c b) eqn:Heqbb2 | ].
      * apply asym in Heqbb1 as ->; [ | assumption ].
        apply Hneq1. reflexivity.
      * discriminate Hleq1.
      * discriminate Hleq2.
  Qed.

  Lemma lt_compat : Proper (eq==>eq==>iff) lt.
  Proof. intros a b H1 c d H2. unfold eq in H1, H2. subst. reflexivity. Qed.

  Definition compare x y := if @leb B.t x y then (if leb y x then Eq else Lt) else Gt.

  Lemma compare_spec x y : CompSpec eq lt x y (compare x y).
  Proof.
  unfold compare.
  destruct (leb x y) eqn:Hlebx; [ destruct (leb y x) eqn:Hleby | ]; constructor.
  - apply asym; assumption.
  - split; [ assumption | ].
    intros ->.
    rewrite Hlebx in Hleby. discriminate Hleby.
  - assert (Ht := total Hlebx).
    split; [ assumption | ].
    intros ->.
    rewrite Ht in Hlebx. discriminate Hlebx.
  Qed.

  Lemma eq_dec x y : {eq x y} + {~ eq x y}.
  Proof.
  destruct (leb x y) eqn:Heq1, (leb y x) eqn:Heq2.
  - destruct (asym Heq1 Heq2). left. reflexivity.
  - right. intros Heq. unfold eq in Heq. subst.
    rewrite Heq1 in Heq2. discriminate Heq2.
  - right. intros Heq. unfold eq in Heq. subst.
    rewrite Heq1 in Heq2. discriminate Heq2.
  - apply total in Heq1. rewrite Heq1 in Heq2. discriminate Heq2.
  Qed.

  Definition le x y := is_true (@leb B.t x y).

  Lemma le_lteq x y : le x y <-> lt x y \/ eq x y.
  Proof.
  split.
  - intro Hle.
    destruct (eq_dec x y).
    + right. assumption.
    + left. split; assumption.
  - intros [[Hle Heq] | ->]; [ assumption | ].
    destruct (leb y y) eqn:Heq2.
    + assumption.
    + exfalso.
      assert (Heq3 := total Heq2).
      rewrite Heq2 in Heq3. discriminate Heq3.
  Qed.

End ModBOrder_as_UsualOrderedTypeFull.

Module UsualOrderedTypeFull_as_BOrder (T : UsualOrderedTypeFull).

  Definition leb x y :=
  match T.compare x y with
  | Gt => false
  | _  => true
  end.

  Lemma leb_le x y : leb x y = true -> T.le x y.
  Proof.
  unfold leb. intro Hcmp.
  apply T.le_lteq.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt ].
  - right. assumption.
  - left. assumption.
  - discriminate Hcmp.
  Qed.

  Lemma le_leb x y : T.le x y -> leb x y = true.
  Proof.
  intro Hle. unfold leb.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt]; [ reflexivity | reflexivity | ].
  destruct (StrictOrder_Irreflexive x).
  apply T.le_lteq in Hle as [ Hlt | -> ].
  - transitivity y; assumption.
  - assumption.
  Qed.

  Lemma nleb_lt x y : leb x y = false -> T.lt y x.
  Proof.
  unfold leb. intro Hleb.
  destruct (T.compare_spec x y) as [ Heq | Hlt | Hgt];
    [ discriminate Hleb | discriminate Hleb | assumption ].
  Qed.

  Lemma lt_nleb x y : T.lt y x -> leb x y = false.
  Proof.
  unfold leb. intro Hlty.
  destruct (T.compare_spec x y) as [ -> | Hlt | Hgt]; [ | | reflexivity ].
  - apply StrictOrder_Irreflexive in Hlty as [].
  - apply (StrictOrder_Transitive _ _ _ Hlty) in Hlt.
    apply StrictOrder_Irreflexive in Hlt as [].
  Qed.

  Lemma to_BOrder : BOrder.
  Proof.
  split with T.t leb.
  - intros a b Hf%nleb_lt. apply le_leb, T.le_lteq.
    left. assumption.
  - intros a b [H1|H1]%leb_le%T.le_lteq [H2|H2]%leb_le%T.le_lteq; auto.
    apply (StrictOrder_Transitive _ _ _ H2) in H1.
    apply StrictOrder_Irreflexive in H1 as [].
  - intros a b c [ H1 | -> ]%leb_le%T.le_lteq [ H2 | -> ]%leb_le%T.le_lteq; apply le_leb, T.le_lteq.
    + left. transitivity b; assumption.
    + left. assumption.
    + left. assumption.
    + right. reflexivity.
  Qed.

End UsualOrderedTypeFull_as_BOrder.

Module UsualOrderedTypeFull_as_ModBOrder (T : UsualOrderedTypeFull) : ModBOrder.
  Module TBOrder := UsualOrderedTypeFull_as_BOrder T.
  Definition t := TBOrder.to_BOrder.
End UsualOrderedTypeFull_as_ModBOrder.


(** * [BOrder] structure over [nat]. *)
#[export]
Instance border_nat : BOrder.
Proof.
split with nat Nat.leb; intros a b.
- intros Hleb.
  case (Nat.compare_spec a b); intros Ho; apply Nat.leb_le; [ lia | | lia ].
  exfalso.
  eapply or_introl, Nat.le_lteq, Nat.leb_le in Ho.
  rewrite Ho in Hleb. discriminate Hleb.
- intros Hleb%Nat.leb_le Hleb2%Nat.leb_le. lia.
- intros c Hleb%Nat.leb_le Hleb2%Nat.leb_le. apply Nat.leb_le. lia.
Defined.

Lemma border_inj A B (f : A -> @car B) (Hi : injective f) : BOrder.
Proof.
split with A (fun x y => leb (f x) (f y)); intros a b; intros.
- apply total. assumption.
- apply Hi, asym; assumption.
- apply trans with (f b); assumption.
Defined.


(** * Sorted lists over [BOrder] *)

(** ** Insertion functions respecting order (with and without duplicates) *)

Fixpoint insert B (a : @car B) l :=
  match l with
  | nil => a :: nil
  | b :: t => if leb a b then a :: b :: t
                         else b :: insert B a t
  end.
Arguments insert {_} _ _.

Lemma insert_insert B (x y : @car B) l :
  insert y (insert x l) = insert x (insert y l).
Proof.
induction l as [|a l IHl]; cbn.
- destruct (leb x y) eqn:Heqbb1, (leb y x) eqn:Heqbb2; try reflexivity.
  + apply (asym Heqbb1) in Heqbb2 as ->. reflexivity.
  + apply total in Heqbb1. rewrite Heqbb1 in Heqbb2. discriminate Heqbb2.
- destruct (leb x a) eqn:Heqbb1, (leb y a) eqn:Heqbb2; cbn.
  + destruct (leb x y) eqn:Heqbb, (leb y x) eqn:Heqbb'; rewrite ? Heqbb1, ? Heqbb2; try reflexivity.
    * apply (asym Heqbb') in Heqbb as ->. reflexivity.
    * apply total in Heqbb'. rewrite Heqbb' in Heqbb. discriminate Heqbb.
  + destruct (leb y x) eqn:Heqbb'; rewrite ? Heqbb1, ? Heqbb2; try reflexivity.
    apply (trans Heqbb') in Heqbb1. rewrite Heqbb1 in Heqbb2. discriminate Heqbb2.
  + destruct (leb x y) eqn:Heqbb; rewrite ? Heqbb1, ? Heqbb2; try reflexivity.
    apply (trans Heqbb) in Heqbb2. rewrite Heqbb1 in Heqbb2. discriminate Heqbb2.
  + rewrite Heqbb1, Heqbb2, IHl. reflexivity.
Qed.

Lemma Permutation_insert B (x : @car B) l : Permutation (insert x l) (x :: l).
Proof.
induction l as [| y l IHl]; [ reflexivity | ].
cbn. destruct (leb x y); [ reflexivity | ].
change (x :: y :: l) with ((x :: nil) ++ y :: l).
apply Permutation_cons_app, IHl.
Qed.

Fixpoint insert_neq B (a : @car B) l :=
  match l with
  | nil => a :: nil
  | b :: t => if leb a b then if leb b a then b :: t
                                         else a :: b :: t
                         else b :: insert_neq B a t
  end.
Arguments insert_neq {_} _ _.

Lemma insert_neq_insert_neq B (x y : @car B) l :
  insert_neq y (insert_neq x l) = insert_neq x (insert_neq y l).
Proof.
induction l as [|a l IHl]; cbn.
- destruct (leb x y) eqn:Heqbb1, (leb y x) eqn:Heqbb2; try reflexivity.
  + apply (asym Heqbb1) in Heqbb2 as ->. reflexivity.
  + apply total in Heqbb1. rewrite Heqbb1 in Heqbb2. discriminate Heqbb2.
- destruct (leb x a) eqn:Heqbb1, (leb y a) eqn:Heqbb2; cbn.
  + destruct (leb x y) eqn:Heqbb, (leb y x) eqn:Heqbb'; rewrite ? Heqbb1, ? Heqbb2.
    * apply (asym Heqbb') in Heqbb as ->. reflexivity.
    * destruct (leb a x) eqn:Heqbb''; cbn; rewrite ?Heqbb2, ?Heqbb'.
      -- apply (trans Heqbb'') in Heqbb. rewrite !Heqbb. cbn. rewrite Heqbb1, Heqbb''. reflexivity.
      -- destruct (leb a y) eqn:Heqbb'''.
         ++ cbn. rewrite Heqbb1, Heqbb''. reflexivity.
         ++ cbn. rewrite Heqbb, Heqbb'. reflexivity.
    * destruct (leb a x) eqn:Heqbb''; cbn.
      -- rewrite Heqbb2.
         destruct (leb a y) eqn:Heqbb'''; cbn.
         ++ exfalso.
            apply (trans Heqbb1) in Heqbb'''. rewrite Heqbb''' in Heqbb. discriminate Heqbb.
         ++ rewrite Heqbb, Heqbb1, Heqbb''. reflexivity.
      -- rewrite Heqbb', Heqbb.
         destruct (leb a y) eqn:Heqbb'''; cbn.
         ++ exfalso.
            apply (trans Heqbb''') in Heqbb'. rewrite Heqbb' in Heqbb''. discriminate Heqbb''.
         ++ rewrite Heqbb, Heqbb1, Heqbb''. reflexivity.
    * apply total in Heqbb'. rewrite Heqbb' in Heqbb. discriminate Heqbb.
  + destruct (leb y x) eqn:Heqbb'; rewrite ?Heqbb1, ?Heqbb2.
    * apply (trans Heqbb') in Heqbb1. rewrite Heqbb1 in Heqbb2. discriminate Heqbb2.
    * destruct (leb a x) eqn:Heqbb''; cbn; rewrite ?Heqbb2, ?Heqbb'; reflexivity.
  + destruct (leb x y) eqn:Heqbb; rewrite ? Heqbb1, ? Heqbb2.
    * apply (trans Heqbb) in Heqbb2. rewrite Heqbb1 in Heqbb2. discriminate Heqbb2.
    * destruct (leb a y) eqn:Heqbb''; cbn; rewrite ?Heqbb1, ?Heqbb; reflexivity.
  + rewrite Heqbb1, Heqbb2, IHl. reflexivity.
Qed.

Lemma insert_neq_in B (x : @car B) l : In x (insert_neq x l).
Proof.
induction l as [| y l IHl]; [ apply in_eq | ].
cbn. destruct (leb x y) eqn:Hxy.
- destruct (leb y x) eqn:Hyx; [ rewrite (asym Hxy Hyx) | ]; apply in_eq.
- apply in_cons, IHl.
Qed.

Lemma insert_neq_incl B (x : @car B) l : incl l (insert_neq x l).
Proof.
induction l as [| y l IHl]; [ apply incl_nil_l | ].
cbn. destruct (leb x y) eqn:Hxy.
- intros z [ -> | Hz ].
  + destruct (leb z x) eqn:Hzx.
    * apply in_eq.
    * apply in_cons, in_eq.
  + destruct (leb y x); apply in_cons; [ | apply in_cons ]; assumption.
- apply incl_cons_cons, IHl.
Qed.

Lemma insert_neq_incl_l B (x : @car B) l : incl (insert_neq x l) (x :: l).
Proof.
induction l as [| y l IHl]; [ reflexivity | ].
cbn. destruct (leb x y) eqn:Hxy.
- destruct (leb y x) eqn:Hyx; [ apply incl_tl | ]; reflexivity.
- intros z [ -> | [-> | Hz]%IHl ].
  + apply in_cons, in_eq.
  + apply in_eq.
  + apply in_cons, in_cons, Hz.
Qed.

Lemma insert_neq_incl_r B (x : @car B) l : incl (x :: l) (insert_neq x l).
Proof.
induction l as [| y l IHl]; [ reflexivity | ].
cbn. destruct (leb x y) eqn:Hxy.
- destruct (leb y x) eqn:Hyx.
  + rewrite (asym Hxy Hyx).
    apply incl_cons; [ apply in_eq | reflexivity ].
  + reflexivity.
- intros z [ -> | [ -> | Hz ] ].
  + apply in_cons, insert_neq_in.
  + apply in_eq.
  + apply in_cons, insert_neq_incl, Hz.
Qed.

Lemma insert_neq_inT B (x : @car B) l : InT x (insert_neq x l).
Proof.
induction l as [| y l IHl]; [ apply inT_eq | ].
cbn. destruct (leb x y) eqn:Hxy.
- destruct (leb y x) eqn:Hyx; [ rewrite (asym Hxy Hyx) | ]; apply inT_eq.
- apply inT_cons, IHl.
Qed.

Lemma insert_neq_inclT B (x : @car B) l : inclT l (insert_neq x l).
Proof.
induction l as [| y l IHl]; [ apply inclT_nil_l | ].
cbn. destruct (leb x y) eqn:Hxy.
- intros z [ -> | Hz ].
  + destruct (leb z x) eqn:Hzx.
    * apply inT_eq.
    * apply inT_cons, inT_eq.
  + destruct (leb y x); apply inT_cons; [ | apply inT_cons ]; assumption.
- apply inclT_cons_cons, IHl.
Qed.

Lemma insert_neq_inclT_l B (x : @car B) l : inclT (insert_neq x l) (x :: l).
Proof.
induction l as [| y l IHl]; [ reflexivity | ].
cbn. destruct (leb x y) eqn:Hxy.
- destruct (leb y x) eqn:Hyx; [ apply inclT_tl | ]; reflexivity.
- intros z [ -> | [-> | Hz]%IHl ].
  + apply inT_cons, inT_eq.
  + apply inT_eq.
  + apply inT_cons, inT_cons, Hz.
Qed.

Lemma insert_neq_inclT_r B (x : @car B) l : inclT (x :: l) (insert_neq x l).
Proof.
induction l as [| y l IHl]; [ reflexivity | ].
cbn. destruct (leb x y) eqn:Hxy.
- destruct (leb y x) eqn:Hyx.
  + rewrite (asym Hxy Hyx).
    apply inclT_cons; [ apply inT_eq | reflexivity ].
  + reflexivity.
- intros z [ -> | [ -> | Hz ] ].
  + apply inT_cons, insert_neq_inT.
  + apply inT_eq.
  + apply inT_cons, insert_neq_inclT, Hz.
Qed.


(** ** Sorted lists *)

Fixpoint is_sorted B (l : list (@car B)) :=
  match l with
  | nil => true
  | a :: nil => true
  | a :: (b :: _) as r => leb a b && is_sorted B r
  end.
Arguments is_sorted {_} _.

Lemma is_sorted_tail B a l : @is_sorted B (a :: l) = true -> is_sorted l = true.
Proof. intro Hs. destruct l as [|b l]; [ reflexivity | apply andb_true_iff in Hs; apply Hs ]. Qed.

Lemma is_sorted_in B a b l : @is_sorted B (a :: l) = true -> In b l -> leb a b = true.
Proof.
induction l as [ | c l IH ]; [ intros _ [] | ]. intros Hs [ -> | Hin ].
- cbn in Hs. now destruct (leb a b).
- apply IH; [ | assumption ]. cbn in Hs.
  apply andb_true_iff in Hs as [Hac Hs].
  cbn. destruct l as [ | d l ]; [ reflexivity | ].
  apply andb_true_iff in Hs as [Hcd Hs].
  apply andb_true_iff. split.
  + apply (trans Hac Hcd).
  + assumption.
Qed.

Definition SortedList B := { m | @is_sorted B m = true }.

Lemma sortedlist_equality B (m1 m2 : SortedList B) : proj1_sig m1 = proj1_sig m2 -> m1 = m2.
Proof.
destruct m1 as [m1' B1], m2 as [m2' B2]. cbn. intros ->.
f_equal. apply (Eqdep_dec.UIP_dec bool_dec).
Qed.

Lemma insert_sorted B a (m : SortedList B) : let l := insert a (proj1_sig m) in
    is_sorted l = true /\ l <> nil
 /\ forall c, In c l -> In c (proj1_sig m) \/ c = a.
Proof.
enough (forall s a (m : SortedList B),
  length (proj1_sig m) = s ->
  let l := insert a (proj1_sig m) in
    is_sorted l = true /\ l <> nil
 /\ forall c, In c l -> In c (proj1_sig m) \/ c = a) as Hlen
  by now intros; apply Hlen with (length (proj1_sig m)).
intro s. induction s as [s IH] using (well_founded_induction lt_wf).
clear a m. intros a [[|b l'] Hsort] Hlen l; repeat split; auto.
- intros [=].
- intros c [ -> | [] ]. right. reflexivity.
- unfold l. clear l. cbn.
  destruct (leb a b) eqn:Heqbb.
  + now apply andb_true_iff; split.
  + destruct s as [|s]; destr_eq Hlen.
    destruct (IH s (le_n _) a (exist _ l' (is_sorted_tail _ _ _ Hsort)) Hlen)
      as [Hsort' _].
    apply total in Heqbb.
    destruct l' as [|c l']; [ (apply andb_true_iff; split); auto | ].
    cbn in Hsort', Hsort. cbn. destruct (leb a c); apply andb_true_iff; split; auto.
    apply andb_true_iff in Hsort. apply Hsort.
- intro Heq. unfold l in Heq. cbn in Heq.
  destruct (leb a b); discriminate Heq.
- intros d Hd. unfold l in Hd. cbn in Hd.
  destruct (leb a b).
  + destruct Hd as [ -> | ]; [ right | left ]; trivial.
  + destruct Hd as [ -> | Hin ].
    * left. apply in_eq.
    * destruct s as [|s]; destr_eq Hlen.
      destruct (IH s (le_n _) a (exist _ l' (is_sorted_tail _ _ _ Hsort)) Hlen) as [_ Hin'].
      apply Hin' in Hin as [|]; [ left; apply in_cons | right ]; assumption.
Qed.

Lemma insert_neq_sorted B a (m : SortedList B) : let l := insert_neq a (proj1_sig m) in
    is_sorted l = true /\ l <> nil
 /\ forall c, In c l -> In c (proj1_sig m) \/ c = a.
Proof.
enough (forall s a (m : SortedList B),
  length (proj1_sig m) = s ->
  let l := insert_neq a (proj1_sig m) in
    is_sorted l = true /\ l <> nil
 /\ forall c, In c l -> In c (proj1_sig m) \/ c = a) as Hlen
  by now intros; apply Hlen with (length (proj1_sig m)).
intro s. induction s as [s IH] using (well_founded_induction lt_wf).
clear a m. intros a [[|b l'] Hsort] Hlen l; repeat split; auto.
- intros [=].
- intros c [ -> | [] ]. right. reflexivity.
- unfold l. clear l. cbn.
  destruct (leb a b) eqn:Heqbb.
  + destruct (leb b a) eqn:Heqbb'; [ assumption | ].
    now apply andb_true_iff; split.
  + destruct s as [|s]; destr_eq Hlen.
    destruct (IH s (le_n _) a (exist _ l' (is_sorted_tail _ _ _ Hsort)) Hlen)
      as [Hsort' _].
    apply total in Heqbb.
    destruct l' as [|c l']; [ (apply andb_true_iff; split); auto | ].
    cbn in Hsort', Hsort. cbn. destruct (leb a c); [ | apply andb_true_iff; split; auto ].
    * destruct (leb c a); apply andb_true_iff; split; auto.
      apply andb_true_iff in Hsort. apply Hsort.
    * apply andb_true_iff in Hsort. apply Hsort.
- intro Heq. unfold l in Heq. cbn in Heq.
  destruct (leb a b), (leb b a); discriminate Heq.
- intros d Hd. unfold l in Hd. cbn in Hd.
  destruct (leb a b) eqn:Hab.
  + destruct (leb b a) eqn:Hba.
    * destruct Hd as [ -> | ]; [ right | left; right; assumption ].
      apply (asym Hba Hab).
    * destruct Hd as [ -> | ]; [ right | left ]; trivial.
  + destruct Hd as [ -> | Hin ].
    * left. apply in_eq.
    * destruct s as [|s]; destr_eq Hlen.
      destruct (IH s (le_n _) a (exist _ l' (is_sorted_tail _ _ _ Hsort)) Hlen) as [_ Hin'].
      apply Hin' in Hin as [|]; [ left; apply in_cons | right ]; assumption.
Qed.

Lemma is_sorted_sorted_neq B (l : list (@car B)) : is_sorted (fold_right insert_neq nil l) = true.
Proof. induction l as [ | x l IH ]; [ reflexivity | apply (insert_neq_sorted _ (exist _ _ IH)) ]. Qed.

Lemma NoDup_insert_neq B (x : @car B) l : is_sorted l = true -> NoDup l -> NoDup (insert_neq x l).
Proof.
induction l as [ | y l IHl ]; intros Hs Hnd; [ repeat constructor; intros [] | cbn ].
destruct (leb x y) eqn:Hxy.
- destruct (leb y x) eqn:Hyx.
  + assumption.
  + constructor; [ | assumption ].
    intros [-> | Hin].
    * rewrite Hxy in Hyx. discriminate Hyx.
    * apply (is_sorted_in _ _ _ _ Hs) in Hin.
      rewrite Hin in Hyx. discriminate Hyx.
- inversion_clear Hnd as [ | ? ? Hnin Hndl].
  constructor.
  + intro Hin. apply Hnin. apply insert_neq_incl_l in Hin as [ <- | Hin ]; [ exfalso | assumption ].
    rewrite (refl _ x) in Hxy. discriminate Hxy.
  + apply IHl.
    * apply (is_sorted_tail _ _ _ Hs).
    * assumption.
Qed.

Fixpoint nodup_sortedb B (l : list (@car B)) :=
match l with
| nil => true
| a :: nil => true
| a :: (b :: _) as r => negb (leb b a) && nodup_sortedb _ r
end.

Lemma nodup_sortedb_cons_cons B (a b : @car B) l :
  nodup_sortedb _ (a :: b :: l) = negb (leb b a) && nodup_sortedb _ (b :: l).
Proof. reflexivity. Qed.

Lemma nodup_sortedb_spec B (l : list (@car B)) : is_sorted l = true -> reflect (NoDup l) (nodup_sortedb _ l).
Proof.
induction l as [ | a [ | b l ] IH ]; intro Hs.
- apply ReflectT. constructor.
- apply ReflectT. repeat constructor. intros [].
- assert (Hs' := is_sorted_tail _ _ _ Hs).
  cbn in Hs. apply andb_true_iff in Hs as [Hab _].
  rewrite nodup_sortedb_cons_cons. destruct (IH Hs').
  + destruct (leb b a) eqn:Hba.
    * apply ReflectF. intro Hnd.
      rewrite (asym Hab Hba) in Hnd.
      inversion_clear Hnd as [ | ? ? Hin ]. apply Hin, in_eq.
    * apply ReflectT.
      constructor; [ | assumption ].
      intros [ -> | Hin ].
      -- rewrite Hba in Hab. discriminate Hab.
      -- apply (is_sorted_in _ _ _ _ Hs') in Hin.
         rewrite Hin in Hba. discriminate Hba.
  + rewrite andb_false_r. apply ReflectF. intro Hnd.
    inversion_clear Hnd. contradiction.
Qed.

Lemma nodup_sorted_neq B (l : list (@car B)) : nodup_sortedb _ (fold_right insert_neq nil l) = true.
Proof. induction l as [ | x l IH ]; [ reflexivity | ].
cbn.
assert (Hs := is_sorted_sorted_neq _ l).
remember (fold_right insert_neq nil l) as m eqn:Hm. clear Hm.
change m with (proj1_sig (exist (fun z => is_sorted z = true) _ Hs)).
destruct (nodup_sortedb_spec _ _ (proj1 (insert_neq_sorted x (exist _ _ Hs)))) as [ | Hd ]; [ reflexivity | ].
exfalso. apply Hd.
cbn in *.
apply NoDup_insert_neq; [ assumption | ].
destruct (nodup_sortedb_spec _ _ Hs); [ assumption | discriminate IH ].
Qed.


(** *** multiset ordering on (sorted) lists *)

Fixpoint leb_mset_rev A (leA : brelation A) l1 l2 :=
  match l1, l2 with
  | nil, _ => true
  | _ :: _, nil => false
  | a1 :: r1, a2 :: r2 => if leA a1 a2 then (if leA a2 a1 then leb_mset_rev leA r1 r2 else true)
                                       else false
  end.

Definition leb_mset (B : BOrder) (l1 l2 : list B) :=
  leb_mset_rev B.(leb) (rev l1) (rev l2).

#[export]
Instance border_list (B : BOrder) : BOrder.
Proof.
split with (list B) (leb_mset B); intros l1 l2; unfold leb_mset; cbn.
- intro Hle. induction l1 as [ | a1 r1 IH ] in Hle, l2 |- * using rev_ind; cbn in *.
  + discriminate Hle.
  + rewrite rev_unit in Hle. cbn in Hle.
    destruct (rev_case l2) as [ -> | [a2 [r2 ->]] ]; cbn in Hle; cbn.
    * reflexivity.
    * rewrite rev_unit in Hle. rewrite !rev_unit. cbn.
      case_eq (leb a1 a2); intros H1.
      -- case_eq (leb a2 a1); intros H2.
         ++ rewrite H1, H2 in Hle. apply IH. assumption.
         ++ rewrite H1, H2 in Hle. discriminate Hle.
      -- rewrite (total H1). reflexivity.
- intros Hle1 Hle2.
  induction l1 as [ | a1 r1 IH ] in Hle1, Hle2, l2 |- * using rev_ind;
    destruct (rev_case l2) as [ -> | [a2 [r2 ->]] ]; cbn in *.
  + reflexivity.
  + rewrite rev_unit in Hle2. discriminate Hle2.
  + rewrite rev_unit in Hle1. cbn in Hle1. discriminate Hle1.
  + rewrite !rev_unit in Hle1, Hle2. cbn in Hle1, Hle2.
    case_eq (leb a1 a2); intros H1; rewrite H1 in Hle1, Hle2.
    * case_eq (leb a2 a1); intros H2; rewrite H2 in Hle1, Hle2.
      -- rewrite (asym H1 H2).
         rewrite (IH r2) by assumption. reflexivity.
      -- discriminate Hle2.
    * discriminate Hle1.
- intros l Hle1 Hle2; cbn in *.
  induction l1 as [ | a1 r1 IH ] in Hle1, Hle2, l2, l |- * using rev_ind; [ reflexivity | cbn in * ].
  rewrite rev_unit. rewrite rev_unit in Hle1.
  destruct (rev_case l2) as [ -> | [a2 [r2 ->]] ].
  + discriminate Hle1.
  + rewrite rev_unit in Hle1, Hle2. cbn in Hle1.
    case_eq (leb a1 a2); intros H1; rewrite H1 in Hle1.
    * destruct (rev_case l) as [ -> | [a [r ->]] ]; [ discriminate Hle2 | ].
      case_eq (leb a2 a1); intros H2; rewrite H2 in Hle1;
         rewrite rev_unit in Hle2; cbn in Hle2; rewrite rev_unit; cbn.
      -- case_eq (leb a2 a); intros H3; rewrite H3 in Hle2.
         ++ case_eq (leb a a2); intros H4; rewrite H4 in Hle2.
            ** rewrite (trans H1 H3), (trans H4 H2).
               apply (IH _ _ Hle1 Hle2).
            ** rewrite (trans H1 H3).
               case_eq (leb a a1); intros H; [ | reflexivity ].
               exfalso. rewrite (trans H H1) in H4. discriminate H4.
         ++ discriminate Hle2.
      -- case_eq (leb a2 a); intros H3; rewrite H3 in Hle2.
         ++ case_eq (leb a a2); intros H4; rewrite H4 in Hle2.
            ** rewrite (asym H3 H4) in *. rewrite H1, H2. reflexivity.
            ** rewrite (trans H1 H3).
               case_eq (leb a a1); intros H; [ | reflexivity ].
               exfalso. rewrite (trans H3 H) in H2. discriminate H2.
         ++ discriminate Hle2.
   * discriminate Hle1.
Defined.

#[export]
Instance border_slist (B : BOrder) : BOrder.
Proof.
split with (SortedList B) (fun m1 m2 => leb_mset _ (proj1_sig m1) (proj1_sig m2)).
- intros m1 m2. apply (border_list B).(total).
- intros m1 m2 H1 H2. apply sortedlist_equality, (border_list B).(asym); assumption.
- intros m1 m2 m3. apply (border_list B).(trans).
Defined.
