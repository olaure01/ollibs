(* This file is directly inspired by the corresponding Rocq Stdlib file
   Sorting/Permutation.v *)

From Stdlib Require Import List PeanoNat Compare_dec CMorphisms FinFun Permutation.
From OLlibs Require Import ListT.
Import ListNotations. (* For notations [] and [a;b;c] *)

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.
(* Set Universe Polymorphism. *)


Section Permutation.

Variable A:Type.

Inductive PermutationT : crelation (list A) :=
| PermutationT_nil_nil : PermutationT [] []
| PermutationT_skip x l l' : PermutationT l l' -> PermutationT (x::l) (x::l')
| PermutationT_swap x y l : PermutationT (y::x::l) (x::y::l)
| PermutationT_trans l l' l'' :
    PermutationT l l' -> PermutationT l' l'' -> PermutationT l l''.

#[local] Hint Constructors PermutationT : core.

(** Some facts about [Permutation] *)

Theorem PermutationT_nil : forall (l : list A), PermutationT [] l -> l = [].
Proof.
  intros l HF.
  remember (@nil A) as m in HF.
  induction HF; discriminate || auto.
Qed.

Theorem PermutationT_nil_cons : forall (l : list A) (x : A), notT (PermutationT nil (x::l)).
Proof.
  intros l x HF.
  apply PermutationT_nil in HF; discriminate.
Qed.

(** Permutation over lists is a equivalence relation *)

Theorem PermutationT_refl : forall l : list A, PermutationT l l.
Proof.
  intro l. induction l as [|a l IHl]; constructor. exact IHl.
Qed.

Theorem PermutationT_sym : forall l l' : list A,
 PermutationT l l' -> PermutationT l' l.
Proof.
  intros l l' Hperm; induction Hperm as [ | | | ? l']; auto.
  apply PermutationT_trans with (l':=l'); assumption.
Qed.

End Permutation.

#[export] Hint Resolve PermutationT_refl PermutationT_nil_nil
                       PermutationT_skip : core.

(* These hints do not reduce the size of the problem to solve and they
   must be used with care to avoid combinatoric explosions *)

#[local] Hint Resolve PermutationT_swap PermutationT_trans : core.
#[local] Hint Resolve PermutationT_sym : core.

(* This provides reflexivity, symmetry and transitivity and rewriting
   on morphims to come *)

#[export] Instance PermutationT_Equivalence A : Equivalence (@PermutationT A) | 10 := {
  Equivalence_Reflexive := @PermutationT_refl A ;
  Equivalence_Symmetric := @PermutationT_sym A ;
  Equivalence_Transitive := @PermutationT_trans A }.

#[export] Instance PermutationT_cons A :
  Proper (Logic.eq ==> @PermutationT A ==> @PermutationT A) (@cons A) | 10.
Proof. repeat intro; subst; auto using PermutationT_skip. Qed.


Section Permutation_properties.

Variable A:Type.

Implicit Types a b : A.
Implicit Types l m : list A.

(** Compatibility with others operations on lists *)

Theorem PermutationT_in : forall (l l' : list A) (x : A),
  PermutationT l l' -> In x l -> In x l'.
Proof. intros l l' x Hperm; induction Hperm; simpl; tauto. Qed.

#[export] Instance PermutationT_in' :
  Proper (Logic.eq ==> @PermutationT A ==> iff) (@In A) | 10.
Proof. repeat red; intros; subst; eauto using PermutationT_in. Qed.

Theorem PermutationT_inT : forall (l l' : list A) (x : A),
 PermutationT l l' -> InT x l -> InT x l'.
Proof.
  intros l l' x Hperm; induction Hperm; simpl; tauto.
Qed.

#[export] Instance PermutationT_inT' :
  Proper (Logic.eq ==> @PermutationT A ==> arrow) (@InT A) | 10.
Proof.
  intros l1 l2 Heq l1' l2' HP Hi ; subst.
  eauto using PermutationT_inT.
Qed.

Lemma PermutationT_app_tail : forall (l l' tl : list A),
 PermutationT l l' -> PermutationT (l++tl) (l'++tl).
Proof.
  intros l l' tl Hperm; induction Hperm as [|x l l'|x y l|l l' l'']; simpl; auto.
  eapply PermutationT_trans with (l':=l'++tl); trivial.
Qed.

Lemma PermutationT_app_head : forall (l tl tl' : list A),
 PermutationT tl tl' -> PermutationT (l++tl) (l++tl').
Proof.
  intros l tl tl' Hperm; induction l;
   [trivial | repeat rewrite <- app_comm_cons; constructor; assumption].
Qed.

Theorem PermutationT_app : forall (l m l' m' : list A),
 PermutationT l l' -> PermutationT m m' -> PermutationT (l++m) (l'++m').
Proof.
  intros l m l' m' Hpermll' Hpermmm';
   induction Hpermll' as [|x l l'|x y l|l l' l''];
    repeat rewrite <- app_comm_cons; auto.
  - apply PermutationT_trans with (l' := (x :: y :: l ++ m));
     [idtac | repeat rewrite app_comm_cons; apply PermutationT_app_head]; trivial.
  - apply PermutationT_trans with (l' := (l' ++ m')); try assumption.
    apply PermutationT_app_tail; assumption.
Qed.

#[export] Instance PermutationT_app' :
 Proper (@PermutationT A ==> @PermutationT A ==> @PermutationT A) (@app A) | 10.
Proof. repeat intro; now apply PermutationT_app. Qed.

Lemma PermutationT_add_inside : forall a (l l' tl tl' : list A),
  PermutationT l l' -> PermutationT tl tl' ->
  PermutationT (l ++ a :: tl) (l' ++ a :: tl').
Proof. intros; apply PermutationT_app; auto. Qed.

Lemma PermutationT_cons_append : forall (l : list A) x,
  PermutationT (x :: l) (l ++ x :: nil).
Proof. intro l. induction l as [ | ? ? IHl ]; intros; auto. simpl.
eapply PermutationT_trans ; [ apply PermutationT_swap | apply PermutationT_skip ].
apply IHl. Qed.
#[local] Hint Resolve PermutationT_cons_append : core.

Theorem PermutationT_app_comm : forall (l l' : list A),
  PermutationT (l ++ l') (l' ++ l).
Proof.
  intro l. induction l as [|x l IHl]; simpl; intro l'.
  - rewrite app_nil_r; trivial.
  - eapply PermutationT_trans ; [ apply PermutationT_skip ; apply IHl | ].
    rewrite app_comm_cons.
    replace (l' ++ x :: l) with ((l' ++ x :: nil) ++ l)
      by (rewrite <- app_assoc ; reflexivity).
    apply PermutationT_app_tail. apply PermutationT_cons_append.
Qed.
#[local] Hint Resolve PermutationT_app_comm : core.

Theorem PermutationT_cons_app : forall (l l1 l2:list A) a,
  PermutationT l (l1 ++ l2) -> PermutationT (a :: l) (l1 ++ a :: l2).
Proof.
  intros l l1 l2 a H.
  eapply PermutationT_trans ; [ apply PermutationT_skip ; apply H | ].
  rewrite app_comm_cons.
  replace (l1 ++ a :: l2) with ((l1 ++ a :: nil) ++ l2)
    by (rewrite <- app_assoc ; reflexivity).
  apply PermutationT_app_tail. apply PermutationT_cons_append.
Qed.
#[local] Hint Resolve PermutationT_cons_app : core.

Lemma PermutationT_AddT a l l' : AddT a l l' -> PermutationT (a::l) l'.
Proof.
 induction 1; simpl; trivial.
 eapply PermutationT_trans ; [ apply PermutationT_swap | ].
 now apply PermutationT_skip.
Qed.

Theorem PermutationT_middle : forall (l1 l2:list A) a,
  PermutationT (a :: l1 ++ l2) (l1 ++ a :: l2).
Proof.
  auto.
Qed.
#[local] Hint Resolve PermutationT_middle : core.

Theorem PermutationT_rev : forall (l : list A), PermutationT l (rev l).
Proof.
  intro l. induction l as [| x l]; simpl; trivial.
  eapply PermutationT_trans ; [ apply PermutationT_cons_append | ].
  apply PermutationT_app_tail. assumption.
Qed.

#[export] Instance PermutationT_rev' :
  Proper (@PermutationT A ==> @PermutationT A) (@rev A) | 10.
Proof.
  intros l1 l2 HP.
  eapply PermutationT_trans ; [ | eapply PermutationT_trans ].
  - apply PermutationT_sym.
    apply PermutationT_rev.
  - eassumption.
  - apply PermutationT_rev.
Qed.

Theorem PermutationT_length : forall (l l' : list A),
 PermutationT l l' -> length l = length l'.
Proof.
  intros l l' Hperm; induction Hperm as [ | | | ? l' ]; simpl; auto. now transitivity (length l').
Qed.

#[export] Instance PermutationT_length' :
  Proper (@PermutationT A ==> Logic.eq) (@length A) | 10.
Proof. exact PermutationT_length. Qed.

Theorem PermutationT_ind_bis :
 forall P : list A -> list A -> Prop,
   P [] [] ->
   (forall x l l', PermutationT l l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l l', PermutationT l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', PermutationT l l' -> P l l' -> PermutationT l' l'' -> P l' l'' -> P l l'') ->
   forall l l', PermutationT l l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans.
  induction 1 as [| | x y l | ]; auto.
  - apply Htrans with (x::y::l); auto.
    + apply Hswap; auto.
      induction l; auto.
    + apply Hskip; auto.
      apply Hskip; auto.
      induction l; auto.
  - eauto.
Qed.

Theorem PermutationT_rect_bis :
 forall P : crelation (list A),
   P [] [] ->
   (forall x l l', PermutationT l l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l l', PermutationT l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', PermutationT l l' -> P l l' -> PermutationT l' l'' -> P l' l'' -> P l l'') ->
   forall l l', PermutationT l l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans.
  induction 1 as [ | | x y l | ]; auto.
  - apply Htrans with (x::y::l); auto.
    + apply Hswap; auto.
      induction l; auto.
    + apply Hskip; auto.
      apply Hskip; auto.
      induction l; auto.
  - eauto.
Qed.

Theorem PermutationT_nil_app_cons : forall (l l' : list A) (x : A),
 notT (PermutationT nil (l++x::l')).
Proof.
  intros l l' x HF.
  apply PermutationT_nil in HF. destruct l; discriminate.
Qed.

Ltac InvAddT := repeat (match goal with
 | H: AddT ?x _ (_ :: _) |- _ => inversion H; clear H; subst
 end).

Ltac finish_basic_permsT H :=
  try constructor; try rewrite PermutationT_swap; try constructor; trivial;
  (rewrite <- H; now apply PermutationT_AddT) ||
  (rewrite H; symmetry; now apply PermutationT_AddT).

Theorem PermutationT_AddT_inv a l1 l2 :
  PermutationT l1 l2 -> forall l1' l2', AddT a l1' l1 -> AddT a l2' l2 ->
   PermutationT l1' l2'.
Proof.
 revert l1 l2. refine (PermutationT_rect_bis _ _ _ _ _).
 - (* nil *)
   inversion_clear 1.
 - (* skip *)
   intros x l1 l2 PE IH. intros. InvAddT; try finish_basic_permsT PE.
   constructor. now apply IH.
 - (* swap *)
   intros x y l1 l2 PE IH. intros. InvAddT; try finish_basic_permsT PE.
   eapply PermutationT_trans ; [ apply PermutationT_swap | ].
   do 2 constructor. now apply IH.
 - (* trans *)
   intros l1 l l2 PE IH PE' IH' l1' l2' AD1 AD2.
   assert {l' : list A & AddT a l' l } as [l' AD].
   { clear IH PE' IH' AD2 l2 l2'. revert l1' AD1.
     induction PE as [ | b l l' HP IHPE | b c l | l l' l'' HP1 IHPE1 HP2 IHPE2 ]; intros l1 AD1.
     - inversion AD1.
     - inversion AD1 as [|? ? ? AD2]; subst.
       + apply (existT _ l'). constructor.
       + apply IHPE in AD2 as [l'0 AD2].
         apply (existT _ (b :: l'0)).
         constructor. assumption.
     - inversion AD1 as [|? ? ? AD2]; subst.
       + apply (existT _ (b :: l)). do 2 constructor.
       + inversion AD2 as [|? l']; subst.
         * apply (existT _ (c :: l)). do 2 constructor.
         * apply (existT _ (b :: c :: l')). do 2 constructor. assumption.
     - apply IHPE1 in AD1 as [l'0 AD1]. apply IHPE2 in AD1. assumption. }
   eapply PermutationT_trans.
   + apply IH.
     * apply AD1.
     * apply AD.
   + now apply IH'.
Qed.

Theorem PermutationT_app_inv (l1 l2 l3 l4:list A) a :
  PermutationT (l1++a::l2) (l3++a::l4) -> PermutationT (l1++l2) (l3 ++ l4).
Proof.
 intros. eapply PermutationT_AddT_inv; eauto using AddT_app.
Qed.

Theorem PermutationT_cons_inv l l' a :
 PermutationT (a::l) (a::l') -> PermutationT l l'.
Proof.
  intro. eapply PermutationT_AddT_inv; eauto using AddT_head.
Qed.

Theorem PermutationT_cons_app_inv l l1 l2 a :
 PermutationT (a :: l) (l1 ++ a :: l2) -> PermutationT l (l1 ++ l2).
Proof.
  intro. eapply PermutationT_AddT_inv; eauto using AddT_head, AddT_app.
Qed.

Theorem PermutationT_app_inv_l : forall l l1 l2,
 PermutationT (l ++ l1) (l ++ l2) -> PermutationT l1 l2.
Proof.
  intro l. induction l as [|a ? IHl]; simpl; auto.
  intros.
  apply IHl.
  apply PermutationT_cons_inv with a; auto.
Qed.

Theorem PermutationT_app_inv_r l l1 l2 :
 PermutationT (l1 ++ l) (l2 ++ l) -> PermutationT l1 l2.
Proof.
 intros HP.
 eapply PermutationT_trans in HP ; [ | apply PermutationT_app_comm ].
 eapply PermutationT_app_inv_l.
 eapply PermutationT_trans ; [ apply HP | ].
 apply PermutationT_app_comm.
Qed.

Lemma PermutationT_length_1_inv: forall a l, PermutationT [a] l -> l = [a].
Proof.
  intros a l H; remember [a] as m eqn:Heqm in H.
  induction H as [ | ? ? ? H | | ]; try (injection Heqm as -> ->);
    discriminate || auto.
  apply PermutationT_nil in H as ->; trivial.
Qed.

Lemma PermutationT_length_1: forall a b, PermutationT [a] [b] -> a = b.
Proof.
  intros a b H.
  apply PermutationT_length_1_inv in H; injection H as ->; trivial.
Qed.

Lemma PermutationT_length_2_inv :
  forall a1 a2 l, PermutationT [a1;a2] l -> { l = [a1;a2] } + { l = [a2;a1] }.
Proof.
  intros a1 a2 l H; remember [a1;a2] as m eqn:Heqm in H.
  induction H as [ | ? ? ? H | | ? ? ? ? IHP1 ? IHP2 ] in a1, a2, Heqm |- *; try (injection Heqm as ? ?; subst);
    discriminate || (try tauto).
  - apply PermutationT_length_1_inv in H as ->; left; auto.
  - apply IHP1 in Heqm. destruct Heqm as [H1|H1]; apply IHP2 in H1; destruct H1 as [];
      auto.
Qed.

Lemma PermutationT_length_2 :
  forall a1 a2 b1 b2, PermutationT [a1;a2] [b1;b2] ->
    { a1 = b1 /\ a2 = b2 } + { a1 = b2 /\ a2 = b1 }.
Proof.
  intros a1 b1 a2 b2 H.
  apply PermutationT_length_2_inv in H as [H|H]; injection H as -> ->; auto.
Qed.

Lemma NoDupT_PermutationT l l' : NoDupT l -> NoDupT l' ->
  (forall x:A, iffT (InT x l) (InT x l')) -> PermutationT l l'.
Proof.
 intros N. revert l'. induction N as [|a l Hal Hl IH].
 - intro l'. destruct l' as [|a ]; simpl; auto.
   intros Hl' H. exfalso. apply (H a); auto.
 - intros l' Hl' H.
   assert (Ha : InT a l') by (apply H; simpl; auto).
   destruct (AddT_inv _ _ Ha) as [l'' AD].
   etransitivity; [ | apply (PermutationT_AddT AD) ].
   apply PermutationT_skip.
   apply IH; clear IH.
   * apply NoDup_NoDupT.
     apply NoDupT_NoDup in Hl'.
     apply AddT_Add in AD.
     now apply (NoDup_Add AD).
   * intro x. split.
     + apply inclT_AddT_inv with a l'; trivial. intro. apply H.
     + intro Hx.
       assert (Hx' : InT x (a::l)).
       { apply H. apply (AddT_inT_inv AD). now right. }
       destruct Hx'; simpl; trivial. subst.
       apply inT_in in Hx.
       apply AddT_Add in AD.
       apply NoDupT_NoDup in Hl'.
       rewrite (NoDup_Add AD) in Hl'. tauto.
Qed.

Lemma NoDupT_PermutationT_bis l l' : NoDupT l ->
  length l' <= length l -> inclT l l' -> PermutationT l l'.
Proof.
 intros Hnd Hlen Hinc. apply NoDupT_PermutationT; auto.
 - apply NoDupT_NoDup in Hnd; apply NoDup_NoDupT.
   apply inclT_incl in Hinc.
   now apply NoDup_incl_NoDup with l.
 - split; auto.
   apply NoDupT_length_inclT; trivial.
Qed.

Lemma PermutationT_NoDupT l l' : PermutationT l l' -> NoDupT l -> NoDupT l'.
Proof.
 induction 1 as [ | ? l | | ]; auto.
 - inversion_clear 1; constructor; [ intros Hin%(@PermutationT_inT _ l) | ]; auto.
 - inversion_clear 1 as [|? ? Hni Hnd]. inversion_clear Hnd; simpl in *.
   constructor.
   + intros [|]; auto.
   + constructor; [ | assumption ]. intro Hin. apply Hni. right. assumption.
Qed.

#[export] Instance PermutationT_NoDupT' :
 Proper (@PermutationT A ==> iffT) (@NoDupT A) | 10.
Proof. repeat red; eauto using PermutationT_NoDupT. Qed.

End Permutation_properties.

Section Permutation_map.

Variable A B : Type.
Variable f : A -> B.

Lemma PermutationT_map l l' :
  PermutationT l l' -> PermutationT (map f l) (map f l').
Proof.
 induction 1; simpl; eauto.
Qed.

#[export] Instance PermutationT_map' :
  Proper (@PermutationT A ==> @PermutationT B) (map f) | 10.
Proof. exact PermutationT_map. Qed.

End Permutation_map.

(*
Lemma nat_bijection_Permutation n f :
 bFun n f ->
 Injective f ->
 let l := seq 0 n in Permutation (map f l) l.
Proof.
 intros Hf BD.
 apply NoDup_Permutation_bis; auto using Injective_map_NoDup, seq_NoDup.
 * now rewrite length_map.
 * intros x. rewrite in_map_iff. intros (y & <- & Hy').
   rewrite in_seq in *. simpl in *.
   destruct Hy' as (_,Hy'). split; [ apply Nat.le_0_l | ]. apply Hf, Hy'.
Qed.
*)

Section PermutationT_alt.
Variable A:Type.
Implicit Type a : A.
Implicit Type l : list A.

(** Alternative characterization of permutation
    via [nth_error] and [nth] *)

Let adapt f n :=
 let m := f (S n) in if le_lt_dec m (f 0) then m else pred m.

#[local] Definition adapt_injective f : Injective f -> Injective (adapt f).
Proof.
 unfold adapt. intros Hf x y EQ.
 destruct le_lt_dec as [LE|LT]; destruct le_lt_dec as [LE'|LT'].
 - now apply eq_add_S, Hf.
 - apply PeanoNat.Nat.lt_eq_cases in LE.
   destruct LE as [LT|EQ']; [|now apply Hf in EQ'].
   unfold lt in LT. rewrite EQ in LT.
   rewrite (PeanoNat.Nat.lt_succ_pred _ _ LT') in LT.
   elim (proj1 (PeanoNat.Nat.lt_nge _ _) LT' LT).
 - apply PeanoNat.Nat.lt_eq_cases in LE'.
   destruct LE' as [LT'|EQ']; [|now apply Hf in EQ'].
   unfold lt in LT'. rewrite <- EQ in LT'.
   rewrite (PeanoNat.Nat.lt_succ_pred _ _ LT) in LT'.
   elim (proj1 (PeanoNat.Nat.lt_nge _ _) LT LT').
 - apply eq_add_S, Hf.
   now rewrite <- (PeanoNat.Nat.lt_succ_pred _ _ LT), <- (PeanoNat.Nat.lt_succ_pred _ _ LT'), EQ.
Defined.

#[local] Definition adapt_ok a l1 l2 f : Injective f -> length l1 = f 0 ->
 forall n, nth_error (l1++a::l2) (f (S n)) = nth_error (l1++l2) (adapt f n).
Proof.
 unfold adapt. intros Hf E n.
 destruct le_lt_dec as [LE|LT].
 - apply PeanoNat.Nat.lt_eq_cases in LE.
   destruct LE as [LT|EQ]; [|now apply Hf in EQ].
   rewrite <- E in LT.
   rewrite 2 nth_error_app1; auto.
 - rewrite <- (PeanoNat.Nat.lt_succ_pred _ _ LT) at 1.
   rewrite <- E, <- (PeanoNat.Nat.lt_succ_pred _ _ LT) in LT.
   rewrite 2 nth_error_app2.
   + rewrite Nat.sub_succ_l; [ reflexivity | ].
     apply Nat.lt_succ_r; assumption.
   + apply Nat.lt_succ_r; assumption.
   + apply Nat.lt_le_incl; assumption.
Defined.

Lemma PermutationT_nth_error l l' :
 PermutationT l l' ->
  (length l = length l') *
  { f | Injective f & forall n, nth_error l' n = nth_error l (f n) }.
Proof.
  intros P.
  split; [now apply PermutationT_length|].
  induction P as [ | ? ? ? ? IHP | | ? ? ? ? IHP1 ? IHP2 ].
  - exists (fun n => n); try red; auto.
  - destruct IHP as [f Hf Hf'].
    exists (fun n => match n with O => O | S n => S (f n) end); try red.
    + intros [|y] [|z]; simpl; now auto.
    + intros [|n]; simpl; auto.
  - exists (fun n => match n with 0 => 1 | 1 => 0 | n => n end); try red.
    + intros [|[|z]] [|[|t]]; simpl; now auto.
    + intros [|[|n]]; simpl; auto.
  - destruct IHP1 as [f Hf Hf'].
    destruct IHP2 as [g Hg Hg'].
    exists (fun n => f (g n)); try red.
    + auto.
    + intros n. rewrite <- Hf'; auto.
Qed.

Lemma nth_error_PermutationT l l' :
  length l = length l' ->
  forall f, Injective f -> (forall n, nth_error l' n = nth_error l (f n)) ->
  PermutationT l l'.
Proof.
  revert l. induction l' as [|a l' IHl'].
  - intros [|l]; now auto.
  - intros l E f Hf Hf'.
    simpl in E.
    assert (Ha : nth_error l (f 0) = Some a)
     by (symmetry; apply (Hf' 0)).
    destruct (nth_error_splitT l (f 0) Ha) as [(l1, l2) L12 L1].
    rewrite L12. symmetry; apply PermutationT_cons_app; symmetry.
    apply IHl' with (adapt f).
    + revert E. rewrite L12, !length_app. simpl.
      rewrite <- plus_n_Sm. now injection 1.
    + now apply adapt_injective.
    + intro n. rewrite <- (adapt_ok a), <- L12; auto.
      apply (Hf' (S n)).
Qed.

Lemma PermutationT_nth_error_bis l l' :
 PermutationT l l' ->
  { f:nat->nat | Injective f /\ bFun (length l) f
               & forall n, nth_error l' n = nth_error l (f n) }.
Proof.
  intros HP; apply PermutationT_nth_error in HP as [E [f Hf Hf']].
  exists f; [ split | ]; trivial.
  intros n Hn.
  destruct (PeanoNat.Nat.le_gt_cases (length l) (f n)) as [LE|LT]; trivial.
  rewrite <- nth_error_None, <- Hf', nth_error_None, <- E in LE.
  elim (proj1 (PeanoNat.Nat.lt_nge _ _) Hn LE).
Qed.

Lemma nth_error_PermutationT_bis l l' :
  forall f, Injective f -> bFun (length l) f ->
    (forall n, nth_error l' n = nth_error l (f n)) ->
  PermutationT l l'.
Proof.
  intros f Hf Hf2 Hf3; apply nth_error_PermutationT with f; auto.
  assert (H : length l' <= length l') by reflexivity.
  rewrite <- nth_error_None, Hf3, nth_error_None in H.
  destruct (PeanoNat.Nat.le_gt_cases (length l) (length l')) as [LE|LT];
   [|apply Hf2 in LT; elim (proj1 (PeanoNat.Nat.lt_nge _ _) LT H)].
  apply (proj1 (PeanoNat.Nat.lt_eq_cases _ _)) in LE. destruct LE as [LT|EQ]; trivial.
  rewrite <- nth_error_Some, Hf3, nth_error_Some in LT.
  assert (Hf' : bInjective (length l) f).
  { intros x y _ _ E. now apply Hf. }
  rewrite (bInjective_bSurjective Hf2) in Hf'.
  destruct (Hf' _ LT) as (y & Hy & Hy').
  apply Hf in Hy'. subst y. elim (PeanoNat.Nat.lt_irrefl _ Hy).
Qed.

Lemma PermutationT_nth l l' d :
 PermutationT l l' ->
  (let n := length l in
   (length l' = n) *
   { f:nat->nat | bFun n f /\ bInjective n f
                & forall x, x < n -> nth x l' d = nth (f x) l d }).
Proof.
 intros H.
 assert (E := PermutationT_length H).
 split; auto.
 apply PermutationT_nth_error_bis in H.
 destruct H as [f [Hf Hf2] Hf3].
 exists f; [ split | ]; auto.
 - intros x y _ _ Hxy. now apply Hf.
 - intros n Hn. rewrite <- 2 nth_default_eq. unfold nth_default.
   now rewrite Hf3.
Qed.

Lemma nth_PermutationT l l' d :
  let n := length l in
   length l' = n ->
   forall f, bFun n f -> bInjective n f ->
    (forall x, x < n -> nth x l' d = nth (f x) l d) ->
 PermutationT l l'.
Proof.
 intros nl E f Hf1 Hf2 Hf3.
 refine (@nth_error_PermutationT _ _ _ (fun n => if le_lt_dec (length l) n then n else f n) _ _).
 - fold nl. symmetry. assumption.
 - intros x y.
   destruct le_lt_dec as [LE|LT];
    destruct le_lt_dec as [LE'|LT']; auto.
   + apply Hf1 in LT'. intros ->.
     elim (PeanoNat.Nat.lt_irrefl (f y)). eapply PeanoNat.Nat.lt_le_trans; eauto.
   + apply Hf1 in LT. intros <-.
     elim (PeanoNat.Nat.lt_irrefl (f x)). eapply PeanoNat.Nat.lt_le_trans; eauto.
 - intros n.
   destruct le_lt_dec as [LE|LT].
   + assert (LE' : length l' <= n) by (now rewrite E).
     rewrite <- nth_error_None in LE, LE'. congruence.
   + assert (LT' : n < length l') by (now rewrite E).
     specialize (Hf3 n LT). rewrite <- 2 nth_default_eq in Hf3.
     unfold nth_default in Hf3.
     apply Hf1 in LT.
     subst nl.
     rewrite <- nth_error_Some in LT, LT'.
     do 2 destruct nth_error; congruence.
Qed.

End PermutationT_alt.

(* begin hide *)
Notation PermutationT_app_swap := PermutationT_app_comm (only parsing).
(* end hide *)


Lemma PermutationT_Permutation A : forall l1 l2 : list A,
  PermutationT l1 l2 -> Permutation.Permutation l1 l2.
Proof.
intros l1 l2 HP.
induction HP ; try constructor ; try assumption.
etransitivity ; eassumption.
Qed.
