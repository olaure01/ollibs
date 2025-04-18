(** Infinite Types *)

From Stdlib Require Import Bool PeanoNat Lia List.
From OLlibs Require Import funtheory ListT.
From OLlibs Require Export inhabitedT dectype.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


(** a pigeonhole principle *)
Definition pigeon X := forall (l1 l2 : list X),
  NoDup l1 -> length l2 < length l1 -> { x | In x l1 & ~ In x l2 }.


(** * Definitions and implications *)

(* The following results are proved in the case of a DecType:
     bijection with nat => section with nat => bijection with one more element
       => non-surjective self injection => injection from nat <=> choice out of finite subsets
*)


(* we start with results true for an arbitrary Type:
     bijection with nat => section with nat => choice out of finite subsets => injection from nat
     bijection with nat => bijection with one more element => non-surjective self injection
*)
Section Infinite.

  Variable X : Type.

  (* bijection with nat *)
  Definition nat_bijective := { f : nat -> X & bijective f }.
  (* section with nat *)
  Definition nat_section := {'(i, s) : (nat -> X) * (X -> nat) | retract s i }.
  (* non-surjective self injection *)
  Definition self_injective := { f : X -> X & injective f & { x | forall y, x <> f y } }.
  (* bijection with extension with one more element *)
  Definition self_option_bijective := { f : option X -> X & bijective f }.
  (* injection from nat *)
  Definition nat_injective := { f : nat -> X | injective f }.
  (* choice out of finite subsets *)
  Definition choice_out_finite := { f : list X -> X | forall l, ~ In (f l) l }.

  Lemma nat_bijective_section : nat_bijective -> nat_section.
  Proof.
  intros [i Hbij].
  destruct (bijective_inverse Hbij) as [s _ Hsec].
  exists (i, s). exact Hsec.
  Qed.

  Lemma section_choice : nat_section -> choice_out_finite.
  Proof.
  intros [(i,s) Hsec].
  remember (fix h l :=
    match l with
    | nil => i 0
    | x :: tl => i (S (max (s x) (s (h tl))))
    end) as c eqn:Heqc.
  exists c.
  enough (forall l, Forall (fun x => s x < s (c l)) l) as Hlt.
  { intros l Hin. specialize Hlt with l.
    apply (proj1 (Forall_forall _ _) Hlt (c l)) in Hin. lia. }
  intro l. induction l as [|a l IHl]; cbn; constructor.
  - rewrite Heqc, Hsec. lia.
  - apply Forall_forall. intros b Hb. apply Forall_forall with (x:= b) in IHl; [ | assumption ].
    subst c. rewrite Hsec. lia.
  Qed.

  Lemma choice_nat_injective : choice_out_finite -> nat_injective.
  Proof.
  intros [c Hc].
  remember (fix h n := (* a non-empty list of iterated choices *)
    match n with
    | 0 => c nil :: nil
    | S k => c (h k) :: h k
    end) as ih.
  exists (fun n => hd (c nil) (ih n)).
  assert(forall n x, In (hd (c nil) (ih x)) (ih (n + x))) as HC.
  { intros n x. induction n as [|n IHn]; cbn; subst.
    - destruct x; apply in_eq.
    - right. exact IHn. }
  enough (forall x y, x < y -> hd (c nil) (ih x) = hd (c nil) (ih y) -> x = y) as Hlt.
  { intros x y Heq.
    case (Nat.compare_spec x y); intros Ho; [ exact Ho | | ].
    - apply Hlt, Heq. exact Ho.
    - symmetry. apply Hlt; [ | symmetry ]; assumption. }
  intros x y Hlt Heq. exfalso.
  specialize HC with (y - S x) x.
  replace (y - S x + x) with (pred y) in HC by lia.
  rewrite Heq in HC.
  replace y with (S (pred y)) in HC at 1 by lia.
  apply (Hc (ih (pred y))). subst ih. assumption.
  Qed.

  Lemma nat_bijective_self_option : nat_bijective -> self_option_bijective.
  Proof.
  intros [i Hbij].
  destruct (bijective_inverse Hbij) as [s Hsec1 Hsec2].
  exists (fun o => match o with
                   | Some x => i (S (s x))
                   | None => i 0
                   end).
  intro y. remember (s y) as n eqn:Hn. destruct n as [|n].
  - exists None.
    + rewrite Hn, Hsec1. reflexivity.
    + intros [x|] ->.
      * exfalso. rewrite Hsec2 in Hn. discriminate Hn.
      * reflexivity.
  - exists (Some (i (pred (S n)))).
    + rewrite Hsec2, Nat.pred_succ, Hn, Hsec1. reflexivity.
    + intros [x|] ->.
      * rewrite Hsec2 in Hn. injection Hn as [= ->].
        rewrite Nat.pred_succ, Hsec1. reflexivity.
      * exfalso. rewrite Hsec2 in Hn. discriminate Hn.
  Qed.

  Lemma option_bijective_self : self_option_bijective -> self_injective.
  Proof.
  intros [f Hinj%bijective_injective].
  exists (fun x => f (Some x)).
  - apply compose_injective; [ intros x y [=] | ]; assumption.
  - exists (f None).
    intros x [=]%Hinj.
  Qed.

End Infinite.

(** [DecType] case *)

(* Implications requiring a DecType
     section with nat => bijection with one more element
     non-surjective self injection => injection from nat => choice out of finite subset
*)
Section InfiniteDec.

  Variable X : DecType.

  Lemma section_self_bijective : nat_section X -> self_option_bijective X.
  Proof.
  intros [(i, s) Hs].
  assert (Hinj := section_injective Hs).
  assert (forall x z, x = i z -> x = i (s x)) as Hsi
    by (now intros x z Heq; rewrite Heq at 2; rewrite Hs).
  exists (fun o => match o with
                   | Some x => if eqb x (i (s x)) then i (S (s x)) else x
                   | None => i 0
                   end).
  intro y. remember (eqb y (i (s y))) as b eqn:Hb. symmetry in Hb. destruct b.
  - apply eqb_eq in Hb.
    remember (s y) as n eqn:Hn. rewrite Hn in Hb. destruct n as [|n].
    + exists None.
      * rewrite Hn. assumption.
      * intros [x|] Hy.
        -- exfalso. remember (eqb x (i (s x))) as b' eqn:Hb'. destruct b'.
           ++ rewrite Hy, Hs in Hn. discriminate Hn.
           ++ symmetry in Hb'. apply eqb_neq in Hb'. apply Hb'. subst y. assumption.
        -- reflexivity.
    + exists (Some (i (pred (S n)))).
      * rewrite Nat.pred_succ, ! Hs, eqb_refl, Hn. assumption.
      * intros [x|] Hy.
        -- remember (eqb x (i (s x))) as b' eqn:Hb'. destruct b'.
           ++ rewrite Hy, Hs in Hn. injection Hn as [= ->].
              symmetry in Hb'. apply eqb_eq in Hb'. rewrite Nat.pred_succ, <- Hb'. reflexivity.
           ++ exfalso. symmetry in Hb'. apply eqb_neq in Hb'. apply Hb'. subst y. assumption.
        -- exfalso. rewrite Hy, Hs in Hn. discriminate Hn.
  - exists (Some y).
    + rewrite Hb. reflexivity.
    + apply eqb_neq in Hb. intros [x|] Hy.
      * remember (eqb x (i (s x))) as b' eqn:Hb'. destruct b'.
        -- exfalso. apply Hb, (Hsi _ (S (s x))), Hy.
        -- rewrite Hy. reflexivity.
      * exfalso. apply Hb, (Hsi _ 0), Hy.
  Qed.

  Lemma pigeon_dectype : pigeon X.
  Proof.
  intro l1. induction l1 as [|a l1 IHl1]; cbn; intros l2 Hnd Hl; [ exfalso; lia | ].
  destruct (in_dec eq_dt_dec a l2) as [Hin|].
  - apply NoDup_NoDupT in Hnd.
    inversion_clear Hnd as [ | ? ? Hnin%notT_inT_not_in Hnd2%NoDupT_NoDup ].
    apply IHl1 with (remove eq_dt_dec a l2) in Hnd2 as [b Hb Hnb].
    + exists b.
      * right. assumption.
      * intro Hin'. apply Hnb.
        apply in_in_remove; [ | assumption ].
        intros ->. exact (Hnin Hb).
    + apply remove_length_lt with (eq_dec:= eq_dt_dec) in Hin. lia.
  - now exists a; [ left | ].
  Qed.

  Lemma injective_enum (f : nat -> X) : injective f -> forall l, { n | ~ In (f n) l }.
  Proof.
  intros Hinj l.
  destruct pigeon_dectype with (map f (seq 0 (S (length l)))) l as [x Hin Hnin].
  - apply injective_NoDup, seq_NoDup. assumption.
  - rewrite length_map, length_seq. lia.
  - remember (S (length l)) as k eqn:Heqk. clear Heqk.
    remember 0 as s eqn:Heqs. clear Heqs.
    induction k as [|k IHk] in s, Hin, Hnin |-*; cbn; [ easy | ].
    case (eq_dt_reflect (f s) x); [ intros <- | intro Hneq ].
    + exists s. assumption.
    + apply IHk with (S s); [ | assumption ].
      now destruct Hin.
  Qed.

  Lemma nat_injective_choice : nat_injective X -> choice_out_finite X.
  Proof.
  intros [i Hi].
  exists (fun l => i (proj1_sig (injective_enum Hi l))).
  intros l Hin. destruct (injective_enum Hi l) as [n Hnin]. exact (Hnin Hin).
  Qed.

  Lemma self_injective_minus (pi : self_injective X) :
    self_injective (minus (proj1_sig (projT3 pi))).
  Proof.
  destruct pi as [f Hinj [i Hi]]. cbn.
  assert (forall x, eqb i x = false -> eqb i (f x) = false) as Hif
    by (intros x _; apply eqb_neq, Hi).
  split with (fun a => exist _ (f (proj1_sig a)) (Hif (proj1_sig a) (proj2_sig a))).
  - intros [x Hx] [y Hy] Heq.
    inversion Heq as [Heq2].
    apply Hinj in Heq2 as ->.
    rewrite ((Eqdep_dec.UIP_dec bool_dec) _ _ Hx Hy). reflexivity.
  - assert (eqb i (f i) = false) as Hj by apply eqb_neq, Hi.
    split with (exist _ (f i) Hj).
    intros [y Hy]. cbn. intro Heq.
    inversion Heq as [Heq2].
    apply Hinj, eqb_neq in Heq2; assumption.
  Qed.

End InfiniteDec.

Arguments self_injective_minus {_} _.

Definition nat_of_self (X : DecType) (pi : self_injective X) n :
   { x | x = Nat.iter n (projT1 (sigT_of_sigT2 pi)) (proj1_sig (projT3 pi)) }
 * { Y : DecType & self_injective Y }.
Proof.
remember pi as HX. destruct pi as [f Hinj [i Hi]].
induction n as [|n IHn].
- split.
  + exists i. subst HX. reflexivity.
  + exists (minus (proj1_sig (projT3 HX))).
    apply (self_injective_minus HX).
- destruct IHn as [[y Hy] [Y HY]]. split.
  + exists (f y). subst y HX. reflexivity.
  + exists (minus (proj1_sig (projT3 HY))).
    apply (self_injective_minus HY).
Defined.

Lemma self_injective_nat (X : DecType) : self_injective X -> nat_injective X.
Proof.
intros HX.
exists (fun n => proj1_sig (fst (nat_of_self X HX n))).
intros x y Heq.
destruct (fst (nat_of_self X HX x)) as [n ->].
destruct (fst (nat_of_self X HX y)) as [m ->]. cbn in Heq.
destruct HX as [f Hinj [i Hi]]. cbn in Heq.
enough (forall x y, x < y -> Nat.iter x f i = Nat.iter y f i -> x = y) as Hlt.
{ case (Nat.compare_spec x y); intros Ho; [ exact Ho | | ].
  - apply Hlt; assumption.
  - symmetry. symmetry in Heq. apply Hlt; assumption. }
clear - Hinj Hi. intros x y Hlt Heq. exfalso.
remember (pred (y - x)) as n eqn:Heqn.
replace y with (S n + x) in Heq by lia. clear Heqn.
induction x as [|x IHx] in Hlt, Heq |- *.
- apply Hi in Heq as [].
- replace (S n + x) with (n + S x) in IHx by lia.
  apply IHx, Hinj; [ lia | assumption ].
Qed.


(** * Infinite Decidable Types
  (infinite) decidable types with freshness function *)

Record InfDecType := {
  infcar :> DecType;
  fresh : list infcar -> infcar;
  fresh_spec : forall l, ~ In (fresh l) l }.
Arguments fresh {_}.
Arguments fresh_spec {_}.

Section InfDecTypes.

  Variable X : InfDecType.

  Lemma infinite_nat_injective : nat_injective X.
  Proof. apply choice_nat_injective. exists fresh. apply fresh_spec. Qed.

  (* A list (of length [n]+1) of distinct fresh elements (not in [l]) *)
  Fixpoint freshlist_of_list (l : list X) n :=
    match n with
    | 0 => fresh l :: nil
    | S k => let lv := freshlist_of_list l k in fresh (lv ++ l) :: lv
    end.

  Definition freshlist l n := hd (fresh l) (freshlist_of_list l n).

  Lemma freshlist_of_list_fresh l n x : In x (freshlist_of_list l n) -> ~ In x l.
  Proof.
  induction n as [|n IHn]; cbn; intros [Hin1 | Hin2] Hinl; subst.
  - exact (fresh_spec _ Hinl).
  - assumption.
  - apply fresh_spec with (freshlist_of_list l n ++ l).
    apply in_or_app. right. assumption.
  - exact (IHn Hin2 Hinl).
  Qed.

  Lemma freshlist_of_list_prefix l n m : n < m -> exists l',
    l' <> nil /\ freshlist_of_list l m = l' ++ freshlist_of_list l n.
  Proof.
  induction m as [|m IHm]; intros Hlt; [ lia | ].
  destruct (Nat.eq_dec n m); subst.
  - now exists (fresh (freshlist_of_list l m ++ l) :: nil).
  - assert (n < m) as [ l' [_ Heq] ]%IHm by lia.
    exists (fresh (freshlist_of_list l m ++ l) :: l').
    split ; [ | rewrite <- app_comm_cons, <- Heq; reflexivity ].
    intros [=].
  Qed.

  Lemma freshlist_of_list_NoDup l n : NoDup (freshlist_of_list l n).
  Proof.
  induction n as [|n IHn]; cbn; constructor; [ intros [] | constructor | | assumption ].
  intros Hin. apply fresh_spec with (freshlist_of_list l n ++ l).
  apply in_or_app. left. assumption.
  Qed.

  Lemma freshlist_fresh l n : ~ In (freshlist l n) l.
  Proof.
  intros Hin.
  assert (In (freshlist l n) (freshlist_of_list l n)) as Hin2 by (destruct n; apply in_eq).
  exact (freshlist_of_list_fresh _ _ _ Hin2 Hin).
  Qed.

  Lemma freshlist_inj l n m : freshlist l n = freshlist l m -> n = m.
  Proof.
  enough (forall n m, n < m -> freshlist l n = freshlist l m -> n = m) as Hlt.
  { intros Heq.
    case (Nat.compare_spec n m); intros Ho; [ exact Ho | | ].
    - apply Hlt, Heq. exact Ho.
    - symmetry. symmetry in Heq. apply Hlt; assumption. }
  clear. intros n m Hlt Heq. exfalso.
  apply freshlist_of_list_prefix with (l:= l) in Hlt as [ l' [Hnil Hprf] ].
  unfold freshlist in Heq. rewrite Hprf in Heq.
  destruct l' as [|c l']; [ apply Hnil; reflexivity | ]. cbn in Heq.
  destruct n as [|n]; cbn in Heq, Hprf; rewrite Heq in Hprf.
  - assert (In c ((c :: l') ++ nil)) as Hin by apply in_eq.
    revert Hin. apply NoDup_remove_2. rewrite <- app_comm_cons, <- Hprf.
    apply (freshlist_of_list_NoDup l m).
  - assert (In c ((c :: l') ++ freshlist_of_list l n)) as Hin by apply in_eq.
    revert Hin. apply NoDup_remove_2. rewrite <- app_comm_cons, <- Hprf.
    apply (freshlist_of_list_NoDup l m).
  Qed.

  Definition Inh_of_InfDecType := {|
    inhcar := X;
    inh_dt := inhabitsT (fresh nil) |}.

End InfDecTypes.

Arguments infinite_nat_injective {_}.
Arguments freshlist {_} _ _.
Arguments Inh_of_InfDecType _ : clear implicits.


(** [nat] instance of [InfDecType] *)
Definition nat_infdectype := {|
  infcar := nat_dectype;
  fresh := (proj1_sig (section_choice (nat_bijective_section (existT _ id (id_bijective)))));
  fresh_spec := (proj2_sig (section_choice (nat_bijective_section (existT _ id (id_bijective))))) |}.
(* alternative direct construction *)
Definition nat_fresh l := S (list_max l).
Lemma nat_fresh_spec l : ~ In (nat_fresh l) l.
Proof.
enough (forall n h, ~ In (n + nat_fresh (h ++ l)) l) as Hh
  by (rewrite <- (app_nil_l l) at 1; apply (Hh 0)).
induction l as [|a l IHl]; unfold nat_fresh; cbn; intros n h Hin; [ destruct Hin | ].
destruct Hin as [Hin|Hin].
- enough (a < n + S (list_max (h ++ a :: l))) by lia.
  clear. induction h; simpl; lia.
- apply IHl with n (h ++ a :: nil).
  rewrite <- app_assoc. exact Hin.
Qed.
(*
Definition nat_infdectype := {|
  infcar := nat_dectype;
  fresh := nat_fresh;
  fresh_spec := nat_fresh_spec |}.
*)

(** [option] construction of [InfDecType] *)
Lemma nat_injective_option (T : Type) : nat_injective T -> nat_injective (option T).
Proof.
intros [i Hi].
exists (fun n => Some (i n)).
intros n m [= Heq]. apply Hi, Heq.
Qed.

Definition option_infdectype (D : InfDecType) := {|
  infcar := option_dectype D;
  fresh := (proj1_sig (@nat_injective_choice (option_dectype D)
                      (nat_injective_option infinite_nat_injective)));
  fresh_spec := (proj2_sig (@nat_injective_choice (option_dectype D)
                           (nat_injective_option infinite_nat_injective))) |}.
(* alternative definition could use: fresh := fun L => Some (fresh (SomeDown L))
                               with: SomeDown := nil => nil
                                               | None :: r => SomeDown r
                                               | Some x :: r => x :: SomeDown r *)

(** [sum] constructions of [InfDecType] *)
Lemma nat_injective_suml (T1 T2 : Type) : nat_injective T1 -> nat_injective (sum T1 T2).
Proof.
intros [i Hi].
exists (fun n => inl (i n)).
intros n m [= Heq]. apply Hi, Heq.
Qed.

Definition suml_infdectype (D1 : InfDecType) (D2 : DecType) := {|
  infcar := sum_dectype D1 D2;
  fresh := (proj1_sig (@nat_injective_choice (sum_dectype D1 D2)
                      (nat_injective_suml _ infinite_nat_injective)));
  fresh_spec := (proj2_sig (@nat_injective_choice (sum_dectype D1 D2)
                           (nat_injective_suml _ infinite_nat_injective))) |}.
(* alternative definition could use direct definition of fresh *)

Lemma nat_injective_sumr (T1 T2 : Type) : nat_injective T2 -> nat_injective (sum T1 T2).
Proof.
intros [i Hi].
exists (fun n => inr (i n)).
intros n m [= Heq]. apply Hi, Heq.
Qed.

Definition sumr_infdectype (D1 : DecType) (D2 : InfDecType) := {|
  infcar := sum_dectype D1 D2;
  fresh := (proj1_sig (@nat_injective_choice (sum_dectype D1 D2)
                      (nat_injective_sumr _ infinite_nat_injective)));
  fresh_spec := (proj2_sig (@nat_injective_choice (sum_dectype D1 D2)
                (nat_injective_sumr _ infinite_nat_injective))) |}.
(* alternative definition could use direct definition of fresh *)

(** [prod] constructions of [InfDecType] *)
Section Prod.

  Variable (ID : InfDecType) (D : InhDecType).

  Definition prodl_fresh (l : list (prod ID D)) : prod ID D :=
    (fresh (map fst l), inhabitantT inh_dt).

  Lemma notin_prodl_fresh l : ~ In (prodl_fresh l) l.
  Proof. intros Hin%(in_map fst). apply (fresh_spec _ Hin). Qed.

  Definition prodl_infdectype := {|
    infcar := prod_dectype ID D;
    fresh := prodl_fresh;
    fresh_spec := notin_prodl_fresh |}.

  Definition prodr_fresh (l : list (prod D ID)) : prod D ID :=
    (inhabitantT inh_dt, fresh (map snd l)).

  Lemma notin_prodr_fresh l : ~ In (prodr_fresh l) l.
  Proof. intros Hin%(in_map snd). apply (fresh_spec _ Hin). Qed.

  Definition prodr_infdectype := {|
    infcar := prod_dectype D ID;
    fresh := prodr_fresh;
    fresh_spec := notin_prodr_fresh |}.

End Prod.

Definition prod_infdectype (ID1 ID2 : InfDecType) := prodl_infdectype ID1 (Inh_of_InfDecType ID2).

(** [list] construction of [InfDecType] *)
Lemma nat_injective_list (T : Type) : inhabitedT T -> nat_injective (list T).
Proof.
intros [x]. exists (repeat x). intros n.
induction n as [|n IHn]; cbn; intros [|m] Heq; inversion Heq; [ reflexivity | ].
f_equal. apply IHn. assumption.
Qed.

Definition list_infdectype (D : InhDecType) := {|
  infcar := list_dectype D;
  fresh := (proj1_sig (@nat_injective_choice (list_dectype D) (nat_injective_list inh_dt)));
  fresh_spec := (proj2_sig (@nat_injective_choice (list_dectype D) (nat_injective_list inh_dt))) |}.
(* alternative definition could use: (x : D) : fresh := fun L => x :: concat L *)
