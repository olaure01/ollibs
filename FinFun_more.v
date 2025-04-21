(** Finite sets as finite subsets (witnessed by a list of elements) of a Type *)

From Stdlib Require Import PeanoNat Relation_Definitions.
From Stdlib Require Export FinFun.
From OLlibs Require Import List_more DecidableT dectype infinite.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


(* TODO move to Relation_Definitions if useful elsewhere
   and consider making argument A implicit (might break a lot of things in Rocq *)
Definition irreflexive A R : Prop := forall x : A, ~ R x x.
Arguments irreflexive : clear implicits.


Section Finite.

Variable (A : Type) (eq_dec : forall x y : A, decidableP (x = y)).
Variable (P : A -> Prop) (PdecT : forall x : A, decidableT (P x)).
(* this could be replaced by (P : Ensemble A) by using Stdlib.Ensembles *)

Definition finite_subset := exists l, NoDup l /\ forall x, P x <-> In x l.

Definition wfinite_subset := exists l, forall x, P x -> In x l.

Lemma finite_wfinite : finite_subset -> wfinite_subset.
Proof. intros [lP [_ HP]]. exists lP. apply HP. Qed.

Lemma wfinite_finite : wfinite_subset -> finite_subset.
Proof using eq_dec PdecT.
intros [l Hf].
exists (nodup eq_dec (filter (fun x => if (PdecT x) then true else false) l)). split.
- apply NoDup_nodup.
- intro x. split.
  + intro HP. apply nodup_In, filter_In. split.
    * exact (Hf _ HP).
    * destruct (PdecT x) as [|HnP]; [ reflexivity | contradiction HnP ].
  + intros [_ Hin]%nodup_In%filter_In.
    destruct (PdecT x); [ assumption | discriminate Hin ].
Qed.

End Finite.

Lemma finite_subset_dec A (P : A -> Prop) : finite_subset P ->
  forall x y, P x -> P y -> decidable (x = y).
Proof. intros [l [Hnd Hf]] x y Hx%Hf Hy%Hf. exact (ListDec.NoDup_list_decidable Hnd _ _ Hx Hy). Qed.

Lemma wfinite_subset_subset A (P Q : A -> Prop) : (forall x, Q x -> P x) -> wfinite_subset P -> wfinite_subset Q.
Proof. intros Hsub [eltsP HP]. exists eltsP. intros x Hx. apply HP, Hsub, Hx. Qed.

Lemma finite_subset_subset A (P Q : A -> Prop) (QdecT : forall x, decidableT (Q x)) :
  (forall x, Q x -> P x) -> finite_subset P -> finite_subset Q.
Proof.
intros Hsub [eltsP [HndP HP]].
exists (filter (fun x => if QdecT x then true else false) eltsP). split.
- apply NoDup_filter, HndP.
- intro x. split.
  + intro HQx. apply filter_In. split.
    * apply HP, Hsub, HQx.
    * destruct (QdecT x) as [HQ|HnQ]; [ reflexivity | contradiction HnQ ].
  + intro Hin. apply filter_In in Hin as [_ Hin].
    destruct (QdecT x); [ assumption | discriminate Hin ].
Qed.

Lemma wfinite_NoDup A (eq_dec : forall x y : A, decidableP (x = y)) (P : A -> Prop) :
  wfinite_subset P -> wfinite_subset (fun l => Forall P l /\ NoDup l).
Proof.
intros [lP HP]. induction lP as [|a lP IHlP] in P, HP |- *.
- exists (nil :: nil). intros [|a l].
  + intros _. apply in_eq.
  + intros [HPa _]. inversion_clear HPa as [|? ? Ha _]. destruct (HP _ Ha).
- destruct (IHlP (fun x => P x /\ x <> a)) as [lP' HP'].
  { intros x [HPx Hxa]. apply HP in HPx. inversion HPx; [ subst | assumption ].
    contradiction Hxa. reflexivity. }
  exists (lP' ++ map (fun '(x, y) => app x (a :: y)) (list_prod lP' lP')).
  intros l [HPl Hnd].
  destruct (in_dec eq_dec a l) as [Hin|Hnin]; apply in_or_app; [right|left].
  + apply in_split in Hin as [l1 [l2 ->]].
    change (l1 ++ a :: l2) with ((fun '(x, y) => app x (a :: y)) (l1, l2)).
    apply in_map, in_prod; apply HP'; split.
    * apply Forall_app in HPl as [HPl _].
      apply Forall_forall. intros x Hin1. apply Forall_forall with (x := x) in HPl; [ | assumption ].
      split; [ assumption | intros -> ].
      apply in_split in Hin1 as [l1' [l2' ->]]. list_simpl in Hnd. apply NoDup_app_remove_l in Hnd.
      inversion_clear Hnd as [|? ? Hina _]. apply Hina, in_elt.
    * apply NoDup_app_remove_r in Hnd. assumption.
    * apply Forall_app in HPl as [_ HPl]. inversion_clear HPl as [|? ? _ Ht].
      apply Forall_forall. intros x Hin2. apply Forall_forall with (x := x) in Ht; [ | assumption ].
      split; [ assumption | intros -> ].
      apply in_split in Hin2 as [l1' [l2' ->]]. list_simpl in Hnd. apply NoDup_app_remove_l in Hnd.
      inversion_clear Hnd as [|? ? Hina _]. apply Hina, in_elt.
    * apply NoDup_app_remove_l in Hnd. inversion Hnd. assumption.
  + apply HP'. split; [ | assumption ].
    apply Forall_forall. intros x Hin. apply Forall_forall with (x := x) in HPl; [ | assumption ].
    split; [ assumption | intros -> ]. contradiction Hnin.
Qed.

Lemma finite_minimization A (P : A -> Prop) (Pfin : finite_subset P) f a (Ha : P a) :
  exists m, P m /\ forall m', P m' -> f m <= f m'.
Proof.
assert (Hdec := finite_subset_dec Pfin).
destruct Pfin as [lP [Hnd HP]].
induction lP as [ | b [ | c l ] IH ] in P, Hdec, Hnd, HP, a, Ha |- *; [ contradiction (proj1 (HP a)) | | ].
- exists b. split.
  + apply HP, in_eq.
  + intros m' Hm'. apply HP in Hm' as [-> | []]. reflexivity.
- destruct (IH (fun x => P x /\ x <> b)) with c as [m' [Hm' Hmin]].
  + apply NoDup_cons_iff in Hnd as [_ Hnd]. assumption.
  + intro x. split.
    * intros [HPx Hneq]. apply HP in HPx as [ | ].
      -- contradiction Hneq. subst x. reflexivity.
      -- assumption.
    * intros [-> | Hin]; split.
      -- apply HP. right. apply in_eq.
      -- intros ->. inversion Hnd as [ | ? ? Hinb _ ]. apply Hinb, in_eq.
      -- apply HP. right. right. assumption.
      -- intros ->. inversion Hnd as [ | ? ? Hinb _ ]. contradiction Hinb. right. assumption.
  + split.
    * apply HP. right. apply in_eq.
    * intros ->. inversion Hnd as [ | ? ? Hinb _ ]. apply Hinb, in_eq.
  + intros x y [HPx _] [HPy _]. apply Hdec; assumption.
  + assert (P b) as HPb by apply HP, in_eq.
    destruct (Compare_dec.le_lt_dec (f m') (f b)).
    * exists m'. split.
      -- apply Hm'.
      -- intros x HPx. destruct (Hdec x b HPx HPb) as [-> | Hneq]; [ assumption | ].
      apply Hmin. split; assumption.
    * exists b. split.
      -- apply HP, in_eq.
      -- intros x HPx. destruct (Hdec x b HPx HPb) as [-> | Hneq]; [ reflexivity | ].
         enough (f m' <= f x) by (apply Nat.lt_le_incl, (Nat.lt_le_trans _ (f m')); assumption).
         apply Hmin. split; assumption.
Qed.

Lemma finite_strictorder_max A (eq_dec : ListDec.decidable_eq A) (P : A -> Prop)
  (R : relation A) (Rdec : forall x y, decidableP (R x y)) d (Hd : P d) :
  finite_subset P -> transitive _ R -> irreflexive _ R ->
  exists a, P a /\ forall b, P b -> ~ R a b.
Proof.
intros [l [Hnd HP]] Htrans Hirrefl. induction l as [|x l IH] in P, d, Hd, Hnd, HP |- *.
{ specialize (HP d) as [HP _]. destruct (HP Hd). }
specialize (IH (fun z => P z /\ z <> x)).
destruct l as [|y l].
{ exists d. split; [ assumption | ].
  intros b Pb.
  apply HP in Hd. inversion Hd as [-> | []].
  apply HP in Pb. inversion Pb as [-> | []].
  apply Hirrefl. }
destruct (IH y) as [m [[Pm Hnmx] Hm]].
- split.
  + apply HP. right. apply in_eq.
  + intros ->. inversion_clear Hnd as [|? ? Hinx _]. apply Hinx, in_eq.
- inversion Hnd. assumption.
- intro z. specialize (HP z) as [Hfin1 Hfin2]. split.
  + intros [Pz Hnzx]. apply Hfin1 in Pz. destruct Pz as [->|Hin]; [ | assumption ].
    contradiction Hnzx. reflexivity.
  + intro Hin. split.
    * apply Hfin2. right. assumption.
    * intros ->. inversion_clear Hnd as [|? ? Hinx _]. contradiction Hinx.
- destruct (Rdec m x) as [Hmx|Hmx].
  + exists x. split.
    * apply HP, in_eq.
    * intros b Pb HR. apply (Hm b).
      -- split; [ assumption | intros -> ]. apply (Hirrefl x HR).
      -- apply (Htrans _ x); assumption.
  + exists m. split; [ assumption | ].
    intros b Pb. destruct (eq_dec x b) as [-> | Hneq]; [ assumption | ].
    apply Hm. split; [ assumption | intros -> ]. contradiction Hneq. reflexivity.
Qed.

Lemma wfinite_not_infinite A (P : A -> Prop) lP (HP : forall x, P x -> In x lP) (f : list A -> A) :
  P (f lP) -> exists l, In (f l) l.
Proof. intro Hf. exists lP. apply HP, Hf. Qed.

Lemma wfinite_not_infinite' A (P : A -> Prop) (Pfin : wfinite_subset P) (f : list A -> A) :
  (forall l, P (f l)) -> ~ (forall l, ~ In (f l) l).
Proof.
intro Hf.
destruct Pfin as [lP HP].
destruct (wfinite_not_infinite _ _ HP _ (Hf lP)) as [lP' HP'].
intro Hin. exact (Hin _ HP').
Qed.

Definition is_finite A := finite_subset (fun _ : A => True).

Lemma is_finite_Finite' A : is_finite A <-> Finite' A.
Proof.
split.
- intros [l [Hnd HP]].
  exists l. split; [ assumption | ].
  intro x. apply HP. exact I.
- intros [l [Hnd Hf]]. exists l. split; [ assumption | ].
  intro x. split; intro.
  + apply Hf.
  + exact I.
Qed.

Definition is_wfinite A := wfinite_subset (fun _ : A => True).

Lemma is_wfinite_Finite A : is_wfinite A <-> Finite A.
Proof. split; intros [l Hf]; exists l; intro x; [ | intros _]; apply Hf. exact I. Qed.

Lemma infinite_not_wfinite (A : InfDecType) : not (is_wfinite A).
Proof. destruct A as [A f HA]. intros [l Hl]. cbn in *. apply (HA l), Hl, I. Qed.
