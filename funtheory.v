(** Properties of functions *)

From Stdlib Require Import Program.Basics Relation_Definitions RelationClasses List.
  (* do not export Program.Basics to avoid impact on [flip] and [arrow] for setoid_rewriting *)
From OLlibs Require Import inhabitedT.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


(* copy of Basics.compose to avoid exporting full Basics *)
Definition compose {A B C} (g : B -> C) (f : A -> B) := fun x : A => g (f x).


(** * Functions on constructors *)
Definition Empty_fun {A} : Empty_set -> A := fun o => match o with end.

Definition option_eval_default A B default (f : A -> B) o :=
  match o with
  | Some a => f a
  | None => default
  end.

Definition option_test A := @option_eval_default A Prop True.

Definition option_testT A := @option_eval_default A Type unit.


(** * Retraction pairs *)

Definition retract A B (s : B -> A) (i : A -> B) := forall x, s (i x) = x.

Lemma id_retract A : retract (@id A) id.
Proof. intros x. reflexivity. Qed.

Lemma compose_retract A B C (s1 : B -> A) (s2 : C -> B) i1 i2 :
  retract s1 i1 -> retract s2 i2 -> retract (compose s1 s2) (compose i2 i1).
Proof. intros Hr1 Hr2 x. unfold compose. rewrite Hr2, Hr1. reflexivity. Qed.

Definition embedding A B := {'(s,i) : (B -> A) * (A -> B) | retract s i }.

Lemma id_embedding A : embedding A A.
Proof. exists (id, id). unfold retract, id. reflexivity. Qed.


Section Function.

  Variable A B : Type.
  Variable f : A -> B.

  (** ** Injective functions *)

  (** Same definition as in standard library [Stdlib.Sets.Image] *)
  Definition injective := forall x y, f x = f y -> x = y.

  Lemma injective_neq : injective -> forall x y, x <> y -> f x <> f y.
  Proof. intros Hi x y Hneq Heq. exact (Hneq (Hi _ _ Heq)). Qed.

  Lemma section_injective g : retract g f -> injective.
  Proof. intros Hsec x y Hf. rewrite <- Hsec, Hf, Hsec. reflexivity. Qed.

  Lemma injective_NoDup : injective -> forall l, NoDup l -> NoDup (map f l).
  Proof.
  (* from Logic.FinFun
  intros Ij. induction 1 as [|x l X N IH]; cbn; constructor; trivial.
  rewrite in_map_iff. intros (y & E & Y). apply Ij in E. now subst.
  *)
  intros Hinj l. induction l as [|a l IHl]; cbn; intros Hnd.
  - constructor.
  - inversion Hnd as [|a' l' Hnin Hnd']; constructor; subst.
    + intros Hin. apply Hnin.
      apply in_map_iff in Hin as [x [->%Hinj Hin]].
      exact Hin.
    + apply IHl, Hnd'.
  Qed.

  (** ** Surjective functions *)

  Definition decT_image := forall y, { x | y = f x } + forall x, y <> f x.

  Lemma injective_decT_image_section : inhabitedT A -> injective -> decT_image ->
    { g & retract g f }.
  Proof.
  intros [a] Hi Hd.
  exists (fun y => match (Hd y) with
                   | inl (exist _ x _) => x
                   | _ => a
                   end).
  intros x.
  destruct (Hd (f x)) as [[x' ->%Hi]|Hneq]; [ | contradiction (Hneq x) ]; reflexivity.
  Qed.

  Definition surjective := forall y, { x | y = f x }.

  Lemma surjective_decT_image : surjective -> decT_image.
  Proof. intros Hs y. left. exact (Hs y). Qed.

  Lemma retract_surjective g : retract f g -> surjective.
  Proof. intros Hr y. exists (g y). rewrite Hr. reflexivity. Qed.

  Lemma surjective_retract (Hs : surjective) : retract f (fun y => proj1_sig (Hs y)).
  Proof. intros y. symmetry. exact (proj2_sig (Hs y)). Qed.

  (** ** Bijective functions *)

  Definition bijective := forall y, { x | y = f x & forall x', y = f x' -> x = x' }.

  Lemma bijective_inverse : bijective -> { g | retract f g & retract g f }.
  Proof.
  intros Hbij.
  exists (fun x => proj1_sig (sig_of_sig2 (Hbij x))); intros x; cbn.
  - destruct (Hbij x) as [y <- _]. reflexivity.
  - destruct (Hbij (f x)) as [y _ Heq]. apply Heq. reflexivity.
  Qed.

  Lemma bijective_injective : bijective -> injective.
  Proof.
  intros Hbij.
  destruct (bijective_inverse Hbij) as [g _ Hsec].
  apply section_injective with g, Hsec.
  Qed.

  Lemma bijective_surjective : bijective -> surjective.
  Proof. intros Hbij y. destruct (Hbij y) as [x -> _]. exists x. reflexivity. Qed.

  Lemma injective_surjective_bijective : injective -> surjective -> bijective.
  Proof.
  intros Hinj Hsurj y.
  destruct (Hsurj y) as [x ->].
  exists x; [ reflexivity | ].
  intros x' Heq2. apply Hinj. assumption.
  Qed.

  Lemma biretract_bijective g : retract f g -> retract g f -> bijective.
  Proof.
  intros Hfg Hgf.
  apply injective_surjective_bijective.
  - apply section_injective with g, Hgf.
  - apply retract_surjective with g, Hfg.
  Qed.

End Function.


(** * More Properties of Injective Functions *)

Lemma id_injective A : injective (@id A).
Proof. intros x y Heq. unfold id in Heq. assumption. Qed.

Lemma compose_injective A B C (f : A -> B) (g : B -> C) :
  injective f -> injective g -> injective (compose g f) .
Proof. unfold injective. auto. Qed.

Lemma map_injective A B (f : A -> B) : injective f -> injective (map f).
Proof.
intros Hf l1.
induction l1 as [|a l1 IHl1]; intros [|b l2] Hmap; inversion Hmap as [[Hhd Htl]].
- reflexivity.
- apply Hf in Hhd as ->.
  apply IHl1 in Htl as ->.
  reflexivity.
Qed.

Lemma map_injective_in A B (f : A -> B) l1 l2 :
  (forall x y, In x l1 -> In y l2 -> f x = f y -> x = y) ->
  map f l1 = map f l2 -> l1 = l2.
Proof.
induction l1 as [|a l1 IHl1] in l2 |-*; intros Hi Hmap; destruct l2; inversion Hmap as [ [Hhd Htl] ].
- reflexivity.
- apply Hi in Hhd as ->; [ | apply in_eq .. ].
  apply IHl1 in Htl as ->; [ reflexivity | ].
  intros. apply Hi; [ right .. | ]; assumption.
Qed.

(** ** Inverse image of a relation by a(n injective) function *)

Section Inverse_image.

  Variable A B : Type.
  Variable f : A -> B.

  Variable R : relation B.

  Definition f_R := fun x y => R (f x) (f y).

  Lemma PreOrder_inverse_image : PreOrder R -> PreOrder f_R.
  Proof.
  intros [Hrefl Htrans]. unfold f_R. split.
  - intros x. apply Hrefl.
  - intros x y z HR1 HR2. exact (Htrans _ _ _ HR1 HR2).
  Qed.

  Lemma Equivalence_inverse_image : Equivalence R -> Equivalence f_R.
  Proof.
  intros [Hrefl Hsym Htrans]. unfold f_R. split.
  - intros x. apply Hrefl.
  - intros x y HR. exact (Hsym _ _ HR).
  - intros x y z HR1 HR2. exact (Htrans _ _ _ HR1 HR2).
  Qed.

  Lemma PartialOrder_injective (f_inj : injective f) Ro :
    @PartialOrder _ eq _ _ Ro -> @PartialOrder _ eq _ _ (PreOrder_inverse_image Ro).
  Proof.
  intros Rp x y. split.
  - intros ->. clear Rp. apply PreOrder_inverse_image in Ro. split; reflexivity.
  - intros [Hr Hs].
    destruct Rp with (f x) (f y) as [_ Hf].
    apply f_inj, Hf. split; assumption.
  Qed.

End Inverse_image.


(** * More Properties of Surjective Functions *)

Lemma id_surjective A : surjective (@id A).
Proof. intros x. exists x. reflexivity. Qed.

Lemma compose_surjective A B C (f : A -> B) (g : B -> C) :
  surjective f -> surjective g -> surjective (compose g f).
Proof. intros Hf Hg z. destruct (Hg z) as [y ->], (Hf y) as [x ->]. exists x. reflexivity. Qed.

Lemma map_surjective A B (f : A -> B) : surjective f -> surjective (map f).
Proof.
intros Hf l1. induction l1 as [| a l1 IHl1].
- exists nil. reflexivity.
- destruct (Hf a) as [b ->], IHl1 as [l ->].
  exists (b :: l). reflexivity.
Qed.


(** * More Properties of Bijective Functions *)

Lemma id_bijective A : bijective (@id A).
Proof. intros x. exists x; trivial. Qed.
Arguments id_bijective {_}.

Lemma compose_bijective A B C (f : A -> B) (g : B -> C) : bijective f -> bijective g ->
  bijective (compose g f).
Proof.
intros Hf Hg z.
destruct (Hg z) as [y -> Hinjf], (Hf y) as [x -> Hinjg].
exists x; [ reflexivity | ].
intros x' Heq. apply Hinjg, Hinjf, Heq.
Qed.


(** * Extensional equality of functions *)

Definition ext_eq A B (f g : A -> B) := forall a, f a = g a.
Notation " f ~ g " := (ext_eq f g) (at level 60).

Lemma compose_ext_eq A B C (f1 g1 : A -> B) (f2 g2 : B -> C) :
  f1 ~ g1 -> f2 ~ g2 -> compose f2 f1 ~ compose g2 g1.
Proof.
intros Hext1 Hext2 x.
unfold compose. rewrite (Hext1 x), (Hext2 (g1 x)). reflexivity.
Qed.

#[export] Instance ext_eq_refl A B : Reflexive (@ext_eq A B).
Proof. intros f x. reflexivity. Qed.

#[export] Instance ext_eq_sym A B : Symmetric (@ext_eq A B).
Proof. intros f g Heq x. rewrite (Heq x). reflexivity. Qed.

#[export] Instance ext_eq_trans A B : Transitive (@ext_eq A B).
Proof. intros f g h Heq1 Heq2 x. rewrite (Heq1 x), (Heq2 x). reflexivity. Qed.

Lemma id_compose_ext A B (f : A -> B) : compose id f ~ f.
Proof. intro x. reflexivity. Qed.

Lemma compose_id_ext A B (f : A -> B) : compose f id ~ f.
Proof. intro x. reflexivity. Qed.

Lemma compose_assoc_ext A B C D (f : A -> B) (g : B -> C) (h : C -> D) :
  compose h (compose g f) ~ compose (compose h g) f.
Proof. intro x. reflexivity. Qed.

Lemma injective_ext A B (f g : A -> B) : injective f -> f ~ g -> injective g.
Proof. intros Hi Heq x y Hg. apply Hi. rewrite (Heq x), (Heq y). assumption. Qed.

Lemma surjective_ext A B (f g : A -> B) : surjective f -> f ~ g -> surjective g.
Proof. intros Hs Heq y. destruct (Hs y) as [x ->]. exists x. apply Heq. Qed.

Lemma bijective_ext A B (f g : A -> B) : bijective f -> f ~ g -> bijective g.
Proof.
intros Hs Heq y. destruct (Hs y) as [x -> Hi]. exists x.
- apply Heq.
- intros y Hy. apply Hi.
  rewrite (Heq y). assumption.
Qed.

Lemma map_ext A B (f g : A -> B) : f ~ g -> map f ~ map g.
Proof. intros Heq l. induction l as [|a l IHl]; [ | cbn; rewrite IHl, (Heq a) ]; reflexivity. Qed.


(** * Additional definitions *)

(* Binary functions *)
Definition injective2 A B C (f : A -> B -> C) :=
  forall x y x' y', f x y = f x' y' -> x = x' /\ y = y'.

Definition surjective2 A B C (f : A -> B -> C) := forall z, {'(x, y) | z = f x y }.
