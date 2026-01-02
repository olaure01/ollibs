From Stdlib Require Import PeanoNat CMorphisms.
From OLlibs Require Import List_more SubList PermutationT.
From OLlibs Require DecidableT.
Import Logic_Datatypes_more.LogicNotations ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


Inductive sublistT A : crelation (list A) :=
| sublistT_nil : sublistT nil nil
| sublistT_cons a l1 l2 : sublistT l1 l2 -> sublistT (a :: l1) (a :: l2)
| sublistT_drop a l1 l2 : sublistT l1 l2 -> sublistT l1 (a :: l2).

Lemma sublistT_sublist A (l1 l2 : list A) : sublistT l1 l2 -> sublist l1 l2.
Proof. intro Hs. induction Hs; now constructor. Qed.

Lemma sublistT_nil_l A (l : list A) : sublistT [] l.
Proof. induction l; constructor. assumption. Qed.

Lemma sublistT_nil_r A (l : list A) : sublistT l [] -> l = [].
Proof. intro Hsub. destruct l as [|a l]; inversion Hsub. reflexivity. Qed.

Lemma sublistT_refl A (l : list A) : sublistT l l.
Proof. induction l; constructor. assumption. Qed.

Lemma sublistT_app_l A (l0 l1 l2 : list A) : sublistT l1 l2 -> sublistT l1 (l0 ++ l2).
Proof. induction l0 as [|a l0 IH]; intro Hsub; [ | apply sublistT_drop, IH ]; assumption. Qed.

Lemma sublistT_app_r A (l0 l1 l2 : list A) : sublistT l1 l2 -> sublistT l1 (l2 ++ l0).
Proof. intro Hsub. induction Hsub; [ apply sublistT_nil_l | constructor; assumption .. ]. Qed.

Lemma sublistT_app_app A (l1 l2 l3 l4 : list A) :
  sublistT l1 l2 -> sublistT l3 l4 -> sublistT (l1 ++ l3) (l2 ++ l4).
Proof.
intro Hsub1. induction Hsub1 as [ | ? ? ? ? IHHsub1 | ? ? ? ? IHHsub1 ];
  intro Hsub2; [ assumption | constructor; apply IHHsub1, Hsub2 .. ].
Qed.

Lemma sublistT_app_app_l A (l0 l1 l2 : list A) : sublistT l1 l2 -> sublistT (l0 ++ l1) (l0 ++ l2).
Proof. apply sublistT_app_app, sublistT_refl. Qed.

Lemma sublistT_app_app_r A (l0 l1 l2 : list A) : sublistT l1 l2 -> sublistT (l1 ++ l0) (l2 ++ l0).
Proof. intro. apply sublistT_app_app, sublistT_refl. assumption. Qed.

Lemma sublistT_inclT A (l1 l2 : list A) : sublistT l1 l2 -> inclT l1 l2.
Proof.
intro Hsub. induction Hsub as [ | | ? ? ? ? IHHsub ].
- apply inclT_nil_l.
- apply inclT_cons_cons. assumption.
- intros x Hx. right. apply IHHsub, Hx.
Qed.

Lemma sublistT_map A B (f : A -> B) l1 l2 : sublistT l1 l2 -> sublistT (map f l1) (map f l2).
Proof. intro Hsub. induction Hsub; constructor; assumption. Qed.

Lemma sublistT_trans A (l1 l2 l3 : list A) : sublistT l1 l2 -> sublistT l2 l3 -> sublistT l1 l3.
Proof.
intros Hsub1 Hsub2. induction Hsub2 as [ | ? ? ? ? IHHsub2 | ? ? ? ? IHHsub2 ] in l1, Hsub1 |- *.
- assumption.
- inversion_clear Hsub1; constructor; apply IHHsub2; assumption.
- apply IHHsub2 in Hsub1. apply sublistT_drop. assumption.
Qed.

Lemma sublistT_antisym A (l1 l2 : list A) : sublistT l1 l2 -> sublistT l2 l1 -> l1 = l2.
Proof.
intro Hsub1. induction Hsub1 as [ | ? l1 l2 Hsub1 IHHsub1 | ? l1 l2 Hsub1 _ ]; intro Hsub2.
- reflexivity.
- f_equal. apply IHHsub1. inversion_clear Hsub2 as [ | | ? ? ? Hsub Hsub' ]; [ assumption | exfalso ].
  apply sublistT_sublist, sublist_length in Hsub1, Hsub.
  apply (Nat.nle_succ_diag_l (length l2)).
  transitivity (length l1); assumption.
- exfalso. apply sublistT_sublist, sublist_length in Hsub1, Hsub2.
  apply (Nat.nle_succ_diag_l (length l2)).
  transitivity (length l1); assumption.
Qed.

#[export] Instance sublistT_preorder A : PreOrder (@sublistT A).
Proof. split; intro; [ apply sublistT_refl | apply sublistT_trans ]. Qed.

#[export] Instance sublistT_antisym' A : Antisymmetric eq (@sublistT A).
Proof. intro. apply sublistT_antisym. Qed.

Lemma sublistT_cons_inv A (a : A) l1 l2 : sublistT (a :: l1) (a :: l2) -> sublistT l1 l2.
Proof.
intro Hs. inversion Hs; subst; [ | transitivity (a :: l1); [ constructor; reflexivity | ] ]; assumption.
Qed.

Lemma sublistT_elt_l_inv A (a : A) l1' l1'' l2 :
  sublistT (l1' ++ a :: l1'') l2 ->
  {'(l2', l2'') & l2 = l2' ++ a :: l2'' & sublistT l1' l2' * sublistT l1'' l2'' }.
Proof.
intro Hs.
remember (l1' ++ a :: l1'') as l1 eqn:Hl1.
induction Hs as [ | b l1 l2 Hs' IH | b l1 l2 Hs' IH ] in l1', l1'', Hl1 |- *.
- decomp_list_eq Hl1.
- decomp_list_eq Hl1; subst.
  + specialize (IH _ _ eq_refl) as [[l2' l2''] -> [Hs2 Hs2']].
    exists (b :: l2', l2''); [ reflexivity | split ].
    * constructor. assumption.
    * assumption.
  + exists (nil, l2); [ reflexivity | now split ].
- subst.
  specialize (IH _ _ eq_refl) as [[l2' l2''] -> [Hs2 Hs2']].
  exists (b :: l2', l2''); [ reflexivity | split ].
  * constructor. assumption.
  * assumption.
Qed.

Lemma sublistT_cons_l_inv A (a : A) l1 l2 :
  sublistT (a :: l1) l2 -> {'(l2', l2'') & l2 = l2' ++ a :: l2'' & sublistT l1 l2'' }.
Proof.
intros [[l2' l2''] -> [Hs Hs']]%(sublistT_elt_l_inv _ nil).
exists (l2', l2''); [ reflexivity | assumption ].
Qed.

Lemma sublistT_sgt A (a : A) l : sublistT [a] l <=> InT a l.
Proof.
split.
- intros Hs%sublistT_inclT. apply Hs, inT_eq.
- intros [[l1 l2] ->]%inT_split.
  apply sublistT_app_l. constructor. apply sublistT_nil_l.
Qed.

Lemma sublistT_AddT A (a : A) l1 l2 : AddT a l1 l2 -> sublistT l1 l2.
Proof. induction 1; constructor; [ apply sublistT_refl | assumption ]. Qed.

Lemma sublistT_inT_extend A (a : A) l1 l2 :
  sublistT l1 l2 -> InT a l2 -> { l1' & sublistT l1' l2 & inclT (a :: l1) l1' * inclT l1' (a :: l1) }.
Proof.
intro Hsub. induction Hsub as [ | b l1 l2 Hsub IH | b l1 l2 Hsub IH ]; intro Hin.
- destruct Hin.
- destruct Hin as [[= ->] | Hin].
  + exists (a :: l1); [ | split ].
    * now constructor.
    * apply inclT_cons; [ apply inT_eq | apply inclT_refl ].
    * apply inclT_cons_cons, inclT_tl, inclT_refl.
  + destruct (IH Hin) as [l1' Hsub' [Hin' Hincl']].
    exists (b :: l1'); [ | split ].
    * now constructor.
    * apply inclT_cons_inv in Hin'.
      apply inclT_cons.
      -- apply inT_cons, (fst Hin').
      -- apply inclT_cons_cons, Hin'.
    * intros c [[= ->] | Hinc%Hincl'].
      -- apply inT_cons, inT_eq.
      -- destruct Hinc as [[= ->] | Hinc].
         ++ apply inT_eq.
         ++ apply inT_cons, inT_cons. assumption.
- destruct Hin as [[= ->] | Hin].
  + exists (a :: l1); [ | split ].
    * now constructor.
    * apply inclT_refl.
    * apply inclT_refl.
  + destruct (IH Hin) as [l1' Hsub' [Hin' Hincl']].
    exists l1'; [ | split ].
    * now constructor.
    * assumption.
    * assumption.
Qed.

Lemma sublistT_filter A f (l : list A) : sublistT (filter f l) l.
Proof. induction l as [ | a l IH ]; cbn; try destruct (f a); now constructor. Qed.


(* with decidable equality *)

Lemma uniquify_map_sublistT A B (eq_dec : forall x y:B, DecidableT.decidableP (x=y)) (f : A -> B) l :
  { l' & NoDupT (map f l') * inclT (map f l) (map f l') & sublistT (map f l') (map f l) }.
Proof.
induction l as [ | a l IHl ].
- exists nil; cbn; [ split | ]; [ | red; trivial | ]; constructor.
- destruct IHl as [l' [Hnd Hinc] Hsub].
  destruct (inT_decT eq_dec (f a) (map f l')).
  + exists l'; cbn; [ split | ]; [ assumption | | ].
    * intros x [|].
      -- now subst.
      -- now apply Hinc.
    * constructor. assumption.
  + exists (a :: l'); cbn; [ split | ].
    * now constructor.
    * intros x [|].
      -- subst. now left.
      -- right. now apply Hinc.
    * constructor. assumption.
Qed.

Lemma uniquify_sublistT A (eq_dec : forall x y:A, DecidableT.decidableP (x=y)) (l:list A) :
  { l' & NoDupT l' * inclT l l' & sublistT l' l }.
Proof.
destruct (uniquify_map_sublistT eq_dec id l) as [l' H].
now exists l'; rewrite !map_id in *.
Qed.


Lemma sublistT_PermutationT A (l1 l2 l2' : list A) :
  sublistT l1 l2 -> PermutationT l2 l2' -> { l1' & PermutationT l1 l1' & sublistT l1' l2' }.
Proof.
intros Hs HP. induction HP as [ | x l l' ? IH | x y | ? ? ? ? IH1 ? IH2 ] in l1, Hs |- *.
- inversion Hs. subst.
  exists nil; constructor.
- inversion Hs as [ | ? ? ? Hs' HP' IHs | ? ? ? Hs' HP' IHs ]; subst.
  + apply IH in Hs' as [l1' Hs1' HP1'].
    exists (x :: l1'); constructor; assumption.
  + apply IH in Hs' as [l1' Hs1' HP1'].
    exists l1'.
    * assumption.
    * constructor; assumption.
- inversion Hs as [ | ? l0 ? Hs' HP IHs | ? ? ? Hs' HP IHs ]; subst.
  + inversion Hs' as [ | ? l1 ? Hs'' HP' IHs' | ? ? ? Hs'' HP' IHs' ]; subst.
    * exists (x :: y :: l1).
      -- constructor.
      -- do 2 constructor; assumption.
    * exists (y :: l0).
      -- reflexivity.
      -- do 2 constructor; assumption.
  + inversion Hs' as [ | ? l0 ? Hs'' HP' IHs' | ? ? ? Hs'' HP' IHs' ]; subst.
    * exists (x :: l0).
      -- reflexivity.
      -- do 2 constructor; assumption.
    * exists l1.
      -- reflexivity.
      -- do 2 constructor; assumption.
- apply IH1 in Hs. destruct Hs as [l1' HP1' Hs1'].
  apply IH2 in Hs1'. destruct Hs1' as [l2' HP2' Hs2'].
  exists l2'; [ transitivity l1' | ]; assumption.
Qed.

Lemma PermutationT_sublistT A (l1 l1' l2' : list A) :
  PermutationT l1 l1' -> sublistT l1' l2' -> { l2 & sublistT l1 l2 & PermutationT l2 l2' }.
Proof.
intro HP. induction HP as [ | x ? ? ? IH | x y | ? ? ? ? IH1 ? IH2 ] in l2' |- *; intro Hs.
- now exists l2'.
- apply sublistT_cons_l_inv in Hs as [[l2'' l2'''] -> Hs].
  apply IH in Hs as [l2' Hs HP'].
  exists (x :: l2'' ++ l2').
  + constructor. apply sublistT_app_l. assumption.
  + rewrite HP'. apply PermutationT_middle.
- apply sublistT_cons_l_inv in Hs as [[l2'' l2'''] -> Hs].
  apply sublistT_cons_l_inv in Hs as [[l3'' l3'''] -> Hs].
  exists (y :: x :: l2'' ++ l3'' ++ l3''').
  + do 2 constructor. apply sublistT_app_l, sublistT_app_l. assumption.
  + rewrite (app_comm_cons l3'' _ x), (app_assoc _ _ (y :: _)).
    apply PermutationT_cons_app. list_simpl. apply PermutationT_middle.
- apply IH2 in Hs as [l2 HP2' Hs2'].
  apply IH1 in HP2' as [l1' HP1' Hs1'].
  exists l1'; [ | transitivity l2 ]; assumption.
Qed.

Lemma sublistT_as_PermutationT A (l1 l2 : list A) :
  sublistT l1 l2 -> { l & PermutationT (l1 ++ l) l2 }.
Proof.
intro Hs. induction Hs as [ | ? ? ? ? [l HP] | a ? ? ? [l HP] ].
- exists nil. reflexivity.
- exists l. constructor. assumption.
- exists (a :: l). rewrite <- HP. symmetry. apply PermutationT_middle.
Qed.

Lemma NoDupT_sublistT A (l1 l2 : list A) : sublistT l1 l2 -> NoDupT l2 -> NoDupT l1.
Proof.
intros [m HP]%sublistT_as_PermutationT Hnd.
symmetry in HP. apply PermutationT_NoDupT, NoDupT_NoDup in HP; [ | assumption ].
apply NoDup_NoDupT, (NoDup_app_remove_r _ _ HP).
Qed.
