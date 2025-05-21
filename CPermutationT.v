(** Cyclic Permutations
Definition and basic properties of cyclic permutations in [Type]. *)

From Stdlib Require Import CMorphisms PeanoNat.
From Stdlib Require CPermutation.
From OLlibs Require Import List_more PermutationT_more funtheory.
Import ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


(** * Definition *)
Inductive CPermutationT A : crelation (list A) :=
| cpermT : forall l1 l2, CPermutationT (l1 ++ l2) (l2 ++ l1).

#[export] Instance CPermutationT_PermutationT A :
   Proper (@CPermutationT A ==> @PermutationT A) id.
Proof. intros ? ? []. apply PermutationT_app_comm. Qed.

Lemma CPermutationT_CPermutation A (l1 l2 : list A) :
  CPermutationT l1 l2 -> CPermutation.CPermutation l1 l2.
Proof. intros []. constructor. Qed.


(** * Properties *)

#[export] Instance CPermutationT_refl A : Reflexive (@CPermutationT A).
Proof.
intro l.
assert (CPermutationT (nil ++ l) (l ++ nil))
  as HC by (eapply cpermT).
simpl in HC.
now rewrite app_nil_r in HC.
Qed.

#[export] Instance CPermutationT_sym A : Symmetric (@CPermutationT A).
Proof. intros ? ? []. apply cpermT. Qed.

#[export] Instance CPermutationT_trans A : Transitive (@CPermutationT A).
Proof.
intros l1 l2 l3 [l4 l5] HC2. inversion HC2 as [l6 l7 H1 H2]. subst.
decomp_app_eq_app H1 as [[l2' <- ->] | [l4' -> <-]].
- rewrite <- app_assoc, app_assoc. apply cpermT.
- rewrite <- app_assoc, (app_assoc l7). apply cpermT.
Qed.

#[export] Instance CPermutationT_equiv A : Equivalence (@CPermutationT A).
Proof.
split.
- apply CPermutationT_refl.
- apply CPermutationT_sym.
- apply CPermutationT_trans.
Qed.

Lemma CPermutationT_split A (l1 l2 : list A) :
  CPermutationT l1 l2 -> { n | l2 = skipn n l1 ++ firstn n l1 }.
Proof.
intros [l1' l2'].
exists (length l1').
rewrite skipn_app, skipn_all, Nat.sub_diag. cbn. f_equal.
now rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r.
Qed.

Lemma CPermutationT_skipn_firstn A (l : list A) n : CPermutationT l (skipn n l ++ firstn n l).
Proof.
transitivity (firstn n l ++ skipn n l); [ | constructor ].
now rewrite (firstn_skipn n).
Qed.

Lemma CPermutationT_app A (l1 l2 l3 : list A) :
  CPermutationT (l1 ++ l2) l3 -> CPermutationT (l2 ++ l1) l3.
Proof. intro HC. exact (CPermutationT_trans (cpermT _ _) HC). Qed.

Theorem CPermutationT_app_comm A (l1 l2 : list A) :
  CPermutationT (l1 ++ l2) (l2 ++ l1).
Proof. apply cpermT. Qed.

Lemma CPermutationT_app_rot A (l1 l2 l3 : list A) :
  CPermutationT (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof. rewrite (app_assoc l2). apply cpermT. Qed.

Lemma CPermutationT_cons_append A (a : A) l :
  CPermutationT (a :: l) (l · a).
Proof. intros. rewrite <- (app_nil_l l), app_comm_cons. apply cpermT. Qed.

Lemma CPermutationT_swap A (a b : A) : CPermutationT (a :: b :: nil) (b :: a :: nil).
Proof.
intros.
change (a :: b :: nil) with ((a :: nil) ++ (b :: nil)).
change (b :: a :: nil) with ((b :: nil) ++ (a :: nil)).
apply cpermT.
Qed.

Lemma CPermutationT_cons A l1 (a : A) l2 :
  CPermutationT (l1 · a) l2 -> CPermutationT (a :: l1) l2.
Proof. intro. now apply (CPermutationT_app l1 (a :: nil)). Qed.

Lemma CPermutationT_morph_cons A (P : list A -> Prop) :
  (forall a l, P (l · a) -> P (a :: l)) ->
  Proper (@CPermutationT A ==> Basics.impl) P.
Proof.
intros HP l1 l2 [l3 l4] HPl.
induction l4 as [|a l4 IHl4] in l3, HPl |- * using rev_ind.
- now rewrite app_nil_r in HPl.
- rewrite app_assoc in HPl. rewrite <- app_assoc, <- app_comm_cons, app_nil_l.
  apply IHl4, HP, HPl.
Qed.

Lemma CPermutationT_nil A (l : list A) : CPermutationT nil l -> l = nil.
Proof. now intro; apply PermutationT_nil, CPermutationT_PermutationT. Qed.

Lemma CPermutationT_nil_cons A l (a : A) : notT (CPermutationT nil (a :: l)).
Proof. intros [=]%CPermutationT_nil. Qed.

Lemma CPermutationT_length_1 A (a b : A) :
  CPermutationT (a :: nil) (b :: nil) -> a = b.
Proof. now intro; apply PermutationT_length_1, CPermutationT_PermutationT. Qed.

Lemma CPermutationT_length_2 A (a1 a2 b1 b2 : A) :
  CPermutationT (a1 :: a2 :: nil) (b1 :: b2 :: nil) -> { a1 = b1 /\ a2 = b2 } + { a1 = b2 /\ a2 = b1 }.
Proof. now intro; apply PermutationT_length_2, CPermutationT_PermutationT. Qed.

Lemma CPermutationT_length_1_inv A (a : A) l : CPermutationT (a :: nil) l -> l = a :: nil.
Proof. now intro; apply PermutationT_length_1_inv, CPermutationT_PermutationT. Qed.

Lemma CPermutationT_length_2_inv A (a : A) b l :
  CPermutationT (a :: b :: nil) l -> { l = a :: b :: nil } + { l = b :: a :: nil }.
Proof. now intro; apply PermutationT_length_2_inv, CPermutationT_PermutationT. Qed.

Lemma CPermutationT_length_3_inv A (a b c : A) l:
  CPermutationT [a ; b; c] l -> (l = [a; b; c]) + (l = [b; c; a]) + (l = [c; a; b]).
Proof.
intro HC. inversion HC as [l1 l2 Heq1 Heq2].
destruct l1 as [|x [|y l1]].
- left. left. rewrite app_nil_r. reflexivity.
- left. right. injection Heq1 as [= -> ->]. reflexivity.
- injection Heq1 as [= -> -> Heq].
  apply app_eq_unitT in Heq as [[-> ->]|[-> ->]].
  + right. reflexivity.
  + left. left. reflexivity.
Qed.

Lemma CPermutationT_vs_elt_inv A (a : A) l l1 l2 :
  CPermutationT l (l1 ++ a :: l2) -> {'(l1',l2') | l2 ++ l1 = l2' ++ l1' & l = l1' ++ a :: l2' }.
Proof.
intro HC. inversion HC as [l3 l4 H1 H2]. subst.
decomp_elt_eq_app H2 as [[l <- ->]|[l -> <-]].
- now exists (l3 ++ l1, l); cbn; rewrite <- app_assoc.
- now exists (l, l2 ++ l4); cbn; rewrite <- app_assoc.
Qed.

Lemma CPermutationT_vs_cons_inv A (a : A) l l1 :
  CPermutationT l (a :: l1) -> {'(l1',l2') | l1 = l2' ++ l1' & l = l1' ++ a :: l2' }.
Proof.
intro HC. rewrite <- (app_nil_l (a::_)) in HC. apply CPermutationT_vs_elt_inv in HC as [(l1',l2') H1 ->].
rewrite app_nil_r in H1. now exists (l1', l2').
Qed.

Lemma CPermutationT_cons_cons_inv A (a b : A) l1 l2 : CPermutationT (cons a l1) (cons b l2) ->
  ((a = b) * (l1 = l2)) + {'(l1', l1'') | l1 = l1' ++ b :: l1'' & l2 = l1'' ++ a :: l1' }.
Proof.
intros [([|x l0], l0') -> Heq2]%CPermutationT_vs_cons_inv; [ left | right ]; injection Heq2 as [= -> ->].
- rewrite app_nil_r. split; reflexivity.
- exists (l0, l0'); reflexivity.
Qed.

Lemma CPermutationT_vs_elt_subst A (a : A) l l1 l2 :
  CPermutationT l (l1 ++ a :: l2) ->
  {'(l', l'') & forall l0, CPermutationT (l' ++ l0 ++ l'') (l1 ++ l0 ++ l2) & l = l' ++ a :: l'' }.
Proof.
intros [(l', l'') Heq ->]%CPermutationT_vs_elt_inv.
exists (l', l''); [ | reflexivity ].
intro l0. etransitivity; [ apply CPermutationT_app_comm | ].
list_simpl. rewrite <- Heq, app_assoc. constructor.
Qed.

Lemma CPermutationT_app_app_inv A (l1 l2 l3 l4 : list A) :
  CPermutationT (l1 ++ l2) (l3 ++ l4) ->
     {'(l1',l2',l3',l4') : _ & prod
        (prod  (CPermutationT l1 (l1' ++ l3'))
               (CPermutationT l2 (l2' ++ l4')))
        (prod  (CPermutationT l3 (l1' ++ l2'))
               (CPermutationT l4 (l3' ++ l4'))) }
   + {'(l1',l2') : _ & prod (prod
        (CPermutationT l1 (l4 ++ l1'))
        (CPermutationT l3 (l2 ++ l2')))
        (CPermutationT l1' l2') }
   + {'(l1',l2') : _ & prod (prod
        (CPermutationT l2 (l4 ++ l1'))
        (CPermutationT l3 (l1 ++ l2')))
        (CPermutationT l1' l2') }
   + {'(l1',l2') : _ & prod (prod
        (CPermutationT l1 (l3 ++ l1'))
        (CPermutationT l4 (l2 ++ l2')))
        (CPermutationT l1' l2') }
   + {'(l1',l2') : _ & prod (prod
        (CPermutationT l2 (l3 ++ l1'))
        (CPermutationT l4 (l1 ++ l2')))
        (CPermutationT l1' l2') }.
Proof.
intro HC. inversion HC as [lx ly Hx Hy].
decomp_app_eq_app Hx as [[l <- ->]|[l -> <-]];
  decomp_app_eq_app Hy as [[l' <- Hy]|[l' Hy <-]]; subst.
- left; left; left; right; exists (l ++ l', l' ++ l); repeat split;
    rewrite <- ? app_assoc; apply CPermutationT_app_rot.
- decomp_app_eq_app Hy as [[l'' <- ->]|[l'' -> <-]].
  + left; left; left; left; exists (l, l'', lx, l'); repeat split;
      apply CPermutationT_refl.
  + left; right; exists (l'' ++ lx , lx ++ l''); repeat split;
      rewrite <- ? app_assoc ; apply CPermutationT_app_rot.
- decomp_app_eq_app Hy as [[l'' <- ->]|[l'' -> <-]].
  + left; left; right; exists (ly ++ l'', l'' ++ ly); repeat split;
      rewrite <- ? app_assoc; apply CPermutationT_app_rot.
  + left; left; left; left; exists (l', ly, l'', l); repeat split;
      apply CPermutationT_refl.
- right; exists (l' ++ l, l ++ l'); repeat split;
    rewrite <- ? app_assoc; apply CPermutationT_app_rot.
Qed.

(** [rev], [in], [map], [Forall], [Exists], etc. *)
#[export] Instance CPermutationT_rev A :
  Proper (@CPermutationT A ==> @CPermutationT A) (@rev A).
Proof.
intros l; induction l; intros l' HC.
- apply CPermutationT_nil in HC; subst; apply CPermutationT_refl.
- apply CPermutationT_sym in HC.
  apply CPermutationT_vs_cons_inv in HC.
  destruct HC as [(l1 & l2) -> ->].
  now simpl; rewrite ? rev_app_distr; simpl; rewrite <- app_assoc.
Qed.

#[export] Instance CPermutationT_in A (a : A) :
  Proper (@CPermutationT A ==> Basics.impl) (In a).
Proof.
intros l l' HC Hin.
apply PermutationT_in with l; [ apply CPermutationT_PermutationT | ]; assumption.
Qed.

#[export] Instance CPermutationT_inT A (a : A) :
  Proper (@CPermutationT A ==> arrow) (InT a).
Proof.
intros l l' HC Hin.
apply PermutationT_inT with l; [ apply CPermutationT_PermutationT | ]; assumption.
Qed.

#[export] Instance CPermutationT_map A B (f : A -> B) :
  Proper (@CPermutationT A ==> @CPermutationT B) (map f).
Proof. intros l l' HC. now inversion HC; subst; rewrite ? map_app. Qed.

Lemma CPermutationT_map_inv A B (f : A -> B) l1 l2 :
  CPermutationT l1 (map f l2) -> { l & l1 = map f l & CPermutationT l2 l }.
Proof.
induction l1 as [|a l1 IHl1] in l2 |- *; intro HP.
- exists nil; [ reflexivity | ].
  destruct l2.
  + apply CPermutationT_refl.
  + apply CPermutationT_nil in HP as [=].
- apply CPermutationT_sym in HP.
  destruct (CPermutationT_vs_cons_inv HP) as [(l3, l4) -> Heq2].
  decomp_map_eq Heq2. subst l2.
  exists (a :: l4 ++ l3).
  + rewrite <- map_app. reflexivity.
  + constructor.
Qed.

#[export] Instance CPermutationT_Forall A (P : A -> Prop) :
  Proper (@CPermutationT A ==> Basics.impl) (Forall P).
Proof.
intros l1 l2 HC HF.
apply PermutationT_Forall with l1, HF.
apply CPermutationT_PermutationT, HC.
Qed.

#[export] Instance CPermutationT_Exists A (P : A -> Prop) :
  Proper (@CPermutationT A ==> Basics.impl) (Exists P).
Proof.
intros l1 l2 HC HE.
apply PermutationT_Exists with l1, HE.
apply CPermutationT_PermutationT, HC.
Qed.

#[export] Instance CPermutationT_ForallT A (P : A -> Type) :
  Proper (@CPermutationT A ==> arrow) (ForallT P).
Proof.
intros l1 l2 HC HF.
apply PermutationT_ForallT with l1, HF.
apply CPermutationT_PermutationT, HC.
Qed.

#[export] Instance CPermutationT_ExistsT A (P : A -> Type) :
  Proper (@CPermutationT A ==> arrow) (ExistsT P).
Proof.
intros l1 l2 HC HE.
apply PermutationT_ExistsT with l1, HE.
apply CPermutationT_PermutationT, HC.
Qed.

Lemma CPermutationT_Forall2T A B (P : A -> B -> Type) l1 l1' l2 :
  CPermutationT l1 l1' -> Forall2T P l1 l2 -> { l2' & CPermutationT l2 l2' & Forall2T P l1' l2' }.
Proof.
intro HP. induction HP as [lc1 lc1'] in l2 |- *; intro HF; inversion HF as [HF' | a b la lb Hab HF' Ha]; subst.
- exists nil.
  + reflexivity.
  + now symmetry in HF'; apply app_eq_nil in HF' as [-> ->].
- destruct lc1; inversion Ha; subst.
  + rewrite app_nil_l in Ha. subst.
    exists (b :: lb).
    * reflexivity.
    * rewrite app_nil_r. assumption.
  + apply Forall2T_app_inv_l in HF' as [(la', lb') [HF1 HF2] ->].
    exists (lb' ++ b :: la').
    * rewrite app_comm_cons. constructor.
    * apply Forall2T_app; [ | constructor ]; assumption.
Qed.

Lemma CPermutationT_image A B (f : A -> B) a l l' :
  CPermutationT (a :: l) (map f l') -> { a' | a = f a' }.
Proof. intro HP. apply PermutationT_image with l l', CPermutationT_PermutationT, HP. Qed.

Lemma CPermutationT_map_inv_inj A B (f : A -> B) (Hi : injective f) l1 l2 :
  CPermutationT (map f l1) (map f l2) -> CPermutationT l1 l2.
Proof.
intro HP. inversion HP as [l3 l4 Heq1 Heq2].
decomp_map_eq Heq1. decomp_map_eq Heq2 eqn:Heq. subst l1 l2.
destruct Heq as [->%(map_injective Hi) ->%(map_injective Hi)]. constructor.
Qed.

Lemma CPermutationT_map_inv_inj_local A B (f : A -> B) l1 l2 :
  (forall x y, In x l1 -> In y l2 -> f x = f y -> x = y) ->
    CPermutationT (map f l1) (map f l2) -> CPermutationT l1 l2.
Proof.
intros Hi HP. inversion HP as [l3 l4 Heq1 Heq2].
decomp_map_eq Heq1. decomp_map_eq Heq2 eqn:Heq. subst l1 l2.
destruct Heq as [Heq1%eq_sym Heq2%eq_sym].
apply map_injective_in in Heq1 as ->; [ apply map_injective_in in Heq2 as -> | ]; [ constructor | | ].
- intros x y Hin1 Hin2 Heq. apply Hi; [ apply in_or_app .. | ]; [left | right | ]; assumption.
- intros x y Hin1 Hin2 Hf. apply Hi; [ apply in_or_app .. | ]; [right | left | ]; assumption.
Qed.

Lemma CPermutationT_concat A (l1 l2 : list (list A)):
  CPermutationT l1 l2 -> CPermutationT (concat l1) (concat l2).
Proof. intro HC. induction HC. rewrite ! concat_app. constructor. Qed.

Lemma CPermutationT_flat_map A B (f : A -> list B) l1 l2:
  CPermutationT l1 l2 -> CPermutationT (flat_map f l1) (flat_map f l2).
Proof. intro HC. induction HC. rewrite ! flat_map_app. constructor. Qed.
