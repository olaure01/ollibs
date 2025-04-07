(** Add-ons for PermutationT library
Usefull properties apparently missing in the PermutationT library. *)

From Stdlib Require Import PeanoNat Permutation CMorphisms.
From OLlibs Require Import List_more funtheory.
From OLlibs Require Export PermutationT.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


(** * Additional Properties *)

#[export] Instance PermutationT_refl' A : Proper (Logic.eq ==> @PermutationT A) id.
Proof. now intros x y ->. Qed.

Lemma PermutationT_morph_transp A (P : list A -> Type) :
  (forall a b l1 l2, P (l1 ++ a :: b :: l2) -> P (l1 ++ b :: a :: l2)) ->
    Proper ((@PermutationT A) ==> arrow) P.
Proof.
assert ((forall a b l1 l2, P (l1 ++ a :: b :: l2) ->
                            P (l1 ++ b :: a :: l2)) ->
         forall l1 l2, PermutationT l1 l2 ->
         forall l0, P (l0 ++ l1) -> P (l0 ++ l2))
  as Himp.
{ intros HP l1 l2 H.
  induction H as [ | ? ? l' ? IH | | ]; auto.
  intros l0 HP'.
  rewrite <- (app_nil_l l'), app_comm_cons, app_assoc.
  now apply IH; list_simpl. }
intros HP l1 l2 H H'.
rewrite <- (app_nil_l l2); rewrite <- (app_nil_l l1) in H'.
now apply Himp with l1.
Qed.

Lemma PermutationT_elt A (a : A) l1 l2 l1' l2' :
  PermutationT (l1 ++ l2) (l1' ++ l2') ->
  PermutationT (l1 ++ a :: l2) (l1' ++ a :: l2').
Proof.
intros HP.
apply PermutationT_trans with (a :: l1 ++ l2).
- apply PermutationT_sym, PermutationT_middle.
- now apply PermutationT_cons_app.
Qed.

Lemma PermutationT_vs_elt_inv A (a : A) l l1 l2 :
  PermutationT l (l1 ++ a :: l2) -> {'(l1', l2') | l = l1' ++ a :: l2' }.
Proof.
intros HP.
remember (l1 ++ a :: l2) as l0 eqn:Heql0; revert l1 l2 Heql0;
  induction HP as [ | ? l ? ? IHP | ? a' l | ? ? ? ? IHP1 ? IHP2 ];
  intros l1 l2 Heql; destruct l1 as [| b l1];
  (try now inversion Heql); inversion Heql as [[Heq1 Heq2]]; subst.
- now exists (@nil A, l).
- destruct (IHP l1 l2 eq_refl) as [(l1', l2') ->].
  now exists (b :: l1', l2').
- now exists (a' :: nil, l).
- destruct l1 as [| c l1]; inversion Heq2; subst.
  + now exists (@nil A, b :: l2).
  + now exists (c :: b :: l1, l2).
- destruct (IHP2 nil l2 eq_refl) as [(l1', l2') ->].
  destruct (IHP1 l1' l2' eq_refl) as [(l1'', l2'') ->].
  now exists (l1'', l2'').
- destruct (IHP2 (b :: l1) l2 eq_refl) as [(l1', l2') ->].
  destruct (IHP1 l1' l2' eq_refl) as [(l1'', l2'') ->].
  now exists (l1'', l2'').
Qed.

Lemma PermutationT_vs_cons_inv A (a : A) l l1 :
  PermutationT l (a :: l1) -> {'(l1', l2') | l = l1' ++ a :: l2' }.
Proof.
intros HP; rewrite <- (app_nil_l (a :: l1)) in HP.
eapply PermutationT_vs_elt_inv; eassumption.
Qed.

Lemma PermutationT_vs_2elts A (s : A) t l1 l2 l3 :
  PermutationT (l1 ++ s :: l2 ++ t :: l3) (s :: t :: l1 ++ l2 ++ l3).
Proof.
apply PermutationT_sym, PermutationT_cons_app.
rewrite 2 app_assoc.
apply PermutationT_cons_app, PermutationT_refl.
Qed.

Lemma PermutationT_vs_2elts_inv A D (s : A) t G :
  PermutationT D (s :: t :: G) ->
  {'(D1, D2, D3) & { D = D1 ++ s :: D2 ++ t :: D3 }
                 + { D = D1 ++ t :: D2 ++ s :: D3 } }.
Proof.
intros HP; assert (HP' := HP).
apply PermutationT_vs_cons_inv in HP'.
destruct HP' as [(l1', l2') HP']; subst.
apply PermutationT_sym, PermutationT_cons_app_inv,
      PermutationT_sym, PermutationT_vs_cons_inv in HP.
destruct HP as [(l1'', l2'') HP]; symmetry in HP.
decomp_elt_eq_app HP as [[l <- ->]|[l -> <-]]; rewrite <- ? app_assoc, <- ? app_comm_cons.
- now exists (l1'', l, l2'); right.
- now exists (l1', l, l2''); left.
Qed.

Lemma PermutationT_app_rot A (l1 l2 l3 : list A) :
  PermutationT (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof. rewrite (app_assoc l2); apply PermutationT_app_comm. Qed.

Lemma PermutationT_app_swap_app A (l1 l2 l3 : list A) :
  PermutationT (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof.
rewrite ? app_assoc.
apply PermutationT_app_tail, PermutationT_app_comm.
Qed.

Lemma PermutationT_app_middle A (l l1 l2 l3 l4 : list A) :
  PermutationT (l1 ++ l2) (l3 ++ l4) ->
  PermutationT (l1 ++ l ++ l2) (l3 ++ l ++ l4).
Proof.
intros HP.
apply PermutationT_trans with (l ++ l1 ++ l2); [ apply PermutationT_app_swap_app | ].
apply PermutationT_trans with (l ++ l3 ++ l4); [ now apply PermutationT_app_head | ].
apply PermutationT_app_swap_app.
Qed.

Lemma PermutationT_app_middle_inv A (l l1 l2 l3 l4 : list A) :
  PermutationT (l1 ++ l ++ l2) (l3 ++ l ++ l4) ->
  PermutationT (l1 ++ l2) (l3 ++ l4).
Proof.
intros HP.
apply (PermutationT_app_inv_l l).
apply PermutationT_trans with (l1 ++ l ++ l2); [ apply PermutationT_app_swap_app | ].
apply PermutationT_trans with (l3 ++ l ++ l4); [ assumption | ].
apply PermutationT_app_swap_app.
Qed.

Lemma PermutationT_vs_elt_subst A (a : A) l l1 l2 :
  PermutationT l (l1 ++ a :: l2) ->
  {'(l3, l4) & forall l0, PermutationT (l1 ++ l0 ++ l2) (l3 ++ l0 ++ l4) & l = l3 ++ a :: l4 }.
Proof.
intros HP.
destruct (PermutationT_vs_elt_inv _ _ _ HP) as [(l', l'') ->].
exists (l', l''); [ | reflexivity ].
intros l0.
apply PermutationT_app_inv, (PermutationT_app_middle l0) in HP.
symmetry; assumption.
Qed.

Lemma PermutationT_app_app_inv A (l1 l2 l3 l4 : list A) :
  PermutationT (l1 ++ l2) (l3 ++ l4) -> {'(l1', l2', l3', l4') & prod (prod
    (PermutationT l1 (l1' ++ l3'))
    (PermutationT l2 (l2' ++ l4'))) (prod
    (PermutationT l3 (l1' ++ l2'))
    (PermutationT l4 (l3' ++ l4'))) }.
Proof.
revert l2 l3 l4; induction l1 as [|a l1 IHl1]; intros l2 l3 l4 HP.
- now exists (@nil A, l3, @nil A, l4); repeat split; try apply PermutationT_refl.
- assert (Heq := HP).
  apply PermutationT_sym, PermutationT_vs_cons_inv in Heq.
  destruct Heq as [(l1', l2') Heq].
  decomp_elt_eq_app Heq; subst.
  + rewrite <- ?app_comm_cons, <- app_assoc, <- app_comm_cons in HP.
    apply PermutationT_cons_app_inv in HP.
    rewrite app_assoc in HP; apply IHl1 in HP.
    destruct HP as [[[[l1'' l2''] l3''] l4''] [[H1 H2] [H3 H4]]].
    exists (a :: l1'', l2'', l3'', l4''); simpl; repeat split; auto.
    now apply PermutationT_sym, PermutationT_cons_app, PermutationT_sym.
  + rewrite <- ?app_comm_cons, app_assoc in HP.
    apply PermutationT_cons_app_inv in HP.
    rewrite <- app_assoc in HP; apply IHl1 in HP.
    destruct HP as [[[[l1'' l2''] l3''] l4''] [[H1 H2] [H3 H4]]].
    exists (l1'', l2'', a :: l3'', l4''); simpl; repeat split; auto.
    * now apply PermutationT_cons_app.
    * now apply PermutationT_sym, PermutationT_cons_app, PermutationT_sym.
Qed.

#[export] Instance PermutationT_Forall A (P : A -> Prop) :
  Proper ((@PermutationT A) ==> Basics.impl) (Forall P).
Proof.
intros l1 l2 H.
apply PermutationT_Permutation in H.
rewrite H; reflexivity.
Qed.

#[export] Instance PermutationT_Exists A (P : A -> Prop) :
  Proper ((@PermutationT A) ==> Basics.impl) (Exists P).
Proof.
intros l1 l2 H.
apply PermutationT_Permutation in H.
rewrite H; reflexivity.
Qed.

#[export] Instance PermutationT_ForallT A (P : A -> Type) :
  Proper ((@PermutationT A) ==> arrow) (ForallT P).
Proof.
intros l1 l2 HP.
induction HP as [ | ? ? ? ? IHP | | ]; intro HF0; auto.
- inversion_clear HF0 as [|? ? Hx HF].
  now apply IHP in HF; constructor.
- inversion_clear HF0 as [|? ? Hx HF]; inversion HF.
  now repeat constructor.
Qed.

#[export] Instance PermutationT_ExistsT A (P : A -> Type) :
  Proper ((@PermutationT A) ==> arrow) (ExistsT P).
Proof.
intros l1 l2 HP.
induction HP as [ | ? ? ? ? IHP | | ]; intro HE0; auto.
- inversion_clear HE0 as [ | ? ? HE ].
  + now apply ExistsT_cons_hd.
  + apply IHP in HE.
    now apply ExistsT_cons_tl.
- inversion_clear HE0 as [ | ? ? HE ]; [ | inversion_clear HE ].
  + now apply ExistsT_cons_tl, ExistsT_cons_hd.
  + now apply ExistsT_cons_hd.
  + now apply ExistsT_cons_tl, ExistsT_cons_tl.
Qed.

Lemma PermutationT_Forall2T A B (P : A -> B -> Type) l1 l1' l2 :
  PermutationT l1 l1' -> Forall2T P l1 l2 ->
  { l2' & PermutationT l2 l2' & Forall2T P l1' l2' }.
Proof.
intros HP; revert l2; induction HP as [ | ? ? ? ? IHP | | ? ? ? HP1 IHP1 HP2 IHP2 ];
  intros l2 HF; inversion HF as [| ? y' ? ? ? HF0]; subst.
- exists nil; auto.
- apply IHP in HF0 as [l2' HP2 HF2].
  exists (y' :: l2'); auto.
- inversion HF0 as [|? y'0 ? l'0]; subst.
  exists (y'0 :: y' :: l'0); auto.
  constructor.
- apply PermutationT_nil in HP1 as ->.
  apply PermutationT_nil in HP2 as ->.
  exists nil; auto.
- apply IHP1 in HF as [l2' HP2' HF2'].
  apply IHP2 in HF2' as [l2'' HP2'' HF2''].
  exists l2''; auto.
  transitivity l2'; assumption.
Qed.

Lemma PermutationT_map_inv A B (f : A -> B) l1 l2 :
  PermutationT l1 (map f l2) -> { l & l1 = map f l & PermutationT l2 l }.
Proof.
induction l1 as [|a l1 IHl1] in l2 |- *; intro HP.
- apply PermutationT_nil in HP.
  destruct l2; inversion HP.
  now exists nil.
- apply PermutationT_sym in HP.
  destruct (PermutationT_vs_cons_inv HP) as [(l1', l2') Heq].
  decomp_map Heq. subst l2.
  apply PermutationT_sym in HP.
  rewrite map_app in HP.
  apply PermutationT_cons_app_inv in HP.
  specialize IHl1 with (l1' ++ l2').
  rewrite map_app in IHl1.
  apply IHl1 in HP as [l' -> HP'].
  exists (a :: l'); [ reflexivity | ].
  apply PermutationT_sym, PermutationT_cons_app, PermutationT_sym, HP'.
Qed.

Lemma PermutationT_map_inv_inj A B (f : A -> B) (Hinj : injective f) l1 l2 :
  PermutationT (map f l1) (map f l2) -> PermutationT l1 l2.
Proof.
revert l2; induction l1 as [|a l1 IHl1]; intros l2 HP.
- apply PermutationT_nil in HP.
  destruct l2; inversion HP.
  apply PermutationT_refl.
- assert (Heq := HP).
  apply PermutationT_sym in Heq.
  apply PermutationT_vs_cons_inv in Heq as [(l3, l4) Heq].
  decomp_map Heq eqn:Hf. subst l2.
  rewrite map_app in HP. cbn in HP. rewrite Hf in HP.
  apply PermutationT_cons_app_inv in HP.
  specialize IHl1 with (l3 ++ l4).
  rewrite map_app in IHl1.
  apply IHl1 in HP.
  apply Hinj in Hf as ->.
  apply PermutationT_cons_app, HP.
Qed.

Lemma PermutationT_image A B (f : A -> B) a l l' :
  PermutationT (a :: l) (map f l') -> { a' | a = f a' }.
Proof.
intros HP; apply PermutationT_map_inv in HP.
destruct HP as [l'' Heq _].
destruct l'' as [ |b l'']; inversion Heq.
now exists b.
Qed.

Lemma PermutationT_elt_map_inv A B (f : A -> B) a l1 l2 l3 l4 :
  PermutationT (l1 ++ a :: l2) (l3 ++ map f l4) ->
  (forall b, a <> f b) -> {'(l1', l2') | l3 = l1' ++ a :: l2' }.
Proof.
intros HP Hf.
apply PermutationT_sym, PermutationT_vs_elt_inv in HP as [(l', l'') Heq].
decomp_elt_eq_app Heq as [[l''' <- ->]|[? -> Heq]].
- exists (l', l'''). reflexivity.
- exfalso.
  decomp_map Heq.
  exact (Hf a eq_refl).
Qed.

#[export] Instance PermutationT_concat A :
  Proper ((@PermutationT (list A)) ==> (@PermutationT A)) (@concat A).
Proof.
intros l1 l2 HP. induction HP; cbn.
- reflexivity.
- apply PermutationT_app_head. assumption.
- rewrite ! app_assoc. apply PermutationT_app_tail, PermutationT_app_swap.
- etransitivity; eassumption.
Qed.

#[export] Instance PermutationT_flat_map A B f :
  Proper ((@PermutationT A) ==> (@PermutationT B)) (flat_map f).
Proof.
intros l1 l2 HP. rewrite ! flat_map_concat_map. apply PermutationT_concat, PermutationT_map, HP.
Qed.

#[export] Instance list_sum_permT : Proper (@PermutationT nat ==> eq) list_sum.
Proof.
intros l1; induction l1 as [|a l1 IHl1]; intros l2 HP.
- now apply PermutationT_nil in HP; subst.
- assert (HP' := HP).
  apply PermutationT_sym, PermutationT_vs_cons_inv in HP'.
  destruct HP' as [(l3, l4) ->].
  apply PermutationT_cons_app_inv in HP.
  simpl; erewrite IHl1; [ | apply HP ].
  rewrite 2 list_sum_app; simpl.
  now rewrite 2 (Nat.add_comm a), Nat.add_assoc.
Qed.


(** * Permutation definition based on transpositions for induction with fixed length *)
Inductive PermutationT_transp A : crelation (list A) :=
| PermutationT_t_refl l : PermutationT_transp l l
| PermutationT_t_swap x y l1 l2 : PermutationT_transp (l1 ++ y :: x :: l2) (l1 ++ x :: y :: l2)
| PermutationT_t_trans l l' l'' :
    PermutationT_transp l l' -> PermutationT_transp l' l'' -> PermutationT_transp l l''.

#[export] Instance PermutationT_transp_sym A : Symmetric (@PermutationT_transp A).
Proof.
intros l1 l2 HC; induction HC; subst; try (now constructor).
eapply PermutationT_t_trans ; eassumption.
Qed.

#[export] Instance PermutationT_transp_equiv A : Equivalence (@PermutationT_transp A).
Proof. split.
- intros l; apply PermutationT_t_refl.
- apply PermutationT_transp_sym.
- intros l1 l2 l3; apply PermutationT_t_trans.
Qed.

Lemma PermutationT_transp_cons A (x : A) l1 l2 :
  PermutationT_transp l1 l2 -> PermutationT_transp (x :: l1) (x :: l2).
Proof.
intros HP; induction HP; try reflexivity.
- rewrite 2 app_comm_cons; apply PermutationT_t_swap.
- etransitivity; eassumption.
Qed.

Lemma permT_perm_tT A (l1 l2 : list A) :
  PermutationT l1 l2 -> PermutationT_transp l1 l2.
Proof.
intros HP; induction HP as [ | |x y | ? l' ].
- constructor.
- now apply PermutationT_transp_cons.
- rewrite <- (app_nil_l (y :: _)), <- (app_nil_l (x :: y :: _)).
  now apply PermutationT_t_swap.
- now transitivity l'.
Qed.

Lemma perm_tT_permT A (l1 l2 : list A) :
  PermutationT_transp l1 l2 -> PermutationT l1 l2.
Proof.
intros HP; induction HP as [ | | ? l' ]; auto.
- now apply PermutationT_app_head, PermutationT_swap.
- now transitivity l'.
Qed.

Lemma PermutationT_ind_transp A (P : list A -> list A -> Prop) :
  (forall l, P l l) ->
  (forall x y l1 l2, P (l1 ++ y :: x :: l2) (l1 ++ x :: y :: l2)) ->
  (forall l l' l'',
     PermutationT l l' -> P l l' -> PermutationT l' l'' -> P l' l'' -> P l l'') ->
  forall l1 l2, PermutationT l1 l2 -> P l1 l2.
Proof.
intros Hr Ht Htr l1 l2 HP%permT_perm_tT.
induction HP as [ | | ? l' ] in Hr, Ht, Htr |- *; auto.
apply (Htr _ l'); auto; now apply perm_tT_permT.
Qed.

Lemma PermutationT_rect_transp A (P : crelation (list A)) :
  (forall l, P l l) ->
  (forall x y l1 l2, P (l1 ++ y :: x :: l2) (l1 ++ x :: y :: l2)) ->
  (forall l l' l'',
     PermutationT l l' -> P l l' -> PermutationT l' l'' -> P l' l'' -> P l l'') ->
  forall l1 l2, PermutationT l1 l2 -> P l1 l2.
Proof.
intros Hr Ht Htr l1 l2 HP%permT_perm_tT.
induction HP as [ | | ? l' ] in Hr, Ht, Htr |- *; auto.
apply (Htr _ l'); auto; now apply perm_tT_permT.
Qed.


Lemma PermutationT_list_sum l1 l2 :
  PermutationT l1 l2 -> list_sum l1 = list_sum l2.
Proof.
unfold list_sum. intros HP. induction HP; simpl; [ auto | auto | | ].
- apply Nat.add_shuffle3.
- etransitivity; eassumption.
Qed.

Lemma PermutationT_list_max l1 l2 :
  PermutationT l1 l2 -> list_max l1 = list_max l2.
Proof.
unfold list_max. intro HP.
induction HP as [ | ? ? ? ? IHHP | x y | ? l' ]; cbn; [ reflexivity | rewrite IHHP; reflexivity | | ].
- rewrite ? Nat.max_assoc, (Nat.max_comm x y). reflexivity.
- transitivity (fold_right Init.Nat.max 0 l'); assumption.
Qed.

Lemma PermutationT_forallb A P (l1 l2 : list A) :
  PermutationT l1 l2 -> forallb P l1 = forallb P l2.
Proof.
intro HP. induction HP as [ | | x y l | l1 l2 l3 HP1 IHP1 HP2 IHP2 ].
- reflexivity.
- cbn. f_equal. assumption.
- cbn. rewrite ! Bool.andb_assoc, (Bool.andb_comm (P y)). reflexivity.
- transitivity (forallb P l2); assumption.
Qed.

Lemma partition_PermutationT A f (l l1 l2 : list A) :
  partition f l = (l1, l2) -> PermutationT l (l1 ++ l2).
Proof.
induction l as [|a l IHl] in l1, l2 |- *; cbn; intros Hp.
- injection Hp as [= <- <-]. reflexivity.
- destruct (partition f l), (f a); injection Hp as [= <- <-].
  + apply PermutationT_cons, IHl; reflexivity.
  + apply PermutationT_cons_app, IHl. reflexivity.
Qed.

Lemma PermutationT_partition A f (l l' l1 l2 l1' l2' : list A) :
  PermutationT l l' -> partition f l = (l1, l2) -> partition f l' = (l1', l2') ->
  PermutationT l1 l1' * PermutationT l2 l2'.
Proof.
intro HP. induction HP as [ | x l l' HP IHHP | x y l
                           | l l' l'' HP1 IHHP1 HP2 IHHP2 ] in l1, l2, l1', l2' |- *;
  cbn; intros Hp1 Hp2.
- injection Hp1 as [= <- <-]. injection Hp2 as [= <- <-]. split; reflexivity.
- destruct (partition f l) as [l3 l4], (partition f l') as [l3' l4'], (f x);
    injection Hp1 as [= <- <-]; injection Hp2 as [= <- <-];
    destruct (IHHP l3 l4 l3' l4' eq_refl eq_refl); split; now try apply PermutationT_cons.
- destruct (partition f l) as [l3 l4], (f x), (f y);
    injection Hp1 as [= <- <-]; injection Hp2 as [= <- <-]; split; (reflexivity + apply PermutationT_swap).
- destruct (partition f l) as [l3 l4], (partition f l') as [l3' l4'],
           (partition f l'') as [l3'' l4''];
     injection Hp1 as [= <- <-]; injection Hp2 as [= <- <-];
     destruct (IHHP1 l3 l4 l3' l4' eq_refl eq_refl);
     destruct (IHHP2 l3' l4' l3'' l4'' eq_refl eq_refl); split; etransitivity; eassumption.
Qed.

Lemma PermutationT_incl A (l1 l2 l0 : list A) : PermutationT l1 l2 -> incl l1 l0 -> incl l2 l0.
Proof. intros HP Hincl x Hin. symmetry in HP. apply Hincl, (PermutationT_in x HP Hin). Qed.

Lemma PermutationT_repeat A (x : A) n l : PermutationT l (repeat x n) -> l = repeat x n.
Proof. intros Heq%PermutationT_Permutation%Permutation_repeat. exact Heq. Qed.
