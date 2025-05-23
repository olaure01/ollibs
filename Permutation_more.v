(** Add-ons for Permutation library
Usefull properties apparently missing in the Permutation library. *)

From Stdlib Require Export Permutation List.
From OLlibs Require Import List_more funtheory.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


Lemma Permutation_app_app_inv A (l1 l2 l3 l4 : list A) :
  Permutation (l1 ++ l2) (l3 ++ l4) -> exists l3' l3'' l4' l4'',
    Permutation l1 (l3' ++ l4')  /\ Permutation l2 (l3'' ++ l4'') /\
    Permutation l3 (l3' ++ l3'') /\ Permutation l4 (l4' ++ l4'').
Proof.
revert l2 l3 l4; induction l1 as [|a l1 IHl1]; intros l2 l3 l4 HP.
- exists (@nil A), l3, (@nil A), l4.
  now repeat split.
- assert (Heq := HP).
  apply (Permutation_in a) in Heq.
  + apply in_app_or in Heq.
    destruct Heq as [Heq | Heq]; apply in_split in Heq;
    destruct Heq as (l' & l'' & Heq); subst.
    * rewrite <- ?app_comm_cons in HP.
      rewrite <- app_assoc, <- app_comm_cons in HP.
      apply Permutation_cons_app_inv in HP.
      rewrite app_assoc in HP.
      apply IHl1 in HP.
      destruct HP as (l3' & l3'' & l4' & l4'' & H1 & H2 & H3 & H4).
      exists (a::l3'), l3'', l4', l4''.
      repeat split; auto.
      -- rewrite <- app_comm_cons.
         now apply Permutation_cons.
      -- apply Permutation_sym.
         rewrite <- app_comm_cons.
         now apply Permutation_cons_app, Permutation_sym.
    * rewrite <- ?app_comm_cons, app_assoc in HP.
      apply Permutation_cons_app_inv in HP.
      rewrite <- app_assoc in HP.
      apply IHl1 in HP.
      destruct HP as (l3' & l3'' & l4' & l4'' & H1 & H2 & H3 & H4).
      exists l3', l3'', (a :: l4'), l4''.
      repeat split; auto.
      -- now apply Permutation_cons_app.
      -- apply Permutation_sym.
         rewrite <- app_comm_cons.
         now apply Permutation_cons_app, Permutation_sym.
  + now constructor.
Qed.

Lemma Permutation_vs_elt_inv_perm A l l1 l2 (a : A) :
  Permutation l (l1 ++ a :: l2) -> exists l' l'', Permutation (l' ++ l'') (l1 ++ l2) /\ l = l' ++ a :: l''.
Proof.
intro HP. destruct (Permutation_vs_elt_inv _ _ _ HP) as [l' [l'' ->]].
exists l', l''; split; [ | reflexivity ].
apply (Permutation_app_inv _ _ _ _ _ HP).
Qed.

Lemma Permutation_vs_elt_subst A (a : A) l l1 l2 :
  Permutation l (l1 ++ a :: l2) -> exists l' l'',
    (forall l0, Permutation (l' ++ l0 ++ l'') (l1 ++ l0 ++ l2)) /\ l = l' ++ a :: l''.
Proof.
intros [l' [l'' [HP ->]]]%Permutation_vs_elt_inv_perm.
exists l', l''; split; [ | reflexivity ].
intro l0. apply (Permutation_app_middle l0 _ _ _ _ HP).
Qed.

Lemma Permutation_map_inv_inj A B (f : A -> B) (Hinj : injective f) l1 l2 :
  Permutation (map f l1) (map f l2) -> Permutation l1 l2.
Proof.
induction l1 as [|a l1 IHl1] in l2 |- *; intro HP.
- apply Permutation_nil, map_eq_nil in HP as ->. constructor.
- symmetry in HP.
  destruct (Permutation_vs_cons_inv HP) as [l3 [l4 Heq]].
  decomp_map_eq Heq eqn:Hf. subst l2.
  rewrite map_app in HP. cbn in HP. rewrite Hf in HP.
  symmetry in HP. apply Permutation_cons_app_inv in HP.
  specialize IHl1 with (l3 ++ l4).
  rewrite map_app in IHl1.
  apply IHl1 in HP.
  apply Hinj in Hf as ->.
  apply Permutation_cons_app, HP.
Qed.

Lemma Permutation_map_inv_inj_local A B (f : A -> B) l1 l2 :
  (forall x y, In x l1 -> In y l2 -> f x = f y -> x = y) ->
    Permutation (map f l1) (map f l2) -> Permutation l1 l2.
Proof.
induction l1 as [|a l1 IHl1] in l2 |- *; intros Hi HP.
- apply Permutation_nil, map_eq_nil in HP as ->. constructor.
- assert (Heq := HP). symmetry in Heq.
  apply Permutation_vs_cons_inv in Heq as [l3 [l4 Heq]].
  decomp_map_eq Heq eqn:Hf. subst l2.
  rewrite map_app in HP. cbn in HP. rewrite Hf in HP.
  apply Permutation_cons_app_inv in HP.
  specialize IHl1 with (l3 ++ l4).
  rewrite map_app in IHl1.
  apply IHl1 in HP.
  + symmetry in Hf. apply Hi in Hf as ->.
    * apply Permutation_cons_app, HP.
    * apply in_eq.
    * apply in_elt.
  + intros x' y' Hx' Hy' Hf'. apply Hi, Hf'.
    * apply in_cons, Hx'.
    * apply in_or_app. apply in_app_or in Hy' as []; [left|right; apply in_cons]; assumption.
Qed.

Lemma Permutation_forallb A P (l1 l2 : list A) : Permutation l1 l2 -> forallb P l1 = forallb P l2.
Proof.
intro HP. induction HP as [ | | x y l | l1 l2 l3 HP1 IHP1 HP2 IHP2 ].
- reflexivity.
- cbn. f_equal. assumption.
- cbn. rewrite ! Bool.andb_assoc, (Bool.andb_comm (P y)). reflexivity.
- transitivity (forallb P l2); assumption.
Qed.

Lemma partition_Permutation A f (l l1 l2 : list A) : partition f l = (l1, l2) -> Permutation l (l1 ++ l2).
Proof.
induction l as [|a l IHl] in l1, l2 |- *; cbn; intros Hp.
- injection Hp as [= <- <-]. reflexivity.
- destruct (partition f l), (f a); injection Hp as [= <- <-].
  + apply Permutation_cons, IHl; reflexivity.
  + apply Permutation_cons_app, IHl. reflexivity.
Qed.

Lemma Permutation_partition A f (l l' l1 l2 l1' l2' : list A) :
  Permutation l l' -> partition f l = (l1, l2) -> partition f l' = (l1', l2') ->
  Permutation l1 l1' /\ Permutation l2 l2'.
Proof.
intros HP; induction HP as [ | x l l' HP IHHP | x y l
                           | l l' l'' HP1 IHHP1 HP2 IHHP2 ] in l1, l2, l1', l2' |- *;
  cbn; intros Hp1 Hp2.
- injection Hp1 as [= <- <-]. injection Hp2 as [= <- <-]. split; reflexivity.
- destruct (partition f l) as [l3 l4], (partition f l') as [l3' l4'], (f x);
    injection Hp1 as [= <- <-]; injection Hp2 as [= <- <-];
    destruct (IHHP l3 l4 l3' l4' eq_refl eq_refl); split; now try apply Permutation_cons.
- destruct (partition f l) as [l3 l4], (f x), (f y);
    injection Hp1 as [= <- <-]; injection Hp2 as [= <- <-]; split; (reflexivity + apply perm_swap).
- destruct (partition f l) as [l3 l4], (partition f l') as [l3' l4'],
           (partition f l'') as [l3'' l4''];
     injection Hp1 as [= <- <-]; injection Hp2 as [= <- <-];
     destruct (IHHP1 l3 l4 l3' l4' eq_refl eq_refl);
     destruct (IHHP2 l3' l4' l3'' l4'' eq_refl eq_refl); split; etransitivity; eassumption.
Qed.

Lemma Permutation_concat A (l1 l2 : list (list A)):
  Permutation l1 l2 -> Permutation (concat l1) (concat l2).
Proof.
intro HP. induction HP; cbn.
- reflexivity.
- apply Permutation_app_head. assumption.
- rewrite ! app_assoc. apply Permutation_app_tail, Permutation_app_swap.
- etransitivity; eassumption.
Qed.
(* simpler proof of [Permutation_flat_map] using [Permutation_concat]:
Proof. intros l1 l2 HP. rewrite ! flat_map_concat_map. apply Permutation_concat, Permutation_map, HP. Qed.
*)

Lemma Permutation_incl A (l1 l2 l0 : list A) : Permutation l1 l2 -> incl l1 l0 -> incl l2 l0.
Proof. intros HP Hincl x Hin. symmetry in HP. apply Hincl, (Permutation_in x HP Hin). Qed.
