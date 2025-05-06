From Stdlib Require Import List Permutation.
From OLlibs Require Import List_more SubList.
Import ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.

Inductive shuffle (A : Type) : list A -> list A -> list A -> Prop :=
| shuffle_nil : shuffle nil nil nil
| shuffle_l a l1 l2 l3 : shuffle l1 l2 l3 -> shuffle (a :: l1) l2 (a :: l3)
| shuffle_r a l1 l2 l3 : shuffle l1 l2 l3 -> shuffle l1 (a :: l2) (a :: l3).

Lemma shuffle_nil_l A (l2 l3 : list A) : shuffle nil l2 l3 -> l2 = l3.
Proof.
intro s. induction l2 as [|a l2 IHl2] in l3, s |- *; inversion s.
- reflexivity.
- subst. f_equal. apply IHl2. assumption.
Qed.

Lemma shuffle_nil_r A (l1 l3 : list A) : shuffle l1 nil l3 -> l1 = l3.
Proof.
intro s. induction l1 as [|a l1 IHl1] in l3, s |- *; inversion s.
- reflexivity.
- subst. f_equal. apply IHl1. assumption.
Qed.

Lemma shuffle_nil_id A (l : list A) : shuffle nil l l.
Proof. now induction l as [|a l IH]; constructor. Qed.

Lemma shuffle_id_nil A (l : list A) : shuffle l nil l.
Proof. now induction l as [|a l IH]; constructor. Qed.

Lemma shuffle_comm A (l1 l2 l3 : list A) : shuffle l1 l2 l3 -> shuffle l2 l1 l3.
Proof. intro s. induction s; constructor; assumption. Qed.

Lemma shuffle_assoc_r A (l1 l2 l3 l' l : list A) :
  shuffle l1 l2 l' -> shuffle l' l3 l -> exists l'', shuffle l1 l'' l /\ shuffle l2 l3 l''.
Proof.
intro s. induction s as [ | a l1' l2' l3' s IHs | a l1' l2' l3' s IHs ] in l3, l |- *; intro s'.
- exists l3; split; [ assumption | apply shuffle_nil_id ].
- induction l3 as [|x l3 IHl] in l, s' |- *.
  + inversion s' as [ | ? ? ? ? s'' | ]. subst.
    apply IHs in s'' as [l'' [s'1 s'2]].
    exists l''; split; [ constructor | ]; assumption.
  + inversion s' as [ | ? ? ? ? s'' | ? ? ? ? s'' ]; subst.
    * apply IHs in s'' as [l'' [s'1 s'2]].
      exists l''; split; [ constructor | ]; assumption.
    * apply IHl in s'' as [l'' [s'1 s'2]].
      exists (x :: l''); split; constructor; assumption.
- induction l3 as [|x l3 IHl] in l, s' |- *.
  + inversion s' as [ | ? ? ? ? s'' | ]. subst.
    apply IHs in s'' as [l'' [s'1 s'2]].
    exists (a :: l''); split; constructor; assumption.
  + inversion s' as [ | ? ? ? ? s'' | ? ? ? ? s'' ]; subst.
    * apply IHs in s'' as [l'' [s'1 s'2]].
      exists (a :: l''); split; constructor; assumption.
    * apply IHl in s'' as [l'' [s'1 s'2]].
      exists (x :: l''); split; constructor; assumption.
Qed.

Lemma shuffle_assoc_l A (l1 l2 l3 l' l : list A) :
  shuffle l1 l' l -> shuffle l2 l3 l' -> exists l'', shuffle l1 l2 l'' /\ shuffle l'' l3 l.
Proof.
intros s1%shuffle_comm s2%shuffle_comm.
destruct (shuffle_assoc_r s2 s1) as [l'' [s1'%shuffle_comm s2'%shuffle_comm]].
exists l''; split; assumption.
Qed.

Lemma shuffle_app A (l1 l2 : list A) : shuffle l1 l2 (l1 ++ l2).
Proof.
induction l1 as [|a l1 IH].
- apply shuffle_nil_id.
- cbn. constructor. exact IH.
Qed.

Lemma shuffle_app_swap A (l1 l2 : list A) : shuffle l1 l2 (l2 ++ l1).
Proof. apply shuffle_comm, shuffle_app. Qed.

Lemma shuffle_app_app A (l1 l2 l3 l1' l2' l3' : list A) : shuffle l1 l2 l3 -> shuffle l1' l2' l3' ->
  shuffle (l1 ++ l1') (l2 ++ l2') (l3 ++ l3').
Proof.
intro s1. induction s1 as [ | x l' l'' l''' s1 IHs1 | x l' l'' l''' s1 IHs1 ];
  intro s2; [ assumption | cbn; constructor; apply IHs1, s2 .. ].
Qed.

Lemma shuffle_app_app_l_l A (l0 l1 l2 l3 : list A) : shuffle l1 l2 l3 -> shuffle (l0 ++ l1) l2 (l0 ++ l3).
Proof. rewrite <- (app_nil_l l2). apply shuffle_app_app, shuffle_id_nil. Qed.

Lemma shuffle_app_app_l_r A (l0 l1 l2 l3 : list A) : shuffle l1 l2 l3 -> shuffle (l1 ++ l0) l2 (l3 ++ l0).
Proof. rewrite <- (app_nil_r l2) at 2. intro s. apply (shuffle_app_app s), shuffle_id_nil. Qed.

Lemma shuffle_app_app_r_l A (l0 l1 l2 l3 : list A) : shuffle l1 l2 l3 -> shuffle l1 (l0 ++ l2) (l0 ++ l3).
Proof. rewrite <- (app_nil_l l1). apply shuffle_app_app, shuffle_nil_id. Qed.

Lemma shuffle_app_app_r_r A (l0 l1 l2 l3 : list A) : shuffle l1 l2 l3 -> shuffle l1 (l2 ++ l0) (l3 ++ l0).
Proof. rewrite <- (app_nil_r l1) at 2. intro s. apply (shuffle_app_app s), shuffle_nil_id. Qed.

Lemma shuffle_elt_l A (a : A) l1' l1'' l2 l3 : shuffle (l1' ++ a :: l1'') l2 l3 ->
  exists l3' l3'', l3 = l3' ++ a :: l3''.
Proof.
intro s. remember (l1' ++ a :: l1'') as l1 eqn:Heql1.
induction s as [ | x l' l'' l''' s IHs | x l' l'' l''' s IHs ] in l1', l1'', Heql1 |- *.
- apply app_cons_not_nil in Heql1 as [].
- destruct l1' as [|b l1']; cbn in Heql1; injection Heql1 as [= -> ->].
  + exists nil, l'''. reflexivity.
  + destruct (IHs _ _ eq_refl) as [l3' [l3'' ->]].
    exists (b :: l3'), l3''. reflexivity.
- destruct (IHs _ _ Heql1) as [l3' [l3'' ->]].
  exists (x :: l3'), l3''. reflexivity.
Qed.

Lemma shuffle_elt_r A (a : A) l1 l2' l2'' l3 : shuffle l1 (l2' ++ a :: l2'') l3 ->
  exists l3' l3'', l3 = l3' ++ a :: l3''.
Proof. intros s%shuffle_comm. exact (shuffle_elt_l _ _ _ s). Qed.

Lemma shuffle_add_elt_l A (a : A) l1 l2 l3' l3'' : shuffle l1 l2 (l3' ++ l3'') ->
  exists l1' l1'', l1 = l1' ++ l1'' /\ shuffle (l1' ++ a :: l1'') l2 (l3' ++ a :: l3'').
Proof.
intro s. remember (l3' ++ l3'') as l3 eqn:Heq3.
induction s as [ | x l' l'' l''' s IHs | x l' l'' l''' s IHs ] in l3', l3'', Heq3 |- *.
- symmetry in Heq3. apply app_eq_nil in Heq3 as [-> ->].
  exists nil, nil. repeat constructor.
- destruct l3' as [|b l3'].
  + cbn in Heq3. subst.
    destruct (IHs nil l''' eq_refl) as [l1' [l1'' [-> s']]]. cbn in s'.
    exists nil, (x :: l1' ++ l1''); auto.
    cbn. split; constructor. constructor. assumption.
  + cbn in Heq3. injection Heq3 as [= <- ->].
    destruct (IHs l3' l3'' eq_refl) as [l1' [l1'' [-> s']]].
    exists (x :: l1'), l1''; auto.
    cbn. split; constructor. assumption.
- destruct l3' as [|b l3'].
  + cbn in Heq3. subst.
    destruct (IHs nil l''' eq_refl) as [l1' [l1'' [-> s']]]. cbn in s'.
    exists nil, (l1' ++ l1''); auto.
    cbn. split; constructor. constructor. assumption.
  + cbn in Heq3. injection Heq3 as [= <- ->].
    destruct (IHs l3' l3'' eq_refl) as [l1' [l1'' [-> s']]].
    exists l1', l1''; auto.
    cbn. split; constructor. assumption.
Qed.

Lemma shuffle_add_elt_r A (a : A) l1 l2 l3' l3'' : shuffle l1 l2 (l3' ++ l3'') ->
  exists l2' l2'', l2 = l2' ++ l2'' /\ shuffle l1 (l2' ++ a :: l2'') (l3' ++ a :: l3'').
Proof.
intros [l2' [l2'' [-> s%shuffle_comm]]]%shuffle_comm%(shuffle_add_elt_l a).
now exists l2', l2''.
Qed.

Lemma shuffle_nil_inv A (l1 l2 : list A) : shuffle l1 l2 nil -> l1 = nil /\ l2 = nil.
Proof. intro s. inversion s. split; reflexivity. Qed.

Lemma shuffle_length_1_inv A (a : A) l1 l2 :
  shuffle l1 l2 [a] -> (l1 = [a] /\ l2 = nil) \/ (l1 = nil /\ l2  = [a]).
Proof.
intro s. inversion s as [ | b l1' l2' l3' s' | b l1' l2' l3' s' ]; subst;
  apply shuffle_nil_inv in s' as [-> ->]; [left | right]; repeat split.
Qed.

Lemma shuffle_length_2_inv A (a b : A) l1 l2 : shuffle l1 l2 [a; b] ->
  (l1 = [a; b] /\ l2 = nil) \/ (l1 = [a] /\ l2 = [b]) \/ (l1 = [b] /\ l2 = [a]) \/ (l1 = nil /\ l2  = [a; b]).
Proof.
intro s. inversion s as [ | c l1' l2' l3' s' | c l1' l2' l3' s' ]; subst;
  apply shuffle_length_1_inv in s' as [[-> ->] | [-> ->]];
  [left | right; left | right; right; left | right; right; right]; repeat split.
Qed.

Lemma shuffle_app_inv A (l1 l2 l3' l3'' : list A) :
  shuffle l1 l2 (l3' ++ l3'') -> exists l1' l1'' l2' l2'',
                                     l1 = l1' ++ l1'' /\ l2 = l2' ++ l2''
                                  /\ shuffle l1' l2' l3' /\ shuffle l1'' l2'' l3''.
Proof.
intro s. remember (l3' ++ l3'') as l3 eqn:Heq3.
induction s as [ | x l' l'' l''' s IHs | x l' l'' l''' s IHs ] in l3', l3'', Heq3 |- *.
- symmetry in Heq3. apply app_eq_nil in Heq3 as [-> ->].
  exists nil, nil, nil, nil; repeat constructor.
- destruct l3' as [|b l3'].
  + cbn in Heq3. subst.
    destruct (IHs nil l''' eq_refl) as [l1' [l1'' [l2' [l2'' [-> [-> [[-> ->]%shuffle_nil_inv s2]]]]]]].
    exists nil, (x :: l1''), nil, l2''; auto.
    repeat constructor. assumption.
  + cbn in Heq3. injection Heq3 as [= <- ->].
    destruct (IHs l3' l3'' eq_refl) as [l1' [l1'' [l2' [l2'' [-> [-> [s1 s2]]]]]]].
    exists (x :: l1'), l1'', l2', l2''; auto.
    repeat constructor; assumption.
- destruct l3' as [|b l3'].
  + cbn in Heq3. subst.
    destruct (IHs nil l''' eq_refl) as [l1' [l1'' [l2' [l2'' [-> [-> [[-> ->]%shuffle_nil_inv s2]]]]]]].
    exists nil, l1'', nil, (x :: l2''); auto.
    repeat constructor. assumption.
  + cbn in Heq3. injection Heq3 as [= <- ->].
    destruct (IHs l3' l3'' eq_refl) as [l1' [l1'' [l2' [l2'' [-> [-> [s1 s2]]]]]]].
    exists l1', l1'', (x :: l2'), l2''; auto.
    repeat constructor; assumption.
Qed.

Lemma shuffle_elt_inv A (a : A) l1 l2 l3' l3'' : shuffle l1 l2 (l3' ++ a :: l3'') ->
  exists l1' l1'' l2' l2'',    ((l1 = l1' ++ a :: l1'' /\ l2 = l2' ++ l2'')
                                  \/ (l1 = l1' ++ l1'' /\ l2 = l2' ++ a :: l2''))
                           /\ shuffle l1' l2' l3' /\ shuffle l1'' l2'' l3''.
Proof.
intros [l1' [l1'' [l2' [l2'' [-> [-> [s' s'']]]]]]]%shuffle_app_inv.
inversion s'' as [ | x l1 l2 l3 | x l1 l2 l3 ]; subst.
- exists l1', l1, l2', l2''. now split; [ left | ].
- exists l1', l1'', l2', l2. now split; [ right | ].
Qed.

Lemma shuffle_Permutation A (l1 l2 l3 : list A) :
  shuffle l1 l2 l3 -> Permutation (l1 ++ l2) l3.
Proof.
intro s. induction s.
- apply perm_nil.
- now apply Permutation_cons.
- symmetry. apply Permutation_cons_app. symmetry. assumption.
Qed.

Lemma Permutation_shuffle A (l1 l2 l3 l3' : list A) : shuffle l1 l2 l3 -> Permutation l3 l3' ->
  exists l1' l2', Permutation l1 l1' /\ Permutation l2 l2' /\ shuffle l1' l2' l3'.
Proof.
intro s. induction s as [ | x l' l'' l''' s IHs | x l' l'' l''' s IHs ] in l3' |-; intro p.
- exists nil, nil. repeat split; [ constructor .. | ].
  rewrite (Permutation_nil p). apply shuffle_nil.
- assert (p' := p). symmetry in p'. apply Permutation_vs_cons_inv in p' as [l31 [l32 ->]].
  apply Permutation_cons_app_inv in p.
  apply IHs in p as [l1' [l2' [p1 [p2 s']]]].
  clear s IHs l'''. induction l31 as [|b l31 IHl] in l', l1', l'', l2', s', p1, p2 |- *.
  + exists (x :: l1'), l2'.
    split; [ now apply Permutation_cons | split; [ assumption | ] ].
    cbn. apply shuffle_l. assumption.
  + cbn in s'. inversion s' as [ | y l0' l0'' l0''' s'' | y l0' l0'' l0''' s'' ]; subst.
    * assert (p' := p1). apply Permutation_vs_cons_inv in p' as [l11 [l12 ->]].
      symmetry in p1. apply Permutation_cons_app_inv in p1. symmetry in p1.
      destruct (IHl _ _ _ _ p1 p2 s'') as [l1'' [l2'' [HP1 [HP2 s]]]].
      exists (b :: l1''), l2''. split; [ | split ].
      -- symmetry. rewrite app_comm_cons. apply Permutation_cons_app.
         symmetry. assumption.
      -- assumption.
      -- cbn. apply shuffle_l. assumption.
    * assert (p' := p2). apply Permutation_vs_cons_inv in p' as [l21 [l22 ->]].
      symmetry in p2. apply Permutation_cons_app_inv in p2. symmetry in p2.
      destruct (IHl _ _ _ _ p1 p2 s'') as [l1'' [l2'' [HP1 [HP2 s]]]].
      exists l1'', (b :: l2''). repeat split.
      -- assumption.
      -- symmetry. apply Permutation_cons_app. symmetry. assumption.
      -- cbn. apply shuffle_r. assumption.
- assert (p' := p). symmetry in p'. apply Permutation_vs_cons_inv in p' as [l31 [l32 ->]].
  apply Permutation_cons_app_inv in p.
  apply IHs in p as [l1' [l2' [p1 [p2 s']]]].
  clear s IHs l'''. induction l31 as [|b l31 IHl] in l', l1', l'', l2', s', p1, p2 |- *.
  + exists l1', (x :: l2'). repeat split.
    * assumption.
    * now apply Permutation_cons.
    * cbn. apply shuffle_r. assumption.
  + cbn in s'. inversion s' as [ | y l0' l0'' l0''' s'' | y l0' l0'' l0''' s'' ]; subst.
    * assert (p' := p1). apply Permutation_vs_cons_inv in p' as [l11 [l12 ->]].
      symmetry in p1. apply Permutation_cons_app_inv in p1. symmetry in p1.
      destruct (IHl _ _ _ _ p1 p2 s'') as [l1'' [l2'' [HP1 [HP2 s]]]].
      exists (b :: l1''), l2''. repeat split.
      -- symmetry. apply Permutation_cons_app. symmetry. assumption.
      -- assumption.
      -- cbn. apply shuffle_l. assumption.
    * assert (p' := p2). apply Permutation_vs_cons_inv in p' as [l21 [l22 ->]].
      symmetry in p2. apply Permutation_cons_app_inv in p2. symmetry in p2.
      destruct (IHl _ _ _ _ p1 p2 s'') as [l1'' [l2'' [HP1 [HP2 s]]]].
      exists l1'', (b :: l2''). repeat split.
      -- assumption.
      -- symmetry. rewrite app_comm_cons. apply Permutation_cons_app. symmetry. assumption.
      -- cbn. apply shuffle_r. assumption.
Qed.

Lemma Permutation_app_shuffle A (l1 l2 l3 : list A) : Permutation (l1 ++ l2) l3 ->
  exists l1' l2', Permutation l1 l1' /\ Permutation l2 l2' /\ shuffle l1' l2' l3.
Proof. intro p. refine (Permutation_shuffle _ p). apply shuffle_app. Qed.

Lemma shuffle_length A (l1 l2 l3 : list A) : shuffle l1 l2 l3 -> length l1 + length l2 = length l3.
Proof. intros s%shuffle_Permutation%Permutation_length. rewrite <- length_app. assumption. Qed.

Lemma shuffle_map A B (f : A -> B) l1 l2 l3 :
  shuffle l1 l2 l3 -> shuffle (map f l1) (map f l2) (map f l3).
Proof. intro s. induction s; constructor; assumption. Qed.

Lemma shuffle_map_inv A B (f : A -> B) l1' l2' l3 : shuffle l1' l2' (map f l3) ->
  exists l1 l2, l1' = map f l1 /\ l2' = map f l2 /\ shuffle l1 l2 l3.
Proof.
intro s. remember (map f l3) as l3' eqn:Heql3.
induction s as [ | x l' l'' l''' s IHs | x l' l'' l''' s IHs ] in l3, Heql3 |- *.
- symmetry in Heql3. apply map_eq_nil in Heql3 as ->.
  exists [], []. repeat split. constructor.
- decomp_map_eq Heql3. subst.
  destruct (IHs l''' eq_refl) as [l1' [l2' [-> [-> Hs]]]].
  exists (x :: l1'), l2'. repeat split. constructor. assumption.
- decomp_map_eq Heql3. subst.
  destruct (IHs l''' eq_refl) as [l1' [l2' [-> [-> Hs]]]].
  exists l1', (x :: l2'). repeat split. constructor. assumption.
Qed.

Lemma partition_shuffle A f (l l1 l2: list A) : partition f l = (l1, l2) -> shuffle l1 l2 l.
Proof.
induction l as [|a l IHl] in l1, l2 |- *; intro Hp.
- rewrite (proj2 (partition_inv_nil _ nil) eq_refl) in Hp. injection Hp as [= <- <-]. constructor.
- cbn in Hp.
  destruct (f a), (partition f l); cbn in *; injection Hp as [= <- <-]; constructor; apply IHl; reflexivity.
Qed.

Lemma in_shuffle A (l1 l2 l3 : list A) :
  shuffle l1 l2 l3 -> forall a, In a l1 \/ In a l2 <-> In a l3.
Proof.
intro s. induction s as [ | x l' l'' l''' s IHs | x l' l'' l''' s IHs ]; intro a; split; cbn.
- intros [[] | []].
- intros [].
- rewrite <- IHs, or_assoc. exact id.
- rewrite or_assoc, IHs. exact id.
- rewrite <- IHs, <- or_assoc, (or_comm (In a l')), or_assoc. exact id.
- rewrite <- IHs, <- or_assoc, (or_comm (x = a)), or_assoc. exact id.
Qed.

Lemma shuffle_sublist_l A (l1 l2 l3 : list A) : shuffle l1 l2 l3 -> sublist l1 l3.
Proof. intro s. induction s; constructor; assumption. Qed.

Lemma shuffle_sublist_r A (l1 l2 l3 : list A) : shuffle l1 l2 l3 -> sublist l2 l3.
Proof. intro s. induction s; constructor; assumption. Qed.

Lemma NoDup_shuffle_l A (l1 l2 l3 : list A) : shuffle l1 l2 l3 -> NoDup l3 -> NoDup l1.
Proof. intros Hs%shuffle_sublist_l. exact (NoDup_sublist Hs). Qed.

Lemma NoDup_shuffle_r A (l1 l2 l3 : list A) : shuffle l1 l2 l3 -> NoDup l3 -> NoDup l2.
Proof. intros Hs%shuffle_sublist_r. exact (NoDup_sublist Hs). Qed.
