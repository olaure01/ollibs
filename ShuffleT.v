From Stdlib Require Import List.
From OLlibs Require Import Datatypes_more List_more SubList Permutation_Type_more Shuffle.
Import ListNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.

Inductive shuffleT (A : Type) : list A -> list A -> list A -> Type :=
| shuffleT_nil : shuffleT nil nil nil
| shuffleT_l a l1 l2 l3 : shuffleT l1 l2 l3 -> shuffleT (a :: l1) l2 (a :: l3)
| shuffleT_r a l1 l2 l3 : shuffleT l1 l2 l3 -> shuffleT l1 (a :: l2) (a :: l3).

Lemma shuffleT_shuffle A (l1 l2 l3 : list A) : shuffleT l1 l2 l3 -> shuffle l1 l2 l3.
Proof. intro s. induction s as [ | a l1' l2' l3' s IHs | a l1' l2' l3' s IHs ]; now constructor. Qed.

Lemma shuffleT_nil_l A (l2 l3 : list A) : shuffleT nil l2 l3 -> l2 = l3.
Proof.
intro s. induction l2 as [|a l2 IHl2] in l3, s |- *; inversion s.
- reflexivity.
- subst. f_equal. apply IHl2. assumption.
Qed.

Lemma shuffleT_nil_r A (l1 l3 : list A) : shuffleT l1 nil l3 -> l1 = l3.
Proof.
intro s. induction l1 as [|a l1 IHl1] in l3, s |- *; inversion s.
- reflexivity.
- subst. f_equal. apply IHl1. assumption.
Qed.

Lemma shuffleT_nil_id A (l : list A) : shuffleT nil l l.
Proof. now induction l as [|a l IH]; constructor. Qed.

Lemma shuffleT_id_nil A (l : list A) : shuffleT l nil l.
Proof. now induction l as [|a l IH]; constructor. Qed.

Lemma shuffleT_comm A (l1 l2 l3 : list A) : shuffleT l1 l2 l3 -> shuffleT l2 l1 l3.
Proof. intro s. induction s; constructor; assumption. Qed.

Lemma shuffleT_assoc_r A (l1 l2 l3 l' l : list A) :
  shuffleT l1 l2 l' -> shuffleT l' l3 l -> { l'' & shuffleT l1 l'' l & shuffleT l2 l3 l'' }.
Proof.
intro s. induction s as [ | a l1' l2' l3' s IHs | a l1' l2' l3' s IHs ] in l3, l |- *; intro s'.
- exists l3; [ assumption | apply shuffleT_nil_id ].
- induction l3 as [|x l3 IHl] in l, s' |- *.
  + inversion s' as [ | ? ? ? ? s'' | ]. subst.
    apply IHs in s'' as [l'' s'1 s'2].
    exists l''; [ constructor | ]; assumption.
  + inversion s' as [ | ? ? ? ? s'' | ? ? ? ? s'' ]; subst.
    * apply IHs in s'' as [l'' s'1 s'2].
      exists l''; [ constructor | ]; assumption.
    * apply IHl in s'' as [l'' s'1 s'2].
      exists (x :: l''); constructor; assumption.
- induction l3 as [|x l3 IHl] in l, s' |- *.
  + inversion s' as [ | ? ? ? ? s'' | ]. subst.
    apply IHs in s'' as [l'' s'1 s'2].
    exists (a :: l''); constructor; assumption.
  + inversion s' as [ | ? ? ? ? s'' | ? ? ? ? s'' ]; subst.
    * apply IHs in s'' as [l'' s'1 s'2].
      exists (a :: l''); constructor; assumption.
    * apply IHl in s'' as [l'' s'1 s'2].
      exists (x :: l''); constructor; assumption.
Qed.

Lemma shuffleT_assoc_l A (l1 l2 l3 l' l : list A) :
  shuffleT l1 l' l -> shuffleT l2 l3 l' -> { l'' & shuffleT l1 l2 l'' & shuffleT l'' l3 l }.
Proof.
intros s1%shuffleT_comm s2%shuffleT_comm.
destruct (shuffleT_assoc_r s2 s1) as [l'' s1'%shuffleT_comm s2'%shuffleT_comm].
exists l''; assumption.
Qed.

Lemma shuffleT_app A (l1 l2 : list A) : shuffleT l1 l2 (l1 ++ l2).
Proof.
induction l1 as [|a l1 IH].
- apply shuffleT_nil_id.
- cbn. constructor. exact IH.
Qed.

Lemma shuffleT_app_swap A (l1 l2 : list A) : shuffleT l1 l2 (l2 ++ l1).
Proof. apply shuffleT_comm, shuffleT_app. Qed.

Lemma shuffleT_app_app A (l1 l2 l3 l1' l2' l3' : list A) : shuffleT l1 l2 l3 -> shuffleT l1' l2' l3' ->
  shuffleT (l1 ++ l1') (l2 ++ l2') (l3 ++ l3').
Proof.
intro s1. induction s1 as [ | x l' l'' l''' s1 IHs1 | x l' l'' l''' s1 IHs1 ];
  intro s2; [ assumption | cbn; constructor; apply IHs1, s2 .. ].
Qed.

Lemma sublist_app_app_l_l A (l0 l1 l2 l3 : list A) : shuffleT l1 l2 l3 -> shuffleT (l0 ++ l1) l2 (l0 ++ l3).
Proof. rewrite <- (app_nil_l l2). apply shuffleT_app_app, shuffleT_id_nil. Qed.

Lemma sublist_app_app_l_r A (l0 l1 l2 l3 : list A) : shuffleT l1 l2 l3 -> shuffleT (l1 ++ l0) l2 (l3 ++ l0).
Proof. rewrite <- (app_nil_r l2) at 2. intro s. apply (shuffleT_app_app s), shuffleT_id_nil. Qed.

Lemma sublist_app_app_r_l A (l0 l1 l2 l3 : list A) : shuffleT l1 l2 l3 -> shuffleT l1 (l0 ++ l2) (l0 ++ l3).
Proof. rewrite <- (app_nil_l l1). apply shuffleT_app_app, shuffleT_nil_id. Qed.

Lemma sublist_app_app_r_r A (l0 l1 l2 l3 : list A) : shuffleT l1 l2 l3 -> shuffleT l1 (l2 ++ l0) (l3 ++ l0).
Proof. rewrite <- (app_nil_r l1) at 2. intro s. apply (shuffleT_app_app s), shuffleT_nil_id. Qed.

Lemma shuffleT_elt_l A (a : A) l1' l1'' l2 l3 : shuffleT (l1' ++ a :: l1'') l2 l3 ->
  {'(l3', l3'') | l3 = l3' ++ a :: l3'' }.
Proof.
intro s. remember (l1' ++ a :: l1'') as l1 eqn:Heql1.
induction s as [ | x l' l'' l''' s IHs | x l' l'' l''' s IHs ] in l1', l1'', Heql1 |- *.
- apply app_cons_not_nil in Heql1 as [].
- destruct l1' as [|b l1']; cbn in Heql1; injection Heql1 as [= -> ->].
  + exists (nil, l'''). reflexivity.
  + destruct (IHs _ _ eq_refl) as [(l3', l3'') ->].
    exists (b :: l3', l3''). reflexivity.
- destruct (IHs _ _ Heql1) as [(l3', l3'') ->].
  exists (x :: l3', l3''). reflexivity.
Qed.

Lemma shuffleT_elt_r A (a : A) l1 l2' l2'' l3 : shuffleT l1 (l2' ++ a :: l2'') l3 ->
  {'(l3', l3'') | l3 = l3' ++ a :: l3'' }.
Proof. intros s%shuffleT_comm. exact (shuffleT_elt_l _ _ _ s). Qed.

Lemma shuffleT_add_elt_l A (a : A) l1 l2 l3' l3'' : shuffleT l1 l2 (l3' ++ l3'') ->
  {'(l1', l1'') & l1 = l1' ++ l1'' & shuffleT (l1' ++ a :: l1'') l2 (l3' ++ a :: l3'') }.
Proof.
intro s. remember (l3' ++ l3'') as l3 eqn:Heq3.
induction s as [ | x l' l'' l''' s IHs | x l' l'' l''' s IHs ] in l3', l3'', Heq3 |- *.
- symmetry in Heq3. apply app_eq_nil in Heq3 as [-> ->].
  exists (nil, nil); constructor. constructor.
- destruct l3' as [|b l3'].
  + cbn in Heq3. subst.
    destruct (IHs nil l''' eq_refl) as [[l1' l1''] -> s']. cbn in s'.
    exists (nil, x :: l1' ++ l1''); auto.
    cbn. constructor. constructor. assumption.
  + cbn in Heq3. injection Heq3 as [= <- ->].
    destruct (IHs l3' l3'' eq_refl) as [[l1' l1''] -> s'].
    exists (x :: l1', l1''); auto.
    cbn. constructor. assumption.
- destruct l3' as [|b l3'].
  + cbn in Heq3. subst.
    destruct (IHs nil l''' eq_refl) as [[l1' l1''] -> s']. cbn in s'.
    exists (nil, l1' ++ l1''); auto.
    cbn. constructor. constructor. assumption.
  + cbn in Heq3. injection Heq3 as [= <- ->].
    destruct (IHs l3' l3'' eq_refl) as [[l1' l1''] -> s'].
    exists (l1', l1''); auto.
    cbn. constructor. assumption.
Qed.

Lemma shuffleT_add_elt_r A (a : A) l1 l2 l3' l3'' : shuffleT l1 l2 (l3' ++ l3'') ->
  {'(l2', l2'') & l2 = l2' ++ l2'' & shuffleT l1 (l2' ++ a :: l2'') (l3' ++ a :: l3'') }.
Proof.
intros [(l2', l2'') -> s%shuffleT_comm]%shuffleT_comm%(shuffleT_add_elt_l a).
now exists (l2', l2'').
Qed.

Lemma shuffleT_nil_inv A (l1 l2 : list A) : shuffleT l1 l2 nil -> l1 = nil /\ l2 = nil.
Proof. intro s. inversion s. split; reflexivity. Qed.

Lemma shuffleT_length_1_inv A (a : A) l1 l2 :
  shuffleT l1 l2 [a] -> (l1 = [a] /\ l2 = nil) + (l1 = nil /\ l2  = [a]).
Proof.
intro s. inversion s as [ | b l1' l2' l3' s' | b l1' l2' l3' s' ]; subst;
  apply shuffleT_nil_inv in s' as [-> ->]; [left | right]; repeat split.
Qed.

Lemma shuffleT_length_2_inv A (a b : A) l1 l2 : shuffleT l1 l2 [a; b] ->
  (l1 = [a; b] /\ l2 = nil) + (l1 = [a] /\ l2 = [b]) + (l1 = [b] /\ l2 = [a]) + (l1 = nil /\ l2  = [a; b]).
Proof.
intro s. inversion s as [ | c l1' l2' l3' s' | c l1' l2' l3' s' ]; subst;
  apply shuffleT_length_1_inv in s' as [[-> ->] | [-> ->]];
  [left; left; left | left; left; right | left; right | right]; repeat split.
Qed.

Lemma shuffleT_app_inv A (l1 l2 l3' l3'' : list A) :
  shuffleT l1 l2 (l3' ++ l3'') -> {'(l1', l1'', l2', l2'')
                                   & l1 = l1' ++ l1'' /\ l2 = l2' ++ l2''
                                   & ((shuffleT l1' l2' l3') * (shuffleT l1'' l2'' l3''))%type }.
Proof.
intro s. remember (l3' ++ l3'') as l3 eqn:Heq3.
induction s as [ | x l' l'' l''' s IHs | x l' l'' l''' s IHs ] in l3', l3'', Heq3 |- *.
- symmetry in Heq3. apply app_eq_nil in Heq3 as [-> ->].
  exists (nil, nil, nil, nil); split; constructor.
- destruct l3' as [|b l3'].
  + cbn in Heq3. subst.
    destruct (IHs nil l''' eq_refl) as [[[[l1' l1''] l2'] l2''] [-> ->] [[-> ->]%shuffleT_nil_inv s2]].
    exists (nil, x :: l1'', nil, l2''); auto.
    split; constructor. assumption.
  + cbn in Heq3. injection Heq3 as [= <- ->].
    destruct (IHs l3' l3'' eq_refl) as [[[[l1' l1''] l2'] l2''] [-> ->] [s1 s2]].
    exists (x :: l1', l1'', l2', l2''); auto.
    split; [ constructor | ]; assumption.
- destruct l3' as [|b l3'].
  + cbn in Heq3. subst.
    destruct (IHs nil l''' eq_refl) as [[[[l1' l1''] l2'] l2''] [-> ->] [[-> ->]%shuffleT_nil_inv s2]].
    exists (nil, l1'', nil, x :: l2''); auto.
    split; constructor. assumption.
  + cbn in Heq3. injection Heq3 as [= <- ->].
    destruct (IHs l3' l3'' eq_refl) as [[[[l1' l1''] l2'] l2''] [-> ->] [s1 s2]].
    exists (l1', l1'', x :: l2', l2''); auto.
    split; [ constructor | ]; assumption.
Qed.

Lemma shuffleT_elt_inv A (a : A) l1 l2 l3' l3'' : shuffleT l1 l2 (l3' ++ a :: l3'') ->
  {'(l1', l1'', l2', l2'') &     (l1 = l1' ++ a :: l1'' /\ l2 = l2' ++ l2'')
                              \/ (l1 = l1' ++ l1'' /\ l2 = l2' ++ a :: l2'')
                           & ((shuffleT l1' l2' l3') * (shuffleT l1'' l2'' l3''))%type }.
Proof.
intros [[[[l1' l1''] l2'] l2''] [-> ->] [s' s'']]%shuffleT_app_inv.
inversion s'' as [ | x l1 l2 l3 | x l1 l2 l3 ]; subst.
- now exists (l1', l1, l2', l2''); [ left | ].
- now exists (l1', l1'', l2', l2); [ right | ].
Qed.

Lemma Permutation_Type_shuffleT A (l1 l2 l3 : list A) :
  shuffleT l1 l2 l3 -> Permutation_Type (l1 ++ l2) l3.
Proof.
intro s. induction s.
- apply Permutation_Type_nil_nil.
- now apply Permutation_Type_cons.
- symmetry. apply Permutation_Type_cons_app. symmetry. assumption.
Qed.

Lemma shuffleT_Permutation_Type A (l1 l2 l3 l3' : list A) : shuffleT l1 l2 l3 -> Permutation_Type l3 l3' ->
  {'(l1', l2') & (Permutation_Type l1 l1' * Permutation_Type l2 l2')%type & shuffleT l1' l2' l3' }.
Proof.
intro s. induction s as [ | x l' l'' l''' s IHs | x l' l'' l''' s IHs ] in l3' |-; intro p.
- exists (nil, nil).
  + split; reflexivity.
  + rewrite (Permutation_Type_nil p). apply shuffleT_nil.
- assert (p' := p). symmetry in p'. apply Permutation_Type_vs_cons_inv in p' as [(l31, l32) ->].
  apply Permutation_Type_cons_app_inv in p.
  apply IHs in p as [(l1', l2') [p1 p2] s'].
  clear s IHs l'''. induction l31 as [|b l31 IHl] in l', l1', l'', l2', s', p1, p2 |- *.
  + exists (x :: l1', l2').
    * now split; [ apply Permutation_Type_cons | ].
    * cbn. apply shuffleT_l. assumption.
  + cbn in s'. inversion s' as [ | y l0' l0'' l0''' s'' | y l0' l0'' l0''' s'' ]; subst.
    * assert (p' := p1). apply Permutation_Type_vs_cons_inv in p' as [(l11, l12) ->].
      symmetry in p1. apply Permutation_Type_cons_app_inv in p1. symmetry in p1.
      destruct (IHl _ _ _ _ p1 p2 s'') as [(l1'', l2'') [] ].
      exists (b :: l1'', l2'').
      -- split; [ | assumption ].
         symmetry. rewrite app_comm_cons. apply Permutation_Type_cons_app. cbn.
         symmetry. assumption.
      -- cbn. apply shuffleT_l. assumption.
    * assert (p' := p2). apply Permutation_Type_vs_cons_inv in p' as [(l21, l22) ->].
      symmetry in p2. apply Permutation_Type_cons_app_inv in p2. symmetry in p2.
      destruct (IHl _ _ _ _ p1 p2 s'') as [(l1'', l2'') [] ].
      exists (l1'', b :: l2'').
      -- split; [ assumption | ].
         symmetry. apply Permutation_Type_cons_app. cbn.
         symmetry. assumption.
      -- cbn. apply shuffleT_r. assumption.
- assert (p' := p). symmetry in p'. apply Permutation_Type_vs_cons_inv in p' as [(l31, l32) ->].
  apply Permutation_Type_cons_app_inv in p.
  apply IHs in p as [(l1', l2') [p1 p2] s'].
  clear s IHs l'''. induction l31 as [|b l31 IHl] in l', l1', l'', l2', s', p1, p2 |- *.
  + exists (l1', x :: l2').
    * now split; [ | apply Permutation_Type_cons ].
    * cbn. apply shuffleT_r. assumption.
  + cbn in s'. inversion s' as [ | y l0' l0'' l0''' s'' | y l0' l0'' l0''' s'' ]; subst.
    * assert (p' := p1). apply Permutation_Type_vs_cons_inv in p' as [(l11, l12) ->].
      symmetry in p1. apply Permutation_Type_cons_app_inv in p1. symmetry in p1.
      destruct (IHl _ _ _ _ p1 p2 s'') as [(l1'', l2'') [] ].
      exists (b :: l1'', l2'').
      -- split; [ | assumption ].
         symmetry. apply Permutation_Type_cons_app. cbn.
         symmetry. assumption.
      -- cbn. apply shuffleT_l. assumption.
    * assert (p' := p2). apply Permutation_Type_vs_cons_inv in p' as [(l21, l22) ->].
      symmetry in p2. apply Permutation_Type_cons_app_inv in p2. symmetry in p2.
      destruct (IHl _ _ _ _ p1 p2 s'') as [(l1'', l2'') [] ].
      exists (l1'', b :: l2'').
      -- split; [ assumption | ].
         symmetry. rewrite app_comm_cons. apply Permutation_Type_cons_app. cbn.
         symmetry. assumption.
      -- cbn. apply shuffleT_r. assumption.
Qed.

Lemma Permutation_Type_app_shuffleT A (l1 l2 l3 : list A) : Permutation_Type (l1 ++ l2) l3 ->
  {'(l1', l2') & (Permutation_Type l1 l1' * Permutation_Type l2 l2')%type & shuffleT l1' l2' l3}.
Proof. intro p. refine (shuffleT_Permutation_Type _ p). apply shuffleT_app. Qed.

Lemma shuffleT_length A (l1 l2 l3 : list A) : shuffleT l1 l2 l3 -> length l1 + length l2 = length l3.
Proof. intros s%Permutation_Type_shuffleT%Permutation_Type_length. rewrite <- length_app. assumption. Qed.

Lemma shuffleT_map A B (f : A -> B) l1 l2 l3 :
  shuffleT l1 l2 l3 -> shuffleT (map f l1) (map f l2) (map f l3).
Proof. intro s. induction s; constructor; assumption. Qed.

Lemma shuffleT_map_inv A B (f : A -> B) l1' l2' l3 : shuffleT l1' l2' (map f l3) ->
  {'(l1, l2) & l1' = map f l1 /\ l2' = map f l2 & shuffleT l1 l2 l3 }.
Proof.
intro s. remember (map f l3) as l3' eqn:Heql3.
induction s as [ | x l' l'' l''' s IHs | x l' l'' l''' s IHs ] in l3, Heql3 |- *.
- symmetry in Heql3. apply map_eq_nil in Heql3 as ->.
  exists ([], []); [ repeat split | constructor ].
- decomp_map Heql3. subst.
  destruct (IHs l''' eq_refl) as [(l1', l2') [-> ->] Hs].
  exists (x :: l1', l2'); [ repeat split | constructor; assumption ].
- decomp_map Heql3. subst.
  destruct (IHs l''' eq_refl) as [(l1', l2') [-> ->] Hs].
  exists (l1', x :: l2'); [ repeat split | constructor; assumption ].
Qed.

Lemma partition_shuffleT A f (l l1 l2: list A) : partition f l = (l1, l2) -> shuffleT l1 l2 l.
Proof.
induction l as [|a l IHl] in l1, l2 |- *; intro Hp.
- rewrite (proj2 (partition_inv_nil _ nil) eq_refl) in Hp. injection Hp as [= <- <-]. constructor.
- cbn in Hp.
  destruct (f a), (partition f l); cbn in *; injection Hp as [= <- <-]; constructor; apply IHl; reflexivity.
Qed.

Lemma elements_in_shuffleT A (l1 l2 l3 : list A) :
  shuffleT l1 l2 l3 -> forall a, iffT (In_inf a l1 + In_inf a l2) (In_inf a l3).
Proof.
intro s. induction s as [ | x l' l'' l''' s IHs | x l' l'' l''' s IHs ]; intro a; split; cbn.
- intros [[] | []].
- intros [].
- intros [[-> | ] | ]; [left; reflexivity | right .. ]; apply IHs; [left | right]; assumption.
- intros [-> | [ | ]%IHs ]; [left; left; reflexivity | left; right | right ]; assumption.
- intros [ | [-> | ] ]; [ right | left; reflexivity | right ]; apply IHs; [left | right]; assumption.
- intros [-> | [ | ]%IHs ]; [right; left; reflexivity | left | right; right ]; assumption.
Qed.

Lemma shuffleT_sublist_l A (l1 l2 l3 : list A) : shuffleT l1 l2 l3 -> sublist l1 l3.
Proof. intro s. induction s; constructor; assumption. Qed.

Lemma shuffleT_sublist_r A (l1 l2 l3 : list A) : shuffleT l1 l2 l3 -> sublist l2 l3.
Proof. intro s. induction s; constructor; assumption. Qed.

Lemma NoDup_inf_shuffleT_l A (l1 l2 l3 : list A) : shuffleT l1 l2 l3 -> NoDup_inf l3 -> NoDup_inf l1.
Proof.
intro s. induction s as [ | x l' l'' l''' s IHs | x l' l'' l''' s IHs ]; intro Hnd.
- constructor.
- inversion Hnd. subst.
  constructor.
  + intro Hin.
    apply Permutation_Type_shuffleT, (Permutation_Type_in_inf x) in s.
    * contradiction s.
    * apply in_inf_or_app. left. assumption.
  + apply IHs. assumption.
- inversion Hnd. subst.
  apply IHs. assumption.
Qed.

Lemma NoDup_inf_shuffleT_r A (l1 l2 l3 : list A) : shuffleT l1 l2 l3 -> NoDup_inf l3 -> NoDup_inf l2.
Proof. intros Hs%shuffleT_comm. exact (NoDup_inf_shuffleT_l Hs). Qed.
