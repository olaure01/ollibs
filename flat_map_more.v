(** Add-ons for [List] library:
Properties of [flat_map]. *)

From OLlibs Require Import funtheory List_more PermutationT_more CPermutationT GPermutationT.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


Lemma flat_map_eq_elt_inv A B (f : A -> list B) a L l1 l2 :
  flat_map f L = l1 ++ a :: l2 ->
  {'(L1, L2, L0, l1', l2') | l1 = flat_map f L1 ++ l1' /\ l2 = l2' ++ flat_map f L2
                           & L = L1 ++ L0 :: L2 /\ f L0 = l1' ++ a :: l2' }.
Proof.
intro Heq. rewrite flat_map_concat_map in Heq.
apply concat_eq_elt in Heq as [(((L1, L2), l1''), l2'') [-> ->] Heq].
remember (l1'' ++ a :: l2'') as L0.
decomp_map_eq Heq eqn:Hf. subst L.
now exists (L1, L2, L0, l1'', l2''); cbn; repeat split; rewrite ? flat_map_concat_map.
Qed.

Lemma app_eq_flat_map_cons_fun_dichot B T (f : B -> T) L l1 l2 :
  l1 ++ l2 = flat_map (fun '(p1, p2) => f p1 :: p2) L ->
      {'(L1, L2, n, l3, l4) | l4 <> nil /\ L = L1 ++ (n, l3 ++ l4) :: L2
          & l1 = flat_map (fun '(p1,p2) => f p1 :: p2) (L1 ++ (n, l3) :: nil)
         /\ l2 = l4 ++ flat_map (fun '(p1,p2) => f p1 :: p2) L2 }
    + {'(L1, L2) | L = L1 ++ L2
          & l1 = flat_map (fun '(p1,p2) => f p1 :: p2) L1
         /\ l2 = flat_map (fun '(p1,p2) => f p1 :: p2) L2 }.
Proof.
induction L as [|[b l] L IHL] in l1, l2 |- *; cbn; intro Heq.
- apply app_eq_nil in Heq as [-> ->].
  right. exists (nil, nil); repeat split.
- rewrite app_comm_cons in Heq.
  decomp_app_eq_app Heq as [[l0 Heq0 ->]|[l0 -> Heq0]].
  + destruct l1 as [|t l1].
    * cbn in Heq0. subst.
      right. exists (nil, (b, l) :: L); repeat split.
    * cbn in Heq0. injection Heq0 as [= -> <-].
      destruct l0 as [|t' l0]; [right|left].
      -- exists ((b, l1) :: nil , L); list_simpl; repeat split.
      -- exists (nil, L, b , l1, t' :: l0); list_simpl; repeat split. intros [=].
  + apply IHL in Heq0 as [ [((((L1, L2), n), l1'), l2') [Hnil ->] [-> ->]]
                         | [(L1, L2) -> [-> ->]]]; [left | right].
    * now exists ((b, l) :: L1, L2, n, l1', l2').
    * now exists ((b, l) :: L1, L2).
Qed.

#[local] Ltac decomp_app_eq_flat_map_cons_fun_core H p :=
  match type of H with
  | ?lh ++ ?lr = flat_map (fun '(p1,p2) => ?f p1 :: p2) ?L => apply app_eq_flat_map_cons_fun_dichot in H as p
  end.
Tactic Notation "decomp_app_eq_flat_map_cons_fun" hyp(H) "as" simple_intropattern(p) :=
  decomp_app_eq_flat_map_cons_fun_core H p.
Tactic Notation "decomp_app_eq_flat_map_cons_fun" hyp(H) :=
  let l1 := fresh "l" in
  let l2 := fresh "l" in
  let n := fresh "n" in
  let L1 := fresh "L" in
  let L2 := fresh "L" in
  let Hnil := fresh "Hnil" in
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  decomp_app_eq_flat_map_cons_fun_core H ipattern:([[((((L1, L2), n), l1), l2) [Hnil H1] [H2 H3]]
                                                   |[(L1, L2) H1 [H2 H3]]]);
  subst.

Lemma app_eq_app_flat_map_cons_fun_trichot B T (f : B -> T) l0 L l1 l2 :
  l1 ++ l2 = l0 ++ flat_map (fun '(p1, p2) => f p1 :: p2) L ->
      { l' | l' <> nil /\ l0 = l1 ++ l'
           & l2 = l' ++ flat_map (fun '(p1,p2) => f p1 :: p2) L }
    + {'(L1, L2, n, l3, l4) | l4 <> nil /\ L = L1 ++ (n , l3 ++ l4) :: L2
           & l1 = l0 ++ flat_map (fun '(p1,p2) => f p1 :: p2) (L1 ++ (n, l3) :: nil)
          /\ l2 = l4 ++ flat_map (fun '(p1,p2) => f p1 :: p2) L2 }
    + {'(L1, L2) | L = L1 ++ L2
           & l1 = l0 ++ flat_map (fun '(p1,p2) => f p1 :: p2) L1
          /\ l2 = flat_map (fun '(p1,p2) => f p1 :: p2) L2 }.
Proof.
intro Heq. decomp_app_eq_app Heq as [[[|t l] <- ->]|[l -> Heq]].
- right. exists (nil, L); list_simpl; repeat split.
- left. left. exists (t :: l); repeat split. intros [=].
- decomp_app_eq_flat_map_cons_fun Heq as [[((((L1, L2), n), l'), l2') [Hnil ->] [-> ->]] | [(L1, L2) -> [-> ->]]].
  + left. right. now exists (L1, L2, n, l', l2').
  + right. now exists (L1, L2).
Qed.

#[local] Ltac decomp_app_eq_app_flat_map_cons_fun_core H p :=
  match type of H with
  | ?lh ++ ?lr = ?l0 ++ flat_map (fun '(p1,p2) => ?f p1 :: p2) ?L =>
     apply app_eq_app_flat_map_cons_fun_trichot in H as p
  end.
Tactic Notation "decomp_app_eq_app_flat_map_cons_fun" hyp(H) "as" simple_intropattern(p) :=
  decomp_app_eq_app_flat_map_cons_fun_core H p.
Tactic Notation "decomp_app_eq_app_flat_map_cons_fun" hyp(H) :=
  let l1 := fresh "l" in
  let l2 := fresh "l" in
  let n := fresh "n" in
  let L1 := fresh "L" in
  let L2 := fresh "L" in
  let Hnil := fresh "Hnil" in
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  decomp_app_eq_app_flat_map_cons_fun_core H ipattern:([[[l1 [Hnil H1] H2]
                                                       | [((((L1, L2), n), l1), l2) [Hnil H1] [H2 H3]]]
                                                       | [(L1, L2) H1 [H2 H3]]]);
  subst.

Lemma elt_eq_app_flat_map_cons_fun_trichot C T (f : C -> T) l0 L l1 l2 B :
  l1 ++ B :: l2 = l0 ++ flat_map (fun '(p1,p2) => f p1 :: p2) L ->
      { l' | l0 = l1 ++ B :: l'
           & l2 = l' ++ flat_map (fun '(p1,p2) => f p1 :: p2) L }
    + {'(L1, L2, n, l1',l2') | L = L1 ++ (n , l1' ++ B :: l2') :: L2
           & l1 = l0 ++ flat_map (fun '(p1,p2) => f p1 :: p2) L1 ++ (f n :: l1')
          /\ l2 = l2' ++ flat_map (fun '(p1,p2) => f p1 :: p2) L2 }
    + {'(L1 , L2, n , l) | B = f n /\ L = L1 ++ (n , l) :: L2
           & l1 = l0 ++ flat_map (fun '(p1,p2) => f p1 :: p2) L1
          /\ l2 = l ++ flat_map (fun '(p1,p2) => f p1 :: p2) L2 }.
Proof.
intro Heq. decomp_elt_eq_app Heq as [[l <- ->]|[l -> Heq]]; [ now left; left; exists l | ].
induction L as [|[n l'] L IHL] in l, l2, Heq |- *; cbn in Heq.
- exfalso. decomp_nil_eq Heq.
- rewrite app_comm_cons in Heq. decomp_elt_eq_app Heq as [[l1 Heq ->]|[l1 -> Heq]].
  + destruct l as [|t l]; inversion Heq; subst.
    * right. exists (nil, L, n, l'); repeat split.
    * left. right. exists (nil, L, n, l, l1); repeat split.
  + apply IHL in Heq as [[[l'' Heqa _]
                      | [((((L', L''), n'), l''), l''') -> [->%app_inv_head ->]]]
                      | [(((L', L''), n'), l'') [-> ->] [->%app_inv_head ->]]].
    * exfalso.
      rewrite <- (app_nil_r l0), <- 2 app_assoc in Heqa. apply app_inv_head in Heqa.
      cbn in Heqa. decomp_nil_eq Heqa.
    * left. right. exists ((n, l') :: L', L'', n', l'', l'''); list_simpl; repeat split.
    * right. exists ((n, l') :: L', L'', n' , l''); repeat split.
Qed.

#[local] Ltac decomp_elt_eq_app_flat_map_cons_fun_core H p :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l0 ++ flat_map (fun '(p1,p2) => ?f p1 ?A :: p2) ?L =>
    apply elt_eq_app_flat_map_cons_fun_trichot in H as p
  end.
Tactic Notation "decomp_elt_eq_app_flat_map_cons_fun" hyp(H) "as" simple_intropattern(p) :=
  decomp_elt_eq_app_flat_map_cons_fun_core H p.
Tactic Notation "decomp_elt_eq_app_flat_map_cons_fun" hyp(H) :=
  let l1 := fresh "l" in
  let l2 := fresh "l" in
  let L1 := fresh "L" in
  let L2 := fresh "L" in
  let n := fresh "n" in
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  let Heq := fresh "Heq" in
  decomp_elt_eq_app_flat_map_cons_fun_core H ipattern:([[[l1 H1 H2]
                                                       | [((((L1, L2), n), l1), l2) H1 [H2 H3]]]
                                                       | [(((L1, L2), n), l1) [Heq H1] [H2 H3]]] );
    [ | | try now inversion Heq ]; subst.

Lemma map_eq_app_flat_map_cons_fun_inv T T1 T2 (g : T -> T2) (f : T1 -> T2) lw' lw l L :
  map f lw = l ++ flat_map (fun '(p1, p2) => g p1 :: p2) L ->
  { Lw | l ++ flat_map (fun '(p1, p2) => app (map f lw') p2) L = map f Lw }.
Proof.
induction L as [|[b l0] L IHL] in lw, l |- *; cbn; intro Heq.
- exists lw. symmetry. assumption.
- rewrite app_comm_cons, app_assoc in Heq.
  apply IHL in Heq as [Lw Heq].
  remember (g b) as c. remember (flat_map (fun '(_, p2) => map f lw' ++ p2) L) as L0.
  decomp_map_eq Heq eqn:Hf. subst Lw. destruct Hf as [_ <-].
  exists (l ++ (lw' ++ l0) ++ L0). rewrite ! map_app. reflexivity.
Qed.

Lemma PermutationT_app_flat_map_cons_fun_inv B T (f : B -> T) lw0 L lw l :
  PermutationT lw (l ++ flat_map (fun '(p1, p2) => f p1 :: p2) L) ->
  {'(L', lw') & L <> nil -> L' <> nil &
           prod (lw = lw' ++ flat_map (fun '(p1,p2) => f p1 :: p2) L')
                (PermutationT (lw' ++ flat_map (fun '(p1,p2) => app lw0 p2) L')
                                  (l ++ flat_map (fun '(p1,p2) => app lw0 p2) L)) }.
Proof.
induction L as [|[n a] l0 IHL] in lw, l |- *; cbn; intros HP.
- rewrite app_nil_r in HP.
  now exists (nil, lw); rewrite ? app_nil_r.
- destruct (PermutationT_vs_elt_inv _ _ _ HP) as [(lw1, lw2) HP2]. subst. cbn in HP.
  apply PermutationT_app_inv in HP.
  rewrite app_assoc in HP; apply IHL in HP.
  destruct HP as [[L' l'] Hnil' [HeqL' HP']].
  decomp_app_eq_app_flat_map_cons_fun HeqL' as [[[l1 [_ ->] ->]|[((((L1, L2), n'), l1), l2) [_ ->] [-> ->]]]
                                               |[(L1, L2) -> [-> ->]]].
  + exists ((n, l1) :: L', lw1); simpl; repeat split.
    * intros _ Heqnil. inversion Heqnil.
    * rewrite <- ? app_assoc in HP' ; rewrite <- ? app_assoc.
      now apply PermutationT_app_middle.
  + exists (L1 ++ (n', l1) :: (n, l2) :: L2, l'); simpl; repeat split.
    * intros _ Heqnil. decomp_nil_eq Heqnil.
    * now rewrite ? flat_map_app; list_simpl.
    * rewrite ? flat_map_app in HP'. cbn in HP'. rewrite <- app_assoc in HP'.
      rewrite ? flat_map_app. cbn. rewrite <- ? app_assoc, app_assoc.
      apply PermutationT_app_middle. cbn.
      etransitivity; [ | rewrite app_assoc; apply HP'].
      rewrite app_assoc, (app_assoc l'). apply PermutationT_app_middle.
      now rewrite <- ? app_assoc.
  + exists (L1 ++ (n , nil) :: L2, l'); simpl; repeat split.
    * intros _ Heqnil. decomp_nil_eq Heqnil.
    * now rewrite ? flat_map_app, <- app_assoc.
    * rewrite ? flat_map_app, <- app_assoc in HP'.
      rewrite ? flat_map_app, <- app_assoc. cbn.
      rewrite app_nil_r, app_assoc. apply PermutationT_app_middle. rewrite <- app_assoc. assumption.
Qed.

Lemma PermutationT_map_eq_app_flat_map_cons_fun_inv T T1 T2 (g : T -> T2) (f : T1 -> T2) lw0 L lw lw' l :
  PermutationT lw lw' -> map f lw' = l ++ flat_map (fun '(p1, p2) => g p1 :: p2) L ->
  {'(L', lw') & L <> nil -> L' <> nil &
           prod (map f lw = lw' ++ flat_map (fun '(p1, p2) => g p1 :: p2) L')
                (PermutationT (lw' ++ flat_map (fun '(_, p2) => app (map f lw0) p2) L')
                                  (l ++ flat_map (fun '(_, p2) => app (map f lw0) p2) L)) }.
Proof.
intros HP%(PermutationT_map f) Heq.
apply PermutationT_app_flat_map_cons_fun_inv.
rewrite <- Heq. assumption.
Qed.

Lemma PermutationT_app_map_app_eq_app_flat_map_cons_fun_inv T T1 T2 (g : T -> T2) (f : T1 -> T2)
  (Hinj : injective f) l0 l1 l2 lp1 lp2 l L :
  PermutationT lp1 lp2 ->
  l1 ++ map f lp2 ++ l2 = l ++ flat_map (fun '(p1, p2) => g p1 :: p2) L ->
  {'(l1', l2', l3', l4', l', L') & prod (l1 ++ map f lp1 ++ l2 = l'
                                     ++ flat_map (fun '(p1, p2) => g p1 :: p2) L')
            (prod (PermutationT l1' l2')
                  (prod (l3' ++ map f l1' ++ l4'
                             = l' ++ flat_map (fun '(_, p2) => (app (map f l0) p2)) L')
                        (l3' ++ map f l2' ++ l4'
                             = l ++ flat_map (fun '(_, p2) => (app (map f l0) p2)) L))) }.
Proof.
intros HP Heq.
decomp_app_eq_app_flat_map_cons_fun Heq as [[[l1' [_ ->] Heq1]|[((((L1, L2), n), l1'), l2') [_ ->] [-> Heq2]]]
                                           |[(L1, L2) -> [-> Heq2]]].
- decomp_app_eq_app_flat_map_cons_fun Heq1
    as [[[l [_ ->] ->]|[((((L1, L2), n), l1''), l2'') [_ ->] [Heq2 ->]]]|[(L1, L2) -> [Heq2 ->]]].
  + now exists (lp1, lp2, l1,
                l ++ flat_map (fun '(p1,p2) => (app (map f l0) p2)) L,
                l1 ++ map f lp1 ++ l, L); list_simpl; repeat split; try reflexivity.
  + destruct (PermutationT_map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ HP Heq2)
      as [[L' l'] Hnil' [HeqL' HPL']].
    destruct (map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ _ Heq2) as [Lp HeqLp].
    destruct (map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (PermutationT Lp' Lp) as HPp
      by (rewrite HeqLp, HeqLp' in HPL'; apply (PermutationT_map_inv_inj Hinj _ _ HPL')).
    induction L' as [|(n', x) L' IHL'] using rev_rect;
      [ exfalso; apply Hnil'; [ intros Heqnil; destruct L1; inversion Heqnil | reflexivity ]
      | clear IHL' ].
    exists (Lp', Lp, l1, l2'' ++ flat_map (fun '(p1,p2) => (app (map f l0) p2)) L2,
            l1 ++ l', L' ++ (n' , x ++ l2'') :: L2); repeat split.
    * rewrite HeqL'. list_simpl. reflexivity.
    * assumption.
    * rewrite <- HeqLp'. list_simpl. reflexivity.
    * rewrite <- HeqLp. list_simpl. reflexivity.
  + destruct (PermutationT_map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ HP Heq2)
      as [[L' l'] Hnil' [HeqL' HPL']]; simpl in Hnil', HeqL', HPL'.
    destruct (map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ _ Heq2) as [Lp HeqLp].
    destruct (map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (PermutationT Lp' Lp) as HPp
      by (rewrite HeqLp, HeqLp' in HPL'; apply (PermutationT_map_inv_inj Hinj _ _ HPL')).
    exists (Lp', Lp, l1, flat_map (fun '(p1,p2) => (app (map f l0) p2)) L2, l1 ++ l', L' ++ L2);
      repeat split.
    * rewrite HeqL', flat_map_app. list_simpl. reflexivity.
    * assumption.
    * rewrite <- HeqLp', flat_map_app. list_simpl. reflexivity.
    * rewrite <- HeqLp, flat_map_app. list_simpl. reflexivity.
- decomp_app_eq_app_flat_map_cons_fun Heq2
    as [[[l' [_ ->] ->]|[((((L1', L2'), n'), l1''), l2'') [_ ->] [Heq2 ->]]]|[(L1', L2') -> [Heq2 ->]]].
  + exists (lp1, lp2,
            l ++ flat_map (fun '(p1,p2) => app (map f l0) p2) (L1 ++ (n , l1') :: nil),
            l' ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L2,
            l, L1 ++ (n , l1' ++ map f lp1 ++ l') :: L2); list_simpl; repeat split. assumption.
  + destruct (PermutationT_map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ HP Heq2)
      as [[L' l''] Hnil' [HeqL' HPL']].
    destruct (map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ _ Heq2) as [Lp HeqLp].
    destruct (map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (PermutationT Lp' Lp) as HPp
      by (rewrite HeqLp in HPL'; rewrite HeqLp' in HPL';
          apply (PermutationT_map_inv_inj Hinj _ _ HPL')).
    induction L' as [|(n'', x) L' IHL'] using rev_rect;
      [ exfalso; apply Hnil'; [ intro Heqnil; destruct L1'; inversion Heqnil | reflexivity ]
      | clear IHL' ].
    exists (Lp', Lp,
            l ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L1 ++ map f l0 ++ l1',
            l2'' ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L2',
            l, L1 ++ (n , l1' ++ l'') :: L' ++ (n'', x ++ l2'') :: L2'); repeat split; list_simpl.
    * rewrite HeqL'. list_simpl. reflexivity.
    * assumption.
    * rewrite <- HeqLp'. list_simpl. reflexivity.
    * rewrite <- HeqLp. list_simpl. reflexivity.
  + destruct (PermutationT_map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ HP Heq2)
      as [[L' l''] Hnil' [HeqL' HPL']].
    destruct (map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ _ Heq2) as [Lp HeqLp].
    destruct (map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (PermutationT Lp' Lp) as HPp
      by (rewrite HeqLp, HeqLp' in HPL'; apply (PermutationT_map_inv_inj Hinj _ _ HPL')).
    exists (Lp', Lp,
            l ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L1 ++ map f l0 ++ l1',
            flat_map (fun '(p1,p2) => app (map f l0) p2) L2',
            l, L1 ++ (n , l1' ++ l'') :: L' ++ L2'); repeat split; list_simpl.
    * rewrite HeqL'. list_simpl. reflexivity.
    * assumption.
    * rewrite <- HeqLp'. list_simpl. reflexivity.
    * rewrite <- HeqLp. list_simpl. reflexivity.
- decomp_app_eq_flat_map_cons_fun Heq2
    as [[((((L1', L2'), n), l1'), l2') [_ ->] [Heq1 ->]] | [(L1', L2') -> [Heq1 ->]]].
  + rewrite <- (app_nil_l (flat_map _ _)) in Heq1.
    destruct (PermutationT_map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ HP Heq1)
      as [[L' l''] Hnil' [HeqL' HPL']]. list_simpl in HPL'.
    destruct (map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ _ Heq1) as [Lp HeqLp]. list_simpl in HeqLp.
    destruct (map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (PermutationT Lp' Lp) as HPp
      by (rewrite HeqLp, HeqLp' in HPL'; apply (PermutationT_map_inv_inj Hinj _ _ HPL')).
    induction L' as [|(n', x) L' IHL'] using rev_rect;
      [ exfalso; apply Hnil'; [ intro Heqnil; destruct L1'; inversion Heqnil | reflexivity ]
      | clear IHL' ].
    induction L1 as [|(n0, x0) L1 IHL1] using rev_rect; [ | clear IHL1 ].
    * exists (Lp', Lp, l, l2' ++ flat_map (fun '(_, p2) => app (map f l0) p2) L2',
              l ++ l'', L' ++ (n', x ++ l2') :: L2'); repeat split; list_simpl.
      -- rewrite HeqL'. list_simpl. reflexivity.
      -- assumption.
      -- rewrite <- HeqLp'. list_simpl. reflexivity.
      -- rewrite <- HeqLp. list_simpl. reflexivity.
    * exists (Lp', Lp,
              l ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L1 ++ map f l0 ++ x0,
              l2' ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L2',
              l, L1 ++ (n0 , x0 ++ l'') :: L' ++ (n' , x ++ l2') :: L2'); repeat split; list_simpl.
      -- rewrite HeqL'. list_simpl. reflexivity.
      -- assumption.
      -- rewrite <- HeqLp'. list_simpl. reflexivity.
      -- rewrite <- HeqLp. list_simpl. reflexivity.
  + rewrite <- (app_nil_l (flat_map _ _)) in Heq1.
    destruct (PermutationT_map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ HP Heq1)
      as [[L' l''] Hnil' [HeqL' HPL']].
    destruct (map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ _ Heq1) as [Lp HeqLp] ; list_simpl in HeqLp.
    destruct (map_eq_app_flat_map_cons_fun_inv _ f l0 _ _ _ HeqL') as [Lp' HeqLp'].
    assert (PermutationT Lp' Lp) as HPp
      by (rewrite HeqLp, HeqLp' in HPL'; apply (PermutationT_map_inv_inj Hinj _ _ HPL')).
    induction L1 as [|(n', x) L1 IHL1] using rev_rect; [ | clear IHL1 ].
    * exists (Lp', Lp, l, flat_map (fun '(p1,p2) => app (map f l0) p2) L2', l ++ l'', L' ++ L2');
        repeat split; list_simpl.
      -- rewrite HeqL'. list_simpl. reflexivity.
      -- assumption.
      -- rewrite <- HeqLp'. list_simpl. reflexivity.
      -- rewrite <- HeqLp. list_simpl. reflexivity.
    * exists (Lp', Lp,
              l ++ flat_map (fun '(p1,p2) => app (map f l0) p2) L1 ++ map f l0 ++ x,
              flat_map (fun '(p1,p2) => app (map f l0) p2) L2',
              l, L1 ++ (n', x ++ l'') :: L' ++ L2'); repeat split; list_simpl.
      -- rewrite HeqL'. list_simpl. reflexivity.
      -- assumption.
      -- rewrite <- HeqLp'. list_simpl. reflexivity.
      -- rewrite <- HeqLp. list_simpl. reflexivity.
Qed.

Lemma CPermutationT_app_flat_map_cons_fun_inv B T (f : B -> T) lw0 L lw l :
  CPermutationT lw (l ++ flat_map (fun '(p1,p2) => f p1 :: p2) L) ->
  {'(L', lw') & L <> nil -> L' <> nil &
           prod (lw = lw' ++ flat_map (fun '(p1,p2) => f p1 :: p2) L')
                (CPermutationT (lw' ++ flat_map (fun '(p1,p2) => app lw0 p2) L')
                                   (l ++ flat_map (fun '(p1,p2) => app lw0 p2) L)) }.
Proof.
intros HC; inversion HC as [l1 l2 Heq1 Heq2]; subst.
decomp_app_eq_app Heq2 as [[l0 <- ->]|[l0 -> Heq1]].
- induction L as [|[n l] L IHL] using rev_rect; [ | clear IHL ]; cbn.
  + now exists (nil, l0 ++ l2); rewrite ? app_nil_r.
  + exists (L ++ (n, l ++ l2) :: nil, l0); simpl; repeat split.
    * intros _ Heqnil. destruct L; discriminate Heqnil.
    * now rewrite 2 flat_map_app; simpl; rewrite ? app_nil_r, <- ? app_assoc, <- app_comm_cons.
    * rewrite 2 flat_map_app; simpl.
      rewrite <- ? app_assoc, ? app_nil_r, 3 app_assoc, <- (app_assoc l0), <- 2 (app_assoc _ _ l);
      constructor.
- decomp_app_eq_flat_map_cons_fun Heq1
    as [[((((L1, L2), n), l1'), l2') [_ ->] [-> ->]] | [(L1, L2) -> [Heq1 ->]]];
    (induction L2 as [|[n' l'] L2 IHL2] using rev_rect; [ | clear IHL2 ]); cbn; subst.
  + exists (L1 ++ (n, l1') :: nil, l2' ++ l); simpl; rewrite ? app_nil_r; repeat split.
    * intros _ Heqnil. destruct L1; discriminate Heqnil.
    * now rewrite <- app_assoc.
    * rewrite 2 flat_map_app; simpl; rewrite <- app_assoc, ? app_nil_r ; symmetry.
      rewrite 3 app_assoc, <- (app_assoc l), <- 2 (app_assoc _ _ l1'); constructor.
  + exists (L2 ++ (n' , l' ++ l) :: L1 ++ (n , l1') :: nil, l2'); simpl; repeat split.
    * intros _ Heqnil. destruct L2; discriminate Heqnil.
    * now rewrite ? flat_map_app; cbn; rewrite flat_map_app; cbn;
        rewrite ? app_nil_r, <- ? app_assoc.
    * rewrite 2 flat_map_app; simpl; rewrite 2 flat_map_app; cbn;
           rewrite ? app_nil_r, <- ? app_assoc, 3 app_assoc,
                   <- (app_assoc l2'), <- 2 (app_assoc _ _ l').
      now etransitivity ; [ apply cpermT | ]; rewrite <- ? app_assoc.
  + now exists (L1, l); cbn; rewrite ? app_nil_r.
  + exists (L2 ++ (n', l' ++ l) :: L1, nil); repeat split.
    * intros _ Heqnil. destruct L2; discriminate Heqnil.
    * now rewrite ? flat_map_app, <- ? app_assoc; simpl; 
      rewrite ? app_nil_r, <- ? app_comm_cons, <- app_assoc.
    * rewrite 2 flat_map_app; cbn; rewrite flat_map_app; cbn; rewrite (app_assoc l).
      now etransitivity; [ | apply cpermT ]; rewrite <- ? app_assoc.
Qed.

Lemma PCPermutationT_app_flat_map_cons_fun_inv b B T (f : B -> T) lw0 L lw l :
  PCPermutationT b lw (l ++ flat_map (fun '(p1,p2) => f p1 :: p2) L) ->
  {'(L', lw') & L <> nil -> L' <> nil &
           prod (lw = lw' ++ flat_map (fun '(p1,p2) => f p1 :: p2) L')
                (PCPermutationT b (lw' ++ flat_map (fun '(p1,p2) => app lw0 p2) L')
                                      (l ++ flat_map (fun '(p1,p2) => app lw0 p2) L)) }.
Proof.
destruct b; [ apply PermutationT_app_flat_map_cons_fun_inv
            | apply CPermutationT_app_flat_map_cons_fun_inv ].
Qed.


Lemma app_eq_flat_map_cons_dichot T (A : T) L l1 l2 :
  l1 ++ l2 = flat_map (cons A) L ->
      {'(L1, L2, l3, l4) | l4 <> nil /\ L = L1 ++ (l3 ++ l4) :: L2
           & l1 = flat_map (cons A) (L1 ++ l3 :: nil)
          /\ l2 = l4 ++ flat_map (cons A) L2 }
    + {'(L1, L2) | L = L1 ++ L2
           & l1 = flat_map (cons A) L1
          /\ l2 = flat_map (cons A) L2 }.
Proof.
intro Heq.
destruct (@app_eq_flat_map_cons_fun_dichot _ _ (fun (p : nat) => A) (map (fun x => (1 , x)) L) l1 l2)
  as [[((((L1, L2), n), l3), l4) [H1 H2] [-> H4]]|[(L1, L2) H1 [-> ->]]].
{ rewrite Heq. clear. induction L as [|? ? IHL]; [| cbn; rewrite IHL ]; reflexivity. }
- left. exists (map snd L1, map snd L2, l3, l4); repeat split; [ assumption | .. ].
  + clear - H2. induction L1 as [|? ? IHL1] in L, H2 |- *; cbn; destruct L as [|l0 L]; inversion H2; cbn.
    * replace (map snd (map (fun x => (1, x)) L)) with L; auto.
      clear. induction L as [|? ? IHL]; [ | cbn; rewrite <- IHL ]; reflexivity.
    * now rewrite (IHL1 L).
  + clear. induction L1 as [|(m, l) ? ?]; [ reflexivity | ].
    cbn. f_equal. f_equal. assumption.
  + replace (flat_map (cons A) (map snd L2)) with (flat_map (fun '(p1,p2) => A :: p2) L2); [ assumption | ].
    clear. induction L2 as [|(m, l) ? ?]; [ reflexivity | ].
    cbn. f_equal. f_equal. assumption.
- right.
  exists (map snd L1, map snd L2); repeat split.
  + clear - H1. induction L1 as [|? ? IHL1] in L, H1 |- *.
    * cbn. cbn in H1. rewrite <- H1.
      clear. induction L as [|? ? IHL]; [ | cbn; rewrite <- IHL ]; reflexivity.
    * destruct L as [|? L]; inversion H1; cbn.
      now rewrite (IHL1 L).
  + clear. induction L1 as [|(m, l) ? ?]; [ reflexivity | ].
    cbn. f_equal. f_equal. assumption.
  + clear. induction L2 as [|(m, l) ? ?]; [ reflexivity | ].
    cbn. f_equal. f_equal. assumption.
Qed.

#[local] Ltac decomp_app_eq_flat_map_cons_core H p :=
  match type of H with
  | ?lh ++ ?lr = flat_map (cons ?A) ?L => apply app_eq_flat_map_cons_dichot in H as p
  end.
Tactic Notation "decomp_app_eq_flat_map_cons" hyp(H) "as" simple_intropattern(p) :=
  decomp_app_eq_flat_map_cons_core H p.
Tactic Notation "decomp_app_eq_flat_map_cons" hyp(H) :=
  let l1 := fresh "l" in
  let l2 := fresh "l" in
  let L1 := fresh "L" in
  let L2 := fresh "L" in
  let Hnil := fresh "Hnil" in
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  decomp_app_eq_flat_map_cons_core H ipattern:([[(((L1,L2), l1), l2) [Hnil H1] [H2 H3]]
                                            |[(L1, L2) H1 [H2 H3]]]);
  subst.

Lemma app_eq_app_flat_map_cons_trichot T (A : T) l0 L l1 l2 :
  l1 ++ l2 = l0 ++ flat_map (cons A) L ->
      { l' | l' <> nil /\ l0 = l1 ++ l'
           & l2 = l' ++ flat_map (cons A) L }
    + {'(L1, L2, l3, l4) | l4 <> nil /\ L = L1 ++ (l3 ++ l4) :: L2
           & l1 = l0 ++ flat_map (cons A) (L1 ++ l3 :: nil)
          /\ l2 = l4 ++ flat_map (cons A) L2 }
    + {'(L1, L2) | L = L1 ++ L2
           & l1 = l0 ++ flat_map (cons A) L1
          /\ l2 = flat_map (cons A) L2 }.
Proof.
intro Heq. decomp_app_eq_app Heq as [[l <- ->]|[l -> Heq1]].
- destruct l as [|t l]; subst.
  + right. exists (nil, L); list_simpl; repeat split.
  + left. left. exists (t :: l); repeat split. intros [=].
- decomp_app_eq_flat_map_cons Heq1 as [[(((L1,L2), l1'), l2') [Hnil ->] [-> ->]] |[(L1, L2) -> [-> ->]]].
  + left. right. exists (L1, L2, l1', l2'); repeat split. assumption.
  + right. exists (L1, L2); repeat split.
Qed.

#[local] Ltac decomp_app_eq_app_flat_map_cons_core H p :=
  match type of H with
  | ?lh ++ ?lr = ?l0 ++ flat_map (cons ?A) ?L => apply app_eq_app_flat_map_cons_trichot in H as p
  end.
Tactic Notation "decomp_app_eq_app_flat_map_cons" hyp(H) "as" simple_intropattern(p) :=
  decomp_app_eq_app_flat_map_cons_core H p.
Tactic Notation "decomp_app_eq_app_flat_map_cons" hyp(H) :=
  let l1 := fresh "l" in
  let l2 := fresh "l" in
  let L1 := fresh "L" in
  let L2 := fresh "L" in
  let Hnil := fresh "Hnil" in
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  decomp_app_eq_app_flat_map_cons_core H ipattern:([[[l1 [Hnil H1] H2]
                                                   | [(((L1, L2), l1), l2) [Hnil H1] [H2 H3]]]
                                                   | [(L1, L2) H1 [H2 H3]]]);
  subst.

Lemma elt_eq_app_flat_map_cons_trichot T (A : T) l0 L l1 l2 B :
  l1 ++ B :: l2 = l0 ++ flat_map (cons A) L ->
      { l' | l0 = l1 ++ B :: l'
           & l2 = l' ++ flat_map (cons A) L }
    + {'(L1, L2, l1', l2') | L = L1 ++ (l1' ++ B :: l2') :: L2
           & l1 = l0 ++ flat_map (cons A) L1 ++ (A :: l1')
          /\ l2 = l2' ++ flat_map (cons A) L2 }
    + {'(L1, L2, l) | B = A /\ L = L1 ++ l :: L2
           & l1 = l0 ++ flat_map (cons A) L1
          /\ l2 = l ++ flat_map (cons A) L2 }.
Proof.
intro Heq. decomp_elt_eq_app Heq as [[l <- ->]|[l -> Heq1]];
  [ left; left; exists l; repeat split | ].
induction L as [|l' L IHL] in l, l2, Heq1 |- *; cbn in Heq1.
- exfalso. decomp_nil_eq Heq1.
- rewrite app_comm_cons in Heq1.
  decomp_elt_eq_app Heq1 as [[l1 Heq0 ->]|[l1 -> Heq2]].
  + destruct l as [|t l]; destr_eq Heq0; subst.
    * right. exists (nil, L, l'); repeat split.
    * left. right. exists (nil, L , l, l1); repeat split.
  + apply IHL in Heq2 as [[[l'' Heqa _]
                       | [(((L', L''), l''), l''') -> [->%app_inv_head ->]]]
                       | [((L', L''), l'') [-> ->] [->%app_inv_head ->]]].
    * exfalso.
      rewrite <- (app_nil_r l0) in Heqa. rewrite <- 2 app_assoc in Heqa. apply app_inv_head in Heqa.
      cbn in Heqa. decomp_nil_eq Heqa.
    * left. right. exists (l' :: L', L'', l'', l'''); list_simpl; repeat split.
    * right. exists (l' :: L', L'', l''); repeat split.
Qed.

#[local] Ltac decomp_elt_eq_app_flat_map_cons_core H p :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l0 ++ flat_map (cons ?A) ?L => apply elt_eq_app_flat_map_cons_trichot in H as p
  end.
Tactic Notation "decomp_elt_eq_app_flat_map_cons" hyp(H) "as" simple_intropattern(p) :=
  decomp_elt_eq_app_flat_map_cons_core H p.
Tactic Notation "decomp_elt_eq_app_flat_map_cons" hyp(H) :=
  let l1 := fresh "l" in
  let l2 := fresh "l" in
  let L1 := fresh "L" in
  let L2 := fresh "L" in
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  let Heq := fresh "Heq" in
  decomp_elt_eq_app_flat_map_cons_core H ipattern:([[[l1 H1 H2]
                                                   | [(((L1, L2), l1), l2) H1 [H2 H3]]]
                                                   | [((L1, L2), l1) [Heq H1] [H2 H3]]]);
    [ | | try now inversion Heq ]; subst.

Lemma map_eq_app_flat_map_cons_inv T T1 (A : T1) (f : T -> T1) lw' lw l L :
  map f lw = l ++ flat_map (cons A) L ->
  { Lw | l ++ flat_map (app (map f lw')) L = map f Lw }.
Proof.
induction L as [|l0 L IHL] in lw, l |- *; cbn; intro Heq.
- exists lw. symmetry. assumption.
- rewrite app_comm_cons, app_assoc in Heq.
  apply IHL in Heq as [Lw Heq].
  remember (flat_map (app (map f lw')) L) as L0.
  decomp_map_eq Heq eqn:Hf. subst Lw. rewrite <- Hf.
  exists (l ++ (lw' ++ l0) ++ L0). rewrite ! map_app. reflexivity.
Qed.

Lemma PermutationT_app_flat_map_cons_inv T (A : T) lw0 L lw l :
  PermutationT lw (l ++ flat_map (cons A) L) ->
  {'(L', lw') & L <> nil -> L' <> nil &
          prod (lw = lw' ++ flat_map (cons A) L')
               (PermutationT (lw' ++ flat_map (app lw0) L')
                                 (l ++ flat_map (app lw0) L)) }.
Proof.
intro HP.
destruct (@PermutationT_app_flat_map_cons_fun_inv _ _ (fun _ => A) lw0 (map (fun p => (1, p)) L) lw l)
  as [(L', lw') H1 [H2 H3]].
{ replace (flat_map (fun '(p1,p2) => A :: p2)
                    (map (fun p => (1,p)) L)) with (flat_map (cons A) L)
    by (clear; induction L as [|? ? IHL]; [ | cbn; rewrite IHL ]; reflexivity).
  assumption. }
split with (map snd L', lw'); repeat split.
- intros Hneq ->%map_eq_nil.
  apply H1; [ | reflexivity ].
  intros ->%map_eq_nil. apply Hneq. reflexivity.
- replace (flat_map (cons A) (map snd L')) with (flat_map (fun '(_, p2) => A :: p2) L')
    by (clear; induction L' as [|[] L' IHL']; [ | cbn; rewrite IHL']; reflexivity).
  assumption.
- replace (flat_map (app lw0) (map snd L')) with (flat_map (fun '(_, p2) => lw0 ++ p2) L')
    by (clear; induction L' as [|[] L' IHL']; [ | cbn; rewrite IHL']; reflexivity).
  replace (flat_map (app lw0) L)
     with (flat_map (fun '(_, p2) => lw0 ++ p2) (map (fun p => (1, p)) L))
       by (clear; induction L as [|? ? IHL]; [ | cbn; rewrite IHL ]; reflexivity).
  assumption.
Qed.

Lemma PermutationT_map_eq_app_flat_map_cons_inv T T1 (A : T1) (f : T -> T1) lw0 L lw lw' l :
  PermutationT lw lw' -> map f lw' = l ++ flat_map (cons A) L ->
  {'(L' , lw') & L <> nil -> L' <> nil &
            prod (map f lw = lw' ++ flat_map (cons A) L')
                 (PermutationT (lw' ++ flat_map (app (map f lw0)) L')
                                   (l ++ flat_map (app (map f lw0)) L)) }.
Proof.
intros HP%(PermutationT_map f) Heq.
apply PermutationT_app_flat_map_cons_inv.
rewrite <- Heq. assumption.
Qed.

Lemma PermutationT_app_map_app_eq_app_flat_map_cons_inv T T1 (A : T1) (f : T -> T1)
  (Hinj : injective f) l0 l1 l2 lp1 lp2 l L :
  PermutationT lp1 lp2 ->
  l1 ++ map f lp2 ++ l2 = l ++ flat_map (cons A) L ->
  {'(l1', l2', l3', l4', l', L')  &  l1 ++ map f lp1 ++ l2 = l' ++ flat_map (cons A) L'
            & prod (PermutationT l1' l2')
             (prod (l3' ++ map f l1' ++ l4' = l' ++ flat_map (app (map f l0)) L')
                   (l3' ++ map f l2' ++ l4' = l ++ flat_map (app (map f l0)) L)) }.
Proof.
intros HP Heq.
destruct (@PermutationT_app_map_app_eq_app_flat_map_cons_fun_inv _ _ _ (fun _ => A)
            f Hinj l0 l1 l2 lp1 lp2 l (map (fun p => (1 , p)) L))
  as [[[[[[l1' l2'] l3'] l4'] l'] L'] [H1 [H2 [H3 H4]]]]; [ assumption | | ].
{ replace (flat_map (fun '(p1, p2) => A :: p2) (map (fun p => (1, p)) L))
     with (flat_map (cons A) L)
  by (clear; induction L as [|? ? IHL]; [ | cbn; rewrite IHL]; reflexivity).
  assumption. }
split with (l1', l2', l3', l4', l', map snd L'); repeat split; [ | assumption | | ].
- replace (flat_map (cons A) (map snd L'))
     with (flat_map (fun '(_, p2) => A :: p2) L')
    by (clear; induction L' as [|[] L' IHL']; [ | cbn; rewrite IHL']; reflexivity).
  assumption.
- replace (flat_map (app (map f l0)) (map snd L'))
     with (flat_map (fun '(_, p2) => map f l0 ++ p2) L')
    by (clear; induction L' as [|[] L' IHL']; [ | cbn; rewrite IHL']; reflexivity).
  assumption.
- replace (flat_map (app (map f l0)) L)
     with (flat_map (fun '(_, p2) => map f l0 ++ p2) (map (fun p  => (1, p)) L))
    by (clear; induction L as [|? ? IHL]; [ | cbn; rewrite IHL]; reflexivity).
  assumption.
Qed.

Lemma CPermutationT_app_flat_map_cons_inv T (A : T) lw0 L lw l :
  CPermutationT lw (l ++ flat_map (cons A) L) ->
  {'(L', lw') & L <> nil -> L' <> nil &
          prod (lw = lw' ++ flat_map (cons A) L')
               (CPermutationT (lw' ++ flat_map (app lw0) L')
                                  (l ++ flat_map (app lw0) L)) }.
Proof.
intro HC.
destruct (@CPermutationT_app_flat_map_cons_fun_inv _ _ (fun p => A) lw0 (map (fun x => (1 , x)) L) lw l)
  as [[L' lw'] H1 [H2 H3]].
{ replace (flat_map (fun '(_, p2) => A :: p2) (map (fun x => (1, x)) L))
     with (flat_map (cons A) L)
    by (clear; induction L as [|[] L IHL]; [ | cbn; rewrite IHL .. ]; reflexivity).
  assumption. }
split with (map snd L' , lw'); repeat split.
- intros Hneq ->%map_eq_nil.
  apply H1; [ | reflexivity ].
  intros ->%map_eq_nil.
  apply Hneq. reflexivity.
- replace (flat_map (cons A) (map snd L'))
     with (flat_map (fun '(_, p2) => A :: p2) L')
    by (clear; induction L' as [|[] L' IHL']; [ | cbn; rewrite IHL']; reflexivity).
  assumption.
- replace (flat_map (app lw0) (map snd L'))
     with (flat_map (fun '(_, p2) => lw0 ++ p2) L')
    by (clear; induction L' as [|[] L' IHL']; [ | cbn; rewrite IHL']; reflexivity).
  replace (flat_map (app lw0) L)
    with (flat_map (fun '(_, p2) => lw0 ++ p2) (map (fun x => (1, x)) L))
    by (clear; induction L as [|? ? IHL]; [ | cbn; rewrite IHL ]; reflexivity).
  assumption.
Qed.
