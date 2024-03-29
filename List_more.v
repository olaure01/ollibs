(** Add-ons for List library
Usefull tactics and properties apparently missing in the List library. *)

From Coq Require Import PeanoNat.
From Coq Require Export List.
From OLlibs Require Import Datatypes_more Bool_more.
From OLlibs Require Export List_Type.
Import EqNotations.

Set Implicit Arguments.


(** misc *)

(* TODO included in PR #11966 submitted, remove once merged and released *)

    Lemma rev_case A (l : list A) : l = nil \/ exists a tl, l = tl ++ a :: nil.
    Proof. induction l as [|a l] using rev_ind; [ left | right; exists a, l ]; reflexivity. Qed.

(* case analysis similar to [destruct l] but splitting at the end of the list in the spirit of [rev_ind] *)

Inductive last_list_internal A : list A -> Type :=
| last_list_nil_internal : last_list_internal nil
| last_list_last_internal : forall a l, last_list_internal (l ++ a :: nil).

Lemma last_case_internal A (l : list A) : last_list_internal l.
Proof. induction l as [|a l] using rev_rect; constructor. Qed.

Tactic Notation "last_destruct" constr(l) :=
  destruct (last_case_internal l).
Tactic Notation "last_destruct" constr(l) "as" simple_intropattern(p) :=
  destruct (last_case_internal l) as p.


(** * Tactics *)

(** ** Simplification in lists *)

Ltac list_simpl :=
  repeat (
    repeat simpl;
    rewrite <- ? app_assoc, <- ? app_comm_cons, ? app_nil_r;
    rewrite <- ? map_rev, ? rev_involutive, ? rev_app_distr, ? rev_unit;
    rewrite ? map_app, ? flat_map_app).
Ltac list_simpl_hyp H :=
  repeat (
    repeat simpl in H;
    rewrite <- ? app_assoc, <- ? app_comm_cons, ? app_nil_r in H;
    rewrite <- ? map_rev, ? rev_involutive, ? rev_app_distr, ? rev_unit in H;
    rewrite ? map_app, ? flat_map_app in H).
Tactic Notation "list_simpl" "in" hyp(H) := list_simpl_hyp H.
Ltac list_simpl_hyps :=
  match goal with
  | H : _ |- _ => list_simpl in H; revert H; list_simpl_hyps; intro H
  | _ => idtac
  end.
Ltac list_simpl_all := list_simpl_hyps; list_simpl.


(** ** Removal of [cons] constructions *)

Lemma cons_is_app A (x:A) l : x :: l = (x :: nil) ++ l.
Proof. reflexivity. Qed.

Ltac cons2app :=
  repeat
  match goal with
  | |- context [ cons ?x ?l ] =>
         lazymatch l with
         | nil => fail
         | _ => rewrite (cons_is_app x l)
           (* one could prefer
                 change (cons x l) with (app (cons x nil) l)
              which leads to simpler generated term
              but does not work with existential variables *)
         end
  end.
Ltac cons2app_hyp H :=
  repeat
  match type of H with
  | context [ cons ?x ?l ]  =>
      lazymatch l with
      | nil => fail
      | _ =>  rewrite (cons_is_app x l) in H
           (* one could prefer
                 change (cons x l) with (app (cons x nil) l) in H
              which leads to simpler generated term
              but does not work with existential variables *)
      end
  end.
Tactic Notation "cons2app" "in" hyp(H) := cons2app_hyp H.
Ltac cons2app_hyps :=
  match goal with
  | H : _ |- _ => cons2app in H; revert H; cons2app_hyps; intro H
  | _ => idtac
  end.
Ltac cons2app_all := cons2app_hyps; cons2app.


(** ** Decomposition of lists and [list] equalities *)

Lemma decomp_length_add A (l : list A) n m : length l = n + m ->
  {'(l1, l2) | length l1 = n /\ length l2 = m & l = l1 ++ l2 }.
Proof.
induction n as [| n IHn] in l, m |- *; intro Heq.
- now split with (nil, l).
- destruct l as [|a l]; inversion Heq as [Heq2].
  specialize (IHn l m Heq2) as [(l1, l2) [<- <-] ->].
  split with (a :: l1, l2); [ split | ]; reflexivity.
Qed.

Ltac nil_vs_elt_inv H :=
  match type of H with
  | nil = ?l1 ++ ?x :: ?l2 => destruct l1; discriminate H
  end.

Ltac unit_vs_elt_inv H := 
  match type of H with
  | ?a :: nil = ?l1 ++ ?x :: ?l2 =>
      let Hnil1 := fresh in
      let Hnil2 := fresh in
      symmetry in H; apply elt_eq_unit in H as [H [Hnil1 Hnil2]];
      (try subst x); (try subst a); rewrite ? Hnil1, ? Hnil2 in *;
      clear Hnil1 Hnil2; (try clear l1); (try clear l2)
  end.

(* TODO compare with [List.app_eq_app] *)
Lemma dichot_app A (l1 l2 l3 l4 : list A) : l1 ++ l2 = l3 ++ l4 ->
     (exists l2', l1 ++ l2' = l3 /\ l2 = l2' ++ l4)
  \/ (exists l4', l1 = l3 ++ l4' /\ l4' ++ l2 = l4).
Proof.
revert l2 l3 l4;induction l1 as [|a l1 IHl1]; intros l2 l3; induction l3 as [|b l3 IHl3];
  intros ? Heq; simpl in Heq; inversion Heq as [[Heq'' Heq']]; subst.
- now right; exists (@nil A).
- now left; exists (b :: l3).
- now right; exists (a :: l1).
- destruct (IHl1 _ _ _ Heq') as [[l2' [<- H2'2]] | [l4' [-> H4'2]]].
  + now left; exists l2'.
  + now right; exists l4'.
Qed.

Ltac dichot_app_exec H :=
  match type of H with
  | _ ++ _ = _ ++ _ => apply dichot_app in H;
                         let l2 := fresh "l" in
                         let l4 := fresh "l" in
                         let H1 := fresh H in
                         let H2 := fresh H in
                         destruct H as [[l2 [H1 H2]] | [l4 [H1 H2]]]
  end.

Lemma dichot_elt_app A l1 (a : A) l2 l3 l4 : l1 ++ a :: l2 = l3 ++ l4 ->
     (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ l4)
  \/ (exists l4', l1 = l3 ++ l4' /\ l4' ++ a :: l2 = l4).
Proof.
revert l2 l3 l4; induction l1 as [|b l1 IHl1]; intros l2 l3; induction l3 as [|c l3 IHl3];
  intros ? Heq; simpl in Heq; inversion Heq as [[Heq'' Heq']]; subst.
- now right; exists (@nil A).
- now left; exists l3.
- now right; exists (b :: l1).
- destruct (IHl1 _ _ _ Heq') as [[l2' [<- H2'2]] | [l4' [-> H4'2]]].
  + now left; exists l2'.
  + now right; exists l4'.
Qed.

Ltac dichot_elt_app_exec H :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ => apply dichot_elt_app in H;
                              let l2 := fresh "l" in
                              let l4 := fresh "l" in
                              let H1 := fresh H in
                              let H2 := fresh H in
                              destruct H as [[l2 [H1 H2]] | [l4 [H1 H2]]]
  | _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H; apply dichot_elt_app in H;
                              let l2 := fresh "l" in
                              let l4 := fresh "l" in
                              let H1 := fresh H in
                              let H2 := fresh H in
                              destruct H as [[l2 [H1 H2]] | [l4 [H1 H2]]]
  end.

Lemma trichot_elt_app A l1 (a : A) l2 l3 l4 l5 : l1 ++ a :: l2 = l3 ++ l4 ++ l5 ->
      (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ l4 ++ l5)
   \/ (exists l2' l2'', l1 = l3 ++ l2' /\ l2' ++ a :: l2'' = l4 /\ l2 = l2'' ++ l5)
   \/ (exists l5', l1 = l3 ++ l4 ++ l5' /\ l5' ++ a :: l2 = l5).
Proof.
revert l2 l3 l4 l5; induction l1 as [|b l1 IHl1]; intros l2 l3; induction l3 as [|c l3 IHl3];
  intros l4 l5 Heq; simpl in Heq; inversion Heq as [[Heq' Heq'']]; subst.
- destruct l4 as [| a' l4]; inversion Heq'.
  + now right; right; exists nil.
  + now right; left; exists nil, l4.
- now left; exists l3.
- destruct l4 as [| a' l4]; inversion Heq' as [[Heq1 Heq2]].
  + now right; right; exists (b :: l1).
  + dichot_elt_app_exec Heq2; subst.
    * now right; left; exists (a' :: l1), l.
    * now right; right; exists l0.
- destruct (IHl1 _ _ _ _ Heq'')
    as [(l' & <- & ->) | [ (l2' & l2'' & -> & <- & ->) | (l' & -> & <-) ]].
  + now left; exists l'.
  + now right; left; exists l2', l2''.
  + now right; right; exists l'.
Qed.

Ltac trichot_elt_app_exec H :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ ++ _ => apply trichot_elt_app in H;
                                   let l2 := fresh "l" in
                                   let l4 := fresh "l" in
                                   let H1 := fresh H in
                                   let H2 := fresh H in
                                   destruct H as [ (l2 & H1 & H2)
                                                 | [ (l2 & l4 & H1 & H2) | (l4 & H1 & H2) ]]
  | _ ++ _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H; apply trichot_elt_app in H;
                                   let l2 := fresh "l" in
                                   let l4 := fresh "l" in
                                   let H1 := fresh H in
                                   let H2 := fresh H in
                                   destruct H as [ (l2 & H1 & H2)
                                                 | [ (l2 & l4 & H1 & H2) | (l4 & H1 & H2) ]]
  end.

Lemma trichot_elt_elt A l1 (a : A) l2 l3 b l4 : l1 ++ a :: l2 = l3 ++ b :: l4 ->
      (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ b :: l4)
   \/ (l1 = l3 /\ a = b /\ l2 = l4)
   \/ (exists l4', l1 = l3 ++ b :: l4' /\ l4' ++ a :: l2 = l4).
Proof.
intro Heq. change (b :: l4) with ((b :: nil) ++ l4) in Heq.
apply trichot_elt_app in Heq;
  destruct Heq as [ | [ (l2' & l2'' & H'1 & H'2 & H'3) | ]]; subst;
  [ left | right; left | right; right ]; auto.
now destruct l2' as [|a' l2']; inversion H'2 as [[H1 H2]];
 subst; [ | destruct l2'; inversion H2 ]; list_simpl.
Qed.

Ltac trichot_elt_elt_exec H :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l1 ++ ?x :: ?l2 =>
      apply trichot_elt_elt in H ;
        let l' := fresh "l" in
        let H1 := fresh H in
        let H2 := fresh H in
        let H3 := fresh H in
        destruct H as [(l' & H1 & H2) | [(H1 & H2 & H3) | (l' & H1 & H2)]] ;
        [ (try subst l1); (try subst lr)
        | (try subst x); (try subst l1); (try subst l2)
        | (try subst l2); (try subst lh) ]
  end.

Lemma dichot_app_inf A (l1 l2 l3 l4 : list A) : l1 ++ l2 = l3 ++ l4 ->
     { l2' | l1 ++ l2' = l3 & l2 = l2' ++ l4 }
   + { l4' | l1 = l3 ++ l4' & l4' ++ l2 = l4 }.
Proof.
induction l1 as [|b l1 IHl1] in l2, l3, l4 |- *; induction l3 as [|c l3 IHl3] in l4 |- *;
  cbn; intro Heq; inversion Heq as [[Heq'' Heq']]; subst.
- now right; exists (@nil A).
- now left; exists (c :: l3).
- now right; exists (b :: l1).
- destruct (IHl1 _ _ _ Heq') as [[l2' <- H2'2] | [l4' -> H4'2]].
  + now left; exists l2'.
  + now right; exists l4'.
Qed.

Ltac dichot_app_inf_exec H :=
  match type of H with
  | _ ++ _ = _ ++ _ => apply dichot_app_inf in H;
                         let l2 := fresh "l" in
                         let l4 := fresh "l" in
                         let H1 := fresh H in
                         let H2 := fresh H in
                         destruct H as [[l2 H1 H2] | [l4 H1 H2]]
  end.

Lemma dichot_elt_app_inf A l1 (a : A) l2 l3 l4 : l1 ++ a :: l2 = l3 ++ l4 ->
     { l2' | l1 ++ a :: l2' = l3 & l2 = l2' ++ l4 }
   + { l4' | l1 = l3 ++ l4' & l4' ++ a :: l2 = l4 }.
Proof.
induction l1 as [|b l1 IHl1] in l2, l3, l4 |- *; induction l3 as [|c l3 IHl3] in l4 |- *;
  cbn; intro Heq; inversion Heq as [[Heq'' Heq']]; subst.
- now right; exists (@nil A).
- now left; exists l3.
- now right; exists (b :: l1).
- destruct (IHl1 _ _ _ Heq') as [[l2' <- H2'2] | [l4' -> H4'2]].
  + now left; exists l2'.
  + now right; exists l4'.
Qed.

Ltac dichot_elt_app_inf_exec H :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ => apply dichot_elt_app_inf in H;
                              let l2 := fresh "l" in
                              let l4 := fresh "l" in
                              let H1 := fresh H in
                              let H2 := fresh H in
                              destruct H as [[l2 H1 H2] | [l4 H1 H2]]
  | _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H; apply dichot_elt_app_inf in H;
                              let l2 := fresh "l" in
                              let l4 := fresh "l" in
                              let H1 := fresh H in
                              let H2 := fresh H in
                              destruct H as [[l2 H1 H2] | [l4 H1 H2]]
  end.

Lemma trichot_elt_app_inf A l1 (a : A) l2 l3 l4 l5 : l1 ++ a :: l2 = l3 ++ l4 ++ l5 ->
     { l2' | l1 ++ a :: l2' = l3 & l2 = l2' ++ l4 ++ l5 }
   + {'(l3', l4') | l1 = l3 ++ l3' & l3' ++ a :: l4' = l4 /\ l2 = l4' ++ l5 }
   + { l5' | l1 = l3 ++ l4 ++ l5' & l5' ++ a :: l2 = l5 }.
Proof.
induction l1 as [|b l1 IHl1] in l2, l3, l4, l5 |- *; induction l3 as [|c l3 IHl3] in l4, l5 |- *;
  cbn; intro Heq; inversion Heq as [[Heq' Heq'']]; subst.
- destruct l4 as [| a' l4]; inversion Heq'.
  + now right; exists nil.
  + now left; right; exists (nil, l4).
- now left; left; exists l3.
- destruct l4 as [| a' l4]; inversion Heq' as [[Heq1 Heq2]].
  + now right; exists (b :: l1).
  + dichot_elt_app_inf_exec Heq2; subst.
    * now left; right; exists (a' :: l1, l).
    * now right; exists l0.
- destruct (IHl1 _ _ _ _ Heq'') as [ [[l' <- ->] | [(l2', l2'') -> [<- ->]]] | [l' -> <-] ].
  + now left; left; exists l'.
  + now left; right; exists (l2', l2'').
  + now right; exists l'.
Qed.

Ltac trichot_elt_app_inf_exec H :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ ++ _ => apply trichot_elt_app_inf in H;
                                   let l2 := fresh "l" in
                                   let l4 := fresh "l" in
                                   let H1 := fresh H in
                                   let H2 := fresh H in
                                   let H3 := fresh H in
                                   destruct H as [ [ [l2 H1 H2] | [[l2 l4] H1 [H2 H3]] ] | [l4 H1 H2] ];
                                   simpl in H1; simpl in H2; try simpl in H3
  | _ ++ _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H; apply trichot_elt_app_inf in H;
                                   let l2 := fresh "l" in
                                   let l4 := fresh "l" in
                                   let H1 := fresh H in
                                   let H2 := fresh H in
                                   destruct H as [ [ [l2 H1 H2] | [[l2 l4] H1 [H2 H3]] ] | [l4 H1 H2] ];
                                   simpl in H1; simpl in H2; try simpl in H3
  end.

Lemma trichot_elt_elt_inf A l1 (a : A) l2 l3 b l4 : l1 ++ a :: l2 = l3 ++ b :: l4 ->
     { l2' | l1 ++ a :: l2' = l3 & l2 = l2' ++ b :: l4 }
   + { l1 = l3 /\ a = b /\ l2 = l4 }
   + { l4' | l1 = l3 ++ b :: l4' & l4' ++ a :: l2 = l4 }.
Proof.
intro Heq. change (b :: l4) with ((b :: nil) ++ l4) in Heq.
apply trichot_elt_app_inf in Heq;
  destruct Heq as [[ | [(l2', l2'') H'1 [H'2 H'3]]] | ]; subst;
  [ left; left | left; right | right ]; auto.
now destruct l2' as [|a' l2']; inversion H'2 as [[H1 H2]];
  subst; [ | destruct l2'; inversion H2 ]; list_simpl.
Qed.

Ltac trichot_elt_elt_inf_exec H :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l1 ++ ?x :: ?l2 =>
      apply trichot_elt_elt_inf in H;
        let l' := fresh "l" in
        let H1 := fresh H in
        let H2 := fresh H in
        let H3 := fresh H in
        destruct H as [[[l' H1 H2] | (H1 & H2 & H3)] | [l' H1 H2]];
        [ try subst l1; try subst lr
        | try subst x; try subst l1; try subst l2
        | try subst l2; try subst lh ]
  end.

(** ** Decomposition of [map] *)

Ltac decomp_map_eq H Heq :=
  match type of H with
  | map _ _ = _ ++ _ => apply map_eq_app in H ;
                          let l1 := fresh "l" in
                          let l2 := fresh "l" in
                          let H1 := fresh H in
                          let H2 := fresh H in
                          let Heq1 := fresh Heq in
                          destruct H as (l1 & l2 & Heq1 & H1 & H2) ;
                          rewrite Heq1 in Heq ; clear Heq1 ;
                          decomp_map_eq H1 Heq ; decomp_map_eq H2 Heq
  | map _ _ = _ :: _ => apply map_eq_cons in H ;
                          let x := fresh "x" in
                          let l2 := fresh "l" in
                          let H1 := fresh H in
                          let H2 := fresh H in
                          let Heq1 := fresh Heq in
                          destruct H as (x & l2 & Heq1 & H1 & H2) ;
                          rewrite Heq1 in Heq ; clear Heq1 ;
                          decomp_map_eq H2 Heq
  | _ => idtac
  end.

Ltac decomp_map H :=
  match type of H with
  | map _ ?l = _ => let l' := fresh "l" in
                    let Heq := fresh H in
                    remember l as l' eqn:Heq in H;
                    decomp_map_eq H Heq;
                    let H' := fresh H in
                    clear l'; rename Heq into H'
  end.

Ltac decomp_map_inf_eq H Heq :=
  match type of H with
  | map _ _ = _ ++ _ => apply map_eq_app_inf in H ;
                          let l1 := fresh "l" in
                          let l2 := fresh "l" in
                          let H1 := fresh H in
                          let H2 := fresh H in
                          let Heq1 := fresh Heq in
                          destruct H as ((l1 & l2) & Heq1 & H1 & H2) ;
                          rewrite Heq1 in Heq ; clear Heq1 ;
                          decomp_map_inf_eq H1 Heq ; decomp_map_inf_eq H2 Heq
  | map _ _  = _ :: _ => apply map_eq_cons_inf in H ;
                          let x := fresh "x" in
                          let l2 := fresh "l" in
                          let H1 := fresh H in
                          let H2 := fresh H in
                          let Heq1 := fresh Heq in
                          destruct H as ((x & l2) & Heq1 & H1 & H2) ;
                          rewrite Heq1 in Heq ; clear Heq1 ;
                          decomp_map_inf_eq H2 Heq
  | _ => idtac
  end.

Ltac decomp_map_inf H :=
  match type of H with
  | map _ ?l = _ => let l' := fresh "l" in
                    let Heq := fresh H in
                    remember l as l' eqn:Heq in H;
                    decomp_map_inf_eq H Heq;
                    let H' := fresh H in
                    clear l'; rename Heq into H'
  end.

(** ** [Forall] *)

Ltac specialize_Forall H a := apply Forall_forall with (x:=a) in H; [ | assumption ].
Tactic Notation "specialize_Forall" hyp(H) "with" constr(x) := specialize_Forall H x.
Ltac specialize_Forall_all a := repeat
match goal with
| H : Forall ?P ?l |- _ => specialize_Forall H with a
end.


(** * Additional statements *)

(** ** [concat] *)

Lemma concat_vs_elt A (a : A) L l1 l2 :
    concat L = l1 ++ a :: l2 ->
    {'(L1, L2, l1', l2') | l1 = concat L1 ++ l1' /\ l2 = l2' ++ concat L2
                      /\ L = L1 ++ (l1' ++ a :: l2') :: L2 }.
Proof.
revert l1 l2; induction L as [|l' L IHL]; simpl; intros l1 l2 eq.
- destruct l1; inversion eq.
- dichot_elt_app_inf_exec eq.
  + now split with (nil, L, l1, l); subst.
  + destruct IHL with l0 l2 as ((((L1, L2), l1'), l2') & (eqb & eqt & eq)); [symmetry ; apply eq1 |].
    split with ((l' :: L1), L2, l1', l2'); subst.
    split; [ apply app_assoc | auto ].
Qed.

Lemma concat_Forall2_inf A B (L : list (list A)) (l : list B) R :
    Forall2_inf R (concat L) l ->
    { L' & concat L' = l & Forall2_inf (Forall2_inf R) L L' }.
Proof.
revert l R; induction L as [|l' L IHL]; simpl; intros l R F2R.
- inversion F2R; subst.
  split with nil.
  + reflexivity.
  + apply Forall2_inf_nil.
- destruct Forall2_inf_app_inv_l with A B R l' (concat L) l; auto.
  destruct x, y; simpl in *.
  destruct IHL with l1 R as [L' p1 p2]; auto.
  split with (l0 :: L').
  + simpl; rewrite p1; auto.
  + now apply Forall2_inf_cons.
Qed.

(** ** [flat_map] *)

Lemma flat_map_map A B C (f : A -> B) (g : B -> list C) l :
  flat_map g (map f l) = flat_map (fun x => g (f x)) l.
Proof. now intros; rewrite flat_map_concat_map, map_map, <- flat_map_concat_map. Qed.

(** ** [filter] *)

Lemma filter_filter_id A f (l : list A) : filter f (filter f l) = filter f l.
Proof.
induction l as [|a l IHl]; [ reflexivity | cbn ].
destruct (f a) eqn:Hfa; cbn; rewrite ? Hfa, IHl; reflexivity.
Qed.

Lemma filter_negb_filter A f (l : list A) : filter (fun x => negb (f x)) (filter f l) = nil.
Proof.
induction l as [|a l IHl]; [ reflexivity | cbn ].
destruct (f a) eqn:Hfa; cbn; rewrite ? Hfa, IHl; reflexivity.
Qed.

Lemma filter_filter_comm A f g (l : list A) : filter f (filter g l) = filter g (filter f l).
Proof.
induction l as [|a l IHl]; [ reflexivity | cbn ].
destruct (f a) eqn:Hfa, (g a) eqn:Hga; cbn; rewrite ? Hfa, ? Hga, IHl; reflexivity.
Qed.

Lemma forallb_filter_forallb A f g (l : list A) : forallb f l = true -> forallb f (filter g l) = true.
Proof.
induction l as [|a l IHl]; [ reflexivity | cbn; intros [Ha Hf]%andb_true_iff ].
destruct (g a); cbn; now rewrite ? Ha, IHl.
Qed.

(** ** [partition] *)

Lemma partition_incl1 A f (l : list A) : incl (fst (partition f l)) l.
Proof. rewrite partition_as_filter. apply incl_filter. Qed.

Lemma partition_incl2 A f (l : list A) : incl (snd (partition f l)) l.
Proof. rewrite partition_as_filter. apply incl_filter. Qed.

Lemma forallb_true_partition A f (l : list A) : forallb f l = true -> partition f l = (l, nil).
Proof.
intros Hf. rewrite partition_as_filter.
rewrite <- (forallb_filter_id f l) at 2 by assumption.
now rewrite filter_negb_filter, forallb_filter_id.
Qed.

Lemma partition_app A f (l1 l2 : list A) :
  partition f (l1 ++ l2) = prod_map2 _ _ _ (@app A) (partition f l1) (partition f l2).
Proof.
induction l1 as [|a l1 IHl1]; cbn.
- destruct (partition f l2); reflexivity.
- destruct (f a); rewrite IHl1; destruct (partition f l1), (partition f l2); reflexivity.
Qed.

Lemma partition_incl1_inf A f (l : list A) : incl_inf (fst (partition f l)) l.
Proof. rewrite partition_as_filter. apply incl_inf_filter. Qed.

Lemma partition_incl2_inf A f (l : list A) : incl_inf (snd (partition f l)) l.
Proof. rewrite partition_as_filter. apply incl_inf_filter. Qed.


(** ** [Forall] and [Exists] *)

Lemma Forall_map A B (f : A -> B) l :
  Forall (fun x => exists y, x = f y) l <-> exists l0, l = map f l0.
Proof.
induction l as [|b l IHl]; split; intro H.
- now exists (@nil A).
- constructor.
- inversion H as [|b' l' [y ->] HF]; subst.
  apply IHl in HF as [l0 ->].
  now exists (y :: l0).
- destruct H as [l0 Heq].
  destruct l0 as [|a' l0]; inversion Heq; subst.
  constructor.
  + now exists a'.
  + apply IHl.
    now exists l0.
Qed.

Lemma Forall2_rev A B (R : A -> B -> Prop) l1 l2 : Forall2 R l1 l2 -> Forall2 R (rev l1) (rev l2).
Proof.
induction l1 as [|a l1 IH] in l2 |- *; intro HF; destruct l2 as [|b l2]; inversion_clear HF.
- constructor.
- cbn. apply Forall2_app.
  + apply IH. assumption.
  + now constructor.
Qed.


(** ** [Forall_inf] *)

(** Translation from [Forall_inf] to a list of dependent pairs *)

Fixpoint list_to_Forall T P (l : list (sigT P)) : Forall_inf P (map (@projT1 T P) l) :=
  match l with
  | nil => Forall_inf_nil _
  | p :: l => Forall_inf_cons (projT1 p) (projT2 p) (list_to_Forall l)
  end.

Fixpoint Forall_to_list T P (l : list T) (Fl : Forall_inf P l) : list (sigT P) :=
  match Fl with
  | Forall_inf_nil _ => nil
  | Forall_inf_cons x Px Fl => (existT P x Px) :: (Forall_to_list Fl)
  end.

Lemma Forall_to_list_support T P L FL :
  map (@projT1 _ _) (@Forall_to_list T P L FL) = L.
Proof.
induction FL ; simpl ; try rewrite IHFL ; reflexivity.
Defined.

Lemma Forall_to_list_length T P (l : list T) (Fl : Forall_inf P l) :
  length (Forall_to_list Fl) = length l.
Proof.
induction Fl.
- reflexivity.
- simpl; rewrite IHFl; reflexivity.
Qed.

Lemma Forall_to_list_to_Forall T P : forall L FL,
 rew (Forall_to_list_support _) in list_to_Forall (@Forall_to_list T P L FL) = FL.
Proof.
induction FL ; simpl.
- reflexivity.
- transitivity (Forall_inf_cons x p
               (rew [Forall_inf P] Forall_to_list_support FL in 
                   list_to_Forall (Forall_to_list FL))).
  + clear.
    destruct (Forall_to_list_support FL) ; reflexivity.
  + rewrite IHFL ; reflexivity.
Qed.


(** ** [Forall2_inf] *)

Lemma Forall2_inf_in_l A B (R : A -> B -> Type) l1 l2 a :
  Forall2_inf R l1 l2 -> In_inf a l1 -> { b & prod (In_inf b l2) (R a b) }.
Proof.
intros HF; induction HF as [| x y ? ? ? ? IHF]; intro Hin; inversion Hin.
- subst; split with y. now split; [ left | ].
- destruct IHF as (b & Hinb & HRab); auto.
  split with b. now split; [ right | ].
Qed.

Lemma Forall2_inf_in_r A B (R : A -> B -> Type) l1 l2 b :
  Forall2_inf R l1 l2 -> In_inf b l2 -> { a & prod (In_inf a l1) (R a b) }.
Proof.
intros HF; induction HF as [| x y ? ? ? ? IHF]; intro Hin; inversion Hin.
- subst; split with x. now split; [ left | ].
- destruct IHF as (a & Hina & HRab); [ assumption | ].
  split with a. now split; [ right | ].
Qed.

Lemma Forall2_inf_rev A B (R : A -> B -> Type) l1 l2 : Forall2_inf R l1 l2 -> Forall2_inf R (rev l1) (rev l2).
Proof.
induction l1 as [|a l1 IH] in l2 |- *; intro HF; destruct l2 as [|b l2]; inversion_clear HF.
- constructor.
- cbn. apply Forall2_inf_app.
  + apply IH. assumption.
  + now constructor.
Qed.


(** ** Map for functions with two arguments: [map2] *)

Fixpoint map2 A B C (f : A -> B -> C) l1 l2 :=
  match l1 , l2 with
  | nil , _ => nil
  | _ , nil => nil
  | a1::r1 , a2::r2 => (f a1 a2)::(map2 f r1 r2)
  end.

Lemma map2_length A B C (f : A -> B -> C) l1 l2 :
  length l1 = length l2 -> length (map2 f l1 l2) = length l2.
Proof.
revert l2; induction l1 as [|a l1 IHl1]; intros l2 Heq; auto.
destruct l2 as [| b l2].
- inversion Heq.
- simpl in Heq; injection Heq; intro Heq'.
  apply IHl1 in Heq'; simpl; auto.
Qed.

Lemma length_map2 A B C (f : A -> B -> C) l1 l2 :
  length (map2 f l1 l2) <= length l1 /\ length (map2 f l1 l2) <= length l2.
Proof.
revert l2; induction l1 as [|a l1 IHl1]; intros l2.
- split; apply le_0_n.
- destruct l2 as [| b l2].
  + split; apply le_0_n.
  + destruct (IHl1 l2).
    now split; simpl; apply le_n_S.
Qed.

Lemma nth_map2 A B C (f : A -> B -> C) l1 l2 i a b c :
  i < length (map2 f l1 l2) ->
    nth i (map2 f l1 l2) c = f (nth i l1 a) (nth i l2 b).
Proof.
revert i l2; induction l1 as [|a' l1 IHl1]; intros i l2 Hlt.
- inversion Hlt.
- destruct l2 as [| b' l2].
  + inversion Hlt.
  + destruct i; simpl in *; auto.
    now apply IHl1, Nat.succ_lt_mono.
Qed.

(** ** [fold_right] *)

Lemma fold_right_app_assoc2 A B f (g : B -> A) h (e : A) l1 l2 :
    (forall x y z, h (g x) (f y z) = f (h (g x) y) z) ->
    (f e (fold_right (fun x => h (g x)) e l2) = (fold_right (fun x => h (g x)) e l2)) ->
  fold_right (fun x => h (g x)) e (l1 ++ l2) =
  f (fold_right (fun x => h (g x)) e l1) (fold_right (fun x => h (g x)) e l2).
Proof.
intros Hassoc Hunit.
rewrite fold_right_app.
remember (fold_right (fun x => f (g x)) e l2) as r.
induction l1; simpl.
- symmetry; apply Hunit.
- rewrite <- Hassoc.
  f_equal; assumption.
Qed.

Lemma fold_right_app_assoc A f (e : A) l1 l2 :
  (forall x y z, f x (f y z) = f (f x y) z) -> (forall x, f e x = x) ->
  fold_right f e (l1 ++ l2) = f (fold_right f e l1) (fold_right f e l2).
Proof. intros Hassoc Hunit; apply fold_right_app_assoc2; [ assumption | apply Hunit ]. Qed.


(** ** Tactics for automatic solving *)

Ltac in_solve :=
  simpl; repeat split;
  repeat (apply in_or_app; simpl);
  repeat (
    repeat match goal with
    | H : ?P /\ ?Q |- _ => destruct H
    | H : ?P \/ ?Q |- _ => destruct H
    end;
    repeat match goal with
    | H : In _ _ |- _ => progress simpl in H
    end;
    repeat match goal with
    | H : In _ (_ :: _) |- _ => inversion H
    end;
    repeat match goal with
    | H : In _ _ |- _ => simpl in H; apply in_app_or in H; destruct H
    end);
  intuition auto with *; fail.

Ltac Forall_inf_cbn_hyp :=
  repeat (
    match goal with
    | H:Forall_inf _ (_ ++ _) |- _ => let H1 := fresh H in assert (H1 := Forall_inf_app_l _ _ H);
                                      let H2 := fresh H in assert (H2 := Forall_inf_app_r _ _ H);
                                      clear H
    | H:Forall_inf _ (_ :: _) |- _ => inversion H; clear H
    end).
Ltac Forall_inf_solve_rec :=
  match goal with
  | |- Forall_inf _ (_ ++ _) => apply Forall_inf_app ; Forall_inf_solve_rec
  | |- Forall_inf _ (_ :: _) => constructor; [ assumption | Forall_inf_solve_rec ]
  | |- Forall_inf _ nil => constructor
  | _ => try assumption
  end.
Ltac Forall_inf_solve := Forall_inf_cbn_hyp; cbn; Forall_inf_solve_rec; fail.


(** reflect *)

Lemma Forall_forallb_reflect A P f (l : list A) :
  (forall a, reflect (P a) (f a)) -> reflect (Forall P l) (forallb f l).
Proof.
intros Hspec.
induction l as [|a l IHl]; [ constructor; constructor | cbn ].
specialize (Hspec a).
destruct (f a), (forallb f l); inversion Hspec as [Hspect|Hspecf]; inversion IHl as [IHlt|IHlf]; constructor.
- constructor; assumption.
- intros HF. apply IHlf. inversion HF. assumption.
- intros HF. apply Hspecf. inversion HF. assumption.
- intros HF. apply IHlf. inversion HF. assumption.
Qed.

Lemma Forall_inf_forallb_reflectT A P f (l : list A) :
  (forall a, reflectT (P a) (f a)) -> reflectT (Forall_inf P l) (forallb f l).
Proof.
intros Hspec.
induction l as [|a l IHl]; [ constructor; constructor | cbn ].
specialize (Hspec a).
destruct (f a), (forallb f l); inversion Hspec as [Hspect|Hspecf]; inversion IHl as [IHlt|IHlf]; constructor.
- constructor; assumption.
- intros HF. apply IHlf. inversion HF. assumption.
- intros HF. apply Hspecf. inversion HF. assumption.
- intros HF. apply IHlf. inversion HF. assumption.
Qed.
