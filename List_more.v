(** Add-ons for List library
Useful tactics and properties apparently missing in the [List] library. *)

(* TODO once it is confirmed that deprecated tactics are subsumed by Type versions, remove them *)

From Stdlib Require Import Decidable PeanoNat Morphisms.
From Stdlib Require Export List.
From OLlibs Require Import Logic_Datatypes_more Bool_more.
From OLlibs Require Export ListT.
Import EqNotations.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


(** misc *)

(* TODO included in PR rocq#11966 submitted, remove once merged and released *)

    Lemma rev_case A (l : list A) : l = nil \/ exists a tl, l = tl ++ a :: nil.
    Proof. induction l as [|a l] using rev_ind; [ left | right; exists a, l ]; reflexivity. Qed.

(* case analysis similar to [destruct l] but splitting at the end of the list in the spirit of [rev_ind] *)

Inductive last_list_internal A : list A -> Type :=
| last_list_nil_internal : last_list_internal nil
| last_list_last_internal : forall a l, last_list_internal (l ++ a :: nil).

Lemma last_case_internal A (l : list A) : last_list_internal l.
Proof. induction l as [|a l] using rev_rect; constructor. Qed.

Tactic Notation "last_destruct" constr(l) := destruct (last_case_internal l).
Tactic Notation "last_destruct" constr(l) "as" simple_intropattern(p) := destruct (last_case_internal l) as p.


(** * Tactics *)

(** ** Simplification in lists *)

Ltac list_simpl :=
  repeat (
    repeat cbn;
    repeat match goal with
    | |- context [(?l1 ++ ?l2) ++ ?l3] => rewrite <- (app_assoc l1 l2 l3)
    | |- context [(?a :: ?l1) ++ ?l2] => rewrite <- (app_comm_cons l1 l2 a)
    | |- context [?l ++ nil] => rewrite (app_nil_r l)
    | |- context [rev (map ?f ?l)] => rewrite <- (map_rev f l)
    | |- context [rev (rev ?l)] => rewrite (rev_involutive l)
    | |- context [rev (?l1 ++ ?l2)] => rewrite (rev_app_distr l1 l2)
    | |- context [map ?f (?l1 ++ ?l2)] => rewrite (map_app f l1 l2)
    | |- context [flat_map ?f (?l1 ++ ?l2)] => rewrite (flat_map_app f l1 l2)
    end).
#[local] Ltac list_simpl_hyp H :=
  repeat (
    repeat cbn in H;
    repeat match type of H with
    | context [(?l1 ++ ?l2) ++ ?l3] => rewrite <- (app_assoc l1 l2 l3) in H
    | context [(?a :: ?l1) ++ ?l2] => rewrite <- (app_comm_cons l1 l2 a) in H
    | context [?l ++ nil] => rewrite (app_nil_r l) in H
    | context [rev (map ?f ?l)] => rewrite <- (map_rev f l) in H
    | context [rev (rev ?l)] => rewrite (rev_involutive l) in H
    | context [rev (?l1 ++ ?l2)] => rewrite (rev_app_distr l1 l2) in H
    | context [map ?f (?l1 ++ ?l2)] => rewrite (map_app f l1 l2) in H
    | context [flat_map ?f (?l1 ++ ?l2)] => rewrite (flat_map_app f l1 l2) in H
    end).
Ltac list_simpl_hyps :=
  match goal with
  | H : _ |- _ => list_simpl_hyp H; revert H; list_simpl_hyps; intro H
  | _ => idtac
  end.

Tactic Notation "list_simpl" "in" "*" := list_simpl_hyps; list_simpl.
Tactic Notation "list_simpl" "in" hyp(H) := list_simpl_hyp H.

Ltac list_reflexivity := list_simpl; reflexivity.

(* same as [list_simpl] but might do more job on specific case
     could loop with existential variables *)
Ltac list_esimpl :=
  repeat (
    repeat cbn;
    rewrite <- ? app_assoc, <- ? app_comm_cons, ? app_nil_r,
            <- ? map_rev, ? rev_involutive, ? rev_app_distr,
            ? map_app, ? flat_map_app).
#[local] Ltac list_esimpl_hyp H :=
  repeat (
    repeat cbn in H;
    rewrite <- ? app_assoc, <- ? app_comm_cons, ? app_nil_r,
            <- ? map_rev, ? rev_involutive, ? rev_app_distr,
            ? map_app, ? flat_map_app in H).
Ltac list_esimpl_hyps :=
  match goal with
  | H : _ |- _ => list_esimpl_hyp H; revert H; list_esimpl_hyps; intro H
  | _ => idtac
  end.
Tactic Notation "list_esimpl" "in" "*" := list_esimpl_hyps; list_esimpl.
Tactic Notation "list_esimpl" "in" hyp(H) := list_esimpl_hyp H.

Ltac list_ereflexivity := list_esimpl; reflexivity.


(** ** Application up to list equality (associativity, unit, etc.) **)

(* similar to [apply] but tries to unify up to equality of lists thanks to [list_reflexivity] *)
(*   use [Tactic Notation] to avoid typing of the argument at calling time *)
Tactic Notation "list_apply" open_constr(t) :=
  match goal with
  | |- context G [?L] => match type of L with
                         | list _ => pattern L; eapply eq_rect; [ eapply t | list_reflexivity ]
                         end
  end.
Tactic Notation "list_apply" open_constr(t) "in" hyp(H) :=
  match type of H with
  | context G [?L] => match type of L with
                      | list _ => pattern L in H; eapply eq_rect in H; [ eapply t in H | list_reflexivity ]
                      end
  end.


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
                 [change (cons x l) with (app (cons x nil) l)]
              which leads to simpler generated term
              but does not work with existential variables *)
         end
  end.
#[local] Ltac cons2app_hyp H :=
  repeat
  match type of H with
  | context [ cons ?x ?l ]  =>
      lazymatch l with
      | nil => fail
      | _ =>  rewrite (cons_is_app x l) in H
           (* one could prefer
                 [change (cons x l) with (app (cons x nil) l) in H]
              which leads to simpler generated term
              but does not work with existential variables *)
      end
  end.
Ltac cons2app_hyps :=
  match goal with
  | H : _ |- _ => cons2app_hyp H; revert H; cons2app_hyps; intro H
  | _ => idtac
  end.
Tactic Notation "cons2app" "in" "*" := cons2app_hyps; cons2app.
Tactic Notation "cons2app" "in" hyp(H) := cons2app_hyp H.


(** ** Decomposition of lists and [list] equalities *)

Lemma length_eq_add_inv A (l : list A) n m : length l = n + m ->
  {'(l1, l2) | length l1 = n /\ length l2 = m & l = l1 ++ l2 }.
Proof.
induction n as [|n IHn] in l, m |- *; intro Heq.
- now split with (nil, l).
- destruct l as [|a l]; inversion Heq as [Heq2].
  specialize (IHn l m Heq2) as [(l1, l2) [<- <-] ->].
  split with (a :: l1, l2); [ split | ]; reflexivity.
Qed.

Ltac decomp_nil_eq H :=
  match type of H with
  | nil = nil => clear H
  | nil = ?l => subst l
  | ?l = nil => subst l
  | nil = ?x :: ?l2 => discriminate H
  | ?x :: ?l2 = nil => discriminate H
  | nil = ?l1 ++ ?x :: ?l2 => destruct l1; discriminate H
  | ?l1 ++ ?x :: ?l2 = nil => destruct l1; discriminate H
  | nil = ?l1 ++ ?l2 => simple apply eq_sym in H;
                        let H1 := fresh H in
                        let H2 := fresh H in
                        apply app_eq_nil in H as [H1 H2];
                        assert (H := I); (* protect name [H] *)
                        try decomp_nil_eq H1; try decomp_nil_eq H2;
                        try (let H1' := fresh in
                             let H2' := fresh in
                             rename H1 into H1'; rename H2 into H2'; (* test if both H1 and H2 exist *)
                             clear H; assert (H := conj H1' H2'); clear H1' H2');
                        try (match type of H with True => clear H; rename H1 into H end);
                        try (match type of H with True => clear H; rename H2 into H end);
                        try (match type of H with True => clear H end)
  | ?l1 ++ ?l2 = nil => let H1 := fresh H in
                        let H2 := fresh H in
                        apply app_eq_nil in H as [H1 H2];
                        assert (H := I); (* protect name [H] *)
                        try decomp_nil_eq H1; try decomp_nil_eq H2;
                        try (let H1' := fresh in
                             let H2' := fresh in
                             rename H1 into H1'; rename H2 into H2'; (* test if both H1 and H2 exist *)
                             clear H; assert (H := conj H1' H2'); clear H1' H2');
                        try (match type of H with True => clear H; rename H1 into H end);
                        try (match type of H with True => clear H; rename H2 into H end);
                        try (match type of H with True => clear H end)
  end.

#[deprecated(since="ollibs 2.1.1", note="Use decomp_nil_eq instead.")] (* TODO add [use] rocq#20444 *)
Ltac decomp_nil_eq_elt H :=
  match type of H with
  | nil = ?x :: ?l2 => discriminate H
  | ?x :: ?l2 = nil => discriminate H
  | nil = ?l1 ++ ?x :: ?l2 => destruct l1; discriminate H
  | ?l1 ++ ?x :: ?l2 = nil => destruct l1; discriminate H
  end.

Ltac decomp_unit_eq H :=
  match type of H with
  | _ :: nil = nil => discriminate H
  | nil = _ :: nil => discriminate H
  | ?a :: nil = ?x :: ?l => let Hnil := fresh H in injection H as [= H Hnil];
                              (try subst x); (try subst a); try decomp_nil_eq Hnil
  | ?x :: ?l = ?a :: nil => let Hnil := fresh H in injection H as [= H Hnil];
                              (try subst x); (try subst a); try decomp_nil_eq Hnil
  | ?a :: nil = ?l1 ++ ?x :: ?l2 =>
      let Hnil1 := fresh H in
      let Hnil2 := fresh H in
      simple apply eq_sym in H; apply elt_eq_unit in H as [H [Hnil1 Hnil2]];
(* [simple apply eq_sym] faster than [symmetry]? *)
      (try subst x); (try subst a); try decomp_nil_eq Hnil1; try decomp_nil_eq Hnil2;
      (try clear l1); (try clear l2)
  | ?l1 ++ ?x :: ?l2 = ?a :: nil =>
      let Hnil1 := fresh H in
      let Hnil2 := fresh H in
      apply elt_eq_unit in H as [H [Hnil1 Hnil2]];
      (try subst x); (try subst a); try decomp_nil_eq Hnil1; try decomp_nil_eq Hnil2;
      (try clear l1); (try clear l2)
  | ?a :: nil = ?l1 ++ ?l2 => simple apply eq_sym in H; let Hnil := fresh H in
                                apply app_eq_unitT in H as [[Hnil H] | [H Hnil]];
                                try decomp_nil_eq Hnil; try decomp_unit_eq H
  | ?l1 ++ ?l2 = ?a :: nil => let Hnil := fresh H in
                              apply app_eq_unitT in H as [[Hnil H] | [H Hnil]];
                              try decomp_nil_eq Hnil; try decomp_unit_eq H
  end.

#[deprecated(since="ollibs 2.1.1", note="Use decomp_unit_eq instead.")] (* TODO add [use] rocq#20444 *)
Ltac decomp_unit_eq_elt H :=
  match type of H with
  | ?a :: nil = ?l1 ++ ?x :: ?l2 =>
      let Hnil1 := fresh H in
      let Hnil2 := fresh H in
      simple apply eq_sym in H; apply elt_eq_unit in H as [H [Hnil1 Hnil2]];
(* [simple apply eq_sym] faster than [symmetry]? *)
      (try subst x); (try subst a); decomp_nil_eq Hnil1; decomp_nil_eq Hnil2;
      (try clear l1); (try clear l2)
  | ?l1 ++ ?x :: ?l2 = ?a :: nil =>
      let Hnil1 := fresh H in
      let Hnil2 := fresh H in
      apply elt_eq_unit in H as [H [Hnil1 Hnil2]];
      (try subst x); (try subst a); decomp_nil_eq Hnil1; decomp_nil_eq Hnil2;
      (try clear l1); (try clear l2)
  end.

Lemma trichot_appT A (l1 l2 l3 l4 : list A) : l1 ++ l2 = l3 ++ l4 ->
    { l2' | l2' <> nil & l1 ++ l2' = l3 /\ l2 = l2' ++ l4 }
  + ((l1 = l3) * (l2 = l4))
  + { l4' | l4' <> nil & l1 = l3 ++ l4' /\ l4' ++ l2 = l4 }.
Proof.
induction l1 as [|b l1 IHl1] in l2, l3, l4 |- *; induction l3 as [|c l3 IHl3] in l4 |- *;
  cbn; intro Heq; inversion Heq as [[Heq'' Heq']]; subst.
- left. right. repeat split.
- left. left. exists (c :: l3); [ intros [=] | repeat split ].
- right. exists (b :: l1); [ intros [=] | repeat split ].
- destruct (IHl1 _ _ _ Heq') as [[[l2' Hnil [<- ->]]|[-> ->]]|[l4' Hnil [-> <-]]].
  + now left; left; exists l2'.
  + left. right. repeat split.
  + now right; exists l4'.
Qed.

Lemma dichot_app_eq_appT A (l1 l2 l3 l4 : list A) : l1 ++ l2 = l3 ++ l4 ->
     { l2' | l1 ++ l2' = l3 & l2 = l2' ++ l4 }
   + { l4' | l1 = l3 ++ l4' & l4' ++ l2 = l4 }.
Proof.
intros [[[l2' Hnil [<- ->]]|[-> ->]]|[l4' Hnil [-> <-]]]%trichot_appT.
- left. exists l2'; reflexivity.
- left. exists nil; list_simpl; reflexivity.
- right. exists l4'; reflexivity.
Qed.

#[local] Ltac decomp_app_eq_app_core H p :=
  match type of H with
  | _ ++ _ = _ ++ _ => apply dichot_app_eq_appT in H as p
  end.
Tactic Notation "decomp_app_eq_app" hyp(H) "as" simple_intropattern(p) := decomp_app_eq_app_core H p.
Tactic Notation "decomp_app_eq_app" hyp(H) :=
  let l := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  decomp_app_eq_app_core H ipattern:([[l H1 H2]|[l H1 H2]]).

Lemma elt_eq_app_dichotT A l1 (a : A) l2 l3 l4 : l1 ++ a :: l2 = l3 ++ l4 ->
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

#[local] Ltac decomp_elt_eq_app_core H p :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ => apply elt_eq_app_dichotT in H as p
  | _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H;
                            apply elt_eq_app_dichotT in H as p
  end.
Tactic Notation "decomp_elt_eq_app" hyp(H) "as" simple_intropattern(p) := decomp_elt_eq_app_core H p.
Tactic Notation "decomp_elt_eq_app" hyp(H) :=
  let l := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  decomp_elt_eq_app_core H ipattern:([[l H1 H2]|[l H1 H2]]).

Lemma trichot_elt_appT A l1 (a : A) l2 l3 l4 l5 : l1 ++ a :: l2 = l3 ++ l4 ++ l5 ->
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
  + decomp_elt_eq_app Heq2; subst.
    * now left; right; eexists (a' :: l1, _).
    * now right; eexists.
- destruct (IHl1 _ _ _ _ Heq'') as [ [[l' <- ->] | [(l2', l2'') -> [<- ->]]] | [l' -> <-] ].
  + now left; left; exists l'.
  + now left; right; exists (l2', l2'').
  + now right; exists l'.
Qed.

#[local] Ltac decomp_elt_eq_app_app_core H p :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ ++ _ => apply trichot_elt_appT in H as p
  | _ ++ _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H;
                                 apply trichot_elt_appT in H as p
  end.
Tactic Notation "decomp_elt_eq_app_app" hyp(H) "as" simple_intropattern(p) :=
  decomp_elt_eq_app_app_core H p.
Tactic Notation "decomp_elt_eq_app_app" hyp(H) :=
  let l1 := fresh "l" in
  let l2 := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  decomp_elt_eq_app_app_core H ipattern:([[[l1 H1 H2] | [[l1 l2] H1 [H2 H3]] ] | [l2 H1 H2] ]).

Lemma trichot_elt_eltT A l1 (a : A) l2 l3 b l4 : l1 ++ a :: l2 = l3 ++ b :: l4 ->
     { l2' | l1 ++ a :: l2' = l3 & l2 = l2' ++ b :: l4 }
   + { l1 = l3 /\ a = b /\ l2 = l4 }
   + { l4' | l1 = l3 ++ b :: l4' & l4' ++ a :: l2 = l4 }.
Proof.
intro Heq. change (b :: l4) with ((b :: nil) ++ l4) in Heq.
decomp_elt_eq_app_app Heq as [[ | [(l2', l2'') H'1 [H'2 H'3]]] | ]; subst;
  [ left; left | left; right | right ]; auto.
now destruct l2' as [|a' l2']; inversion H'2 as [[H1 H2]];
  subst; [ | destruct l2'; inversion H2 ]; list_simpl.
Qed.

#[local] Ltac decomp_elt_eq_elt_core H p :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l1 ++ ?x :: ?l2 =>
      apply trichot_elt_eltT in H as p;
        [ try subst l1; try subst lr
        | try subst x; try subst l1; try subst l2
        | try subst l2; try subst lh ]
  end.
Tactic Notation "decomp_elt_eq_elt" hyp(H) "as" simple_intropattern(p) :=
  decomp_elt_eq_elt_core H p.
Tactic Notation "decomp_elt_eq_elt" hyp(H) :=
  let l := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  decomp_elt_eq_elt_core H ipattern:([[[l H1 H2] | [H1 [H2 H3]]] | [l H1 H2]]).

Lemma app_eq_app_trichot A (l1 l2 l3 l4 : list A) : l1 ++ l2 = l3 ++ l4 ->
     (exists l2', l2' <> nil /\ l1 ++ l2' = l3 /\ l2 = l2' ++ l4)
  \/ (l1 = l3 /\ l2 = l4)
  \/ (exists l4', l4' <> nil /\ l1 = l3 ++ l4' /\ l4' ++ l2 = l4).
Proof.
intros [l [[-> ->]|[-> ->]]]%app_eq_app; destruct l as [|a l].
- right. left. list_simpl. repeat split.
- right. right. exists (a :: l); split; [ intros [=] | repeat split ].
- right. left. list_simpl. repeat split.
- left. exists (a :: l); split; [ intros [=] | repeat split ].
Qed.

Lemma app_eq_app_dichot A (l1 l2 l3 l4 : list A) : l1 ++ l2 = l3 ++ l4 ->
     (exists l2', l1 ++ l2' = l3 /\ l2 = l2' ++ l4)
  \/ (exists l4', l1 = l3 ++ l4' /\ l4' ++ l2 = l4).
Proof. intros [l [[-> ->]|[-> ->]]]%app_eq_app; [ right | left ]; exists l; repeat split. Qed.

#[local] Ltac decomp_app_eq_app_Prop_core H p :=
  match type of H with
  | _ ++ _ = _ ++ _ => apply app_eq_app_dichot in H as p
  end.
#[deprecated(since="ollibs 2.0.8", note="Use decomp_app_eq_app instead.")] (* TODO add [use] rocq#20444 *)
Tactic Notation "decomp_app_eq_app_Prop" hyp(H) "as" simple_intropattern(p) := decomp_app_eq_app_Prop_core H p.
#[deprecated(since="ollibs 2.0.8", note="Use decomp_app_eq_app instead.")] (* TODO add [use] rocq#20444 *)
Tactic Notation "decomp_app_eq_app_Prop" hyp(H) :=
  let l := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  decomp_app_eq_app_Prop_core H ipattern:([[l [H1 H2]]|[l [H1 H2]]]).

Lemma elt_eq_app_dichot A l1 (a : A) l2 l3 l4 : l1 ++ a :: l2 = l3 ++ l4 ->
     (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ l4)
  \/ (exists l4', l1 = l3 ++ l4' /\ l4' ++ a :: l2 = l4).
Proof.
induction l1 as [|b l1 IHl1] in l2, l3, l4 |- *; induction l3 as [|c l3 IHl3] in l4 |- *; cbn;
  intro Heq; inversion Heq as [[Heq'' Heq']].
- now right; exists (@nil A).
- now left; exists l3.
- now right; exists (b :: l1).
- destruct (IHl1 _ _ _ Heq') as [[l2' [<- H2'2]] | [l4' [-> H4'2]]].
  + now left; exists l2'.
  + now right; exists l4'.
Qed.

#[local] Ltac decomp_elt_eq_app_Prop_core H p :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ => apply elt_eq_app_dichot in H as p
  | _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H;
                            apply elt_eq_app_dichot in H as p
  end.
#[deprecated(since="ollibs 2.0.8", note="Use decomp_elt_eq_app instead.")] (* TODO add [use] rocq#20444 *)
Tactic Notation "decomp_elt_eq_app_Prop" hyp(H) "as" simple_intropattern(p) := decomp_elt_eq_app_Prop_core H p.
#[deprecated(since="ollibs 2.0.8", note="Use decomp_elt_eq_app instead.")] (* TODO add [use] rocq#20444 *)
Tactic Notation "decomp_elt_eq_app_Prop" hyp(H) :=
  let l := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  decomp_elt_eq_app_Prop_core H ipattern:([[l [H1 H2]]|[l [H1 H2]]]).

Lemma elt_eq_app_app_trichot A l1 (a : A) l2 l3 l4 l5 : l1 ++ a :: l2 = l3 ++ l4 ++ l5 ->
      (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ l4 ++ l5)
   \/ (exists l2' l2'', l1 = l3 ++ l2' /\ l2' ++ a :: l2'' = l4 /\ l2 = l2'' ++ l5)
   \/ (exists l5', l1 = l3 ++ l4 ++ l5' /\ l5' ++ a :: l2 = l5).
Proof.
induction l1 as [|b l1 IHl1] in l2, l3, l4, l5 |- *; induction l3 as [|c l3 IHl3] in l4, l5 |- *; cbn;
  intro Heq; simpl in Heq; inversion Heq as [[Heq' Heq'']].
- destruct l4 as [| a' l4]; inversion Heq'.
  + now right; right; exists nil.
  + now right; left; exists nil, l4.
- now left; exists l3.
- destruct l4 as [| a' l4]; inversion Heq' as [[Heq1 Heq2]].
  + now right; right; exists (b :: l1).
  + decomp_elt_eq_app Heq2; subst.
    * now right; left; exists (a' :: l1); eexists.
    * now right; right; eexists.
- destruct (IHl1 _ _ _ _ Heq'')
    as [[l' [<- ->]] | [ [l2' [l2'' [-> [<- ->]]]] | [l' [-> <-]] ]].
  + now left; exists l'.
  + now right; left; exists l2', l2''.
  + now right; right; exists l'.
Qed.

#[local] Ltac decomp_elt_eq_app_app_Prop_core H p :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ ++ _ => apply elt_eq_app_app_trichot in H as p
  | _ ++ _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H;
                                 apply elt_eq_app_app_trichot in H as p
  end.
#[deprecated(since="ollibs 2.0.8", note="Use decomp_elt_eq_app_app instead.")] (* TODO add [use] rocq#20444 *)
Tactic Notation "decomp_elt_eq_app_app_Prop" hyp(H) "as" simple_intropattern(p) :=
  decomp_elt_eq_app_app_Prop_core H p.
#[deprecated(since="ollibs 2.0.8", note="Use decomp_elt_eq_app_app instead.")] (* TODO add [use] rocq#20444 *)
Tactic Notation "decomp_elt_eq_app_app_Prop" hyp(H) :=
  let l1 := fresh "l" in
  let l2 := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  decomp_elt_eq_app_app_Prop_core H ipattern:([[l1 [H1 H2]] | [[l1 [l2 [H1 [H2 H3]]]] | [l2 [H1 H2]]]]).

Lemma elt_eq_elt_trichot A l1 (a : A) l2 l3 b l4 : l1 ++ a :: l2 = l3 ++ b :: l4 ->
      (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ b :: l4)
   \/ (l1 = l3 /\ a = b /\ l2 = l4)
   \/ (exists l4', l1 = l3 ++ b :: l4' /\ l4' ++ a :: l2 = l4).
Proof.
intro Heq. change (b :: l4) with ((b :: nil) ++ l4) in Heq.
decomp_elt_eq_app_app Heq as [[[l2' ? ?] | [[[|a' l2'] l2''] -> [[= -> H] ->]] ] | [l2' ? ?] ];
  [ now left; exists l2' | right; left .. | now right; right; exists l2' ].
- subst. list_simpl. repeat split.
- decomp_nil_eq H.
Qed.

#[local] Ltac decomp_elt_eq_elt_Prop_core H p :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l1 ++ ?x :: ?l2 =>
      apply elt_eq_elt_trichot in H as p;
        [ try subst l1; try subst lr
        | try subst x; try subst l1; try subst l2
        | try subst l2; try subst lh ]
  end.
#[deprecated(since="ollibs 2.0.8", note="Use decomp_elt_eq_elt instead.")] (* TODO add [use] rocq#20444 *)
Tactic Notation "decomp_elt_eq_elt_Prop" hyp(H) "as" simple_intropattern(p) := decomp_elt_eq_elt_Prop_core H p.
Tactic Notation "decomp_elt_eq_elt_Prop" hyp(H) :=
  let l := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  decomp_elt_eq_elt_Prop_core H ipattern:([[l [H1 H2]] | [[H1 [H2 H3]] | [l [H1 H2]]]]).

(** ** Decomposition of [map] *)

(* works better when right-hand side leaves are variables,
   use [remember] to assign name to non-variables leaves *)

(* recursively decompose [H : map f l = _] into smaller equations of the shape [map f _  = _]
   by decomposing [l] *)
Ltac decomp_map_to_eqs H :=
  match type of H with
  | map _ _ = _ ++ _ => let l1 := fresh "l" in
                        let l2 := fresh "l" in
                        let H1 := fresh H in
                        let H2 := fresh H in
                        apply map_eq_appT in H as [(l1, l2) -> [H1 H2]];
                        assert (H := I); (* protect name [H] *)
                        decomp_map_to_eqs H1; decomp_map_to_eqs H2;
                        clear H; assert (H := conj H1 H2); clear H1 H2
  | map _ _ = _ :: _ => let x := fresh "x" in
                        let l2 := fresh "l" in
                        let H1 := fresh H in
                        let H2 := fresh H in
                        apply map_eq_consT in H as [(x, l2) -> [H1 H2]];
                        assert (H := I); (* protect name [H] *)
                        decomp_map_to_eqs H2;
                        clear H; assert (H := conj H1 H2); clear H1 H2
  | map _ _ = nil => apply map_eq_nil in H
  | _ => idtac
  end.

(* takes a conjunction [H] of equations [f _ = _] and [map f _ = _]
   and for each [f b = a] with [a] and [b] variables, renames [a] into [f a] and [b] into [a]
   [b] is supposed to be a fresh name generated by [decomp_map_to_eqs] while [a] was already there *)
Ltac substitute_map_family H :=
  match type of H with
  | _ /\ _ => let H1 := fresh H in
              let H2 := fresh H in
              destruct H as [H1 H2];
              assert (H := I); (* protect name [H] *)
              substitute_map_family H1; substitute_map_family H2;
              try (let H1' := fresh in
                   let H2' := fresh in
                   rename H1 into H1'; rename H2 into H2'; (* test if both H1 and H2 exist *)
                   clear H; assert (H := conj H1' H2'); clear H1' H2');
              try (match type of H with True => clear H; rename H1 into H end);
              try (match type of H with True => clear H; rename H2 into H end);
              try (match type of H with True => clear H end)
  | _ ?b = ?a => subst a; rename b into a
  | _ => idtac
  end.

(* decompose [H : map f l = _] using [decomp_map_to_eqs]
   decomposition of [l] is returned in [H] and sub-equations generated by [decomp_map_to_eqs] in [Heq] *)
Ltac decomp_map_core H Heq :=
  match type of H with
  | map _ ?l = _ => let l' := fresh "l" in
                    rename H into Heq;
                    remember l as l' eqn:H in Heq; simple apply eq_sym in H;
                    decomp_map_to_eqs Heq
  | _ = map _ _ => simple apply eq_sym in H; decomp_map_core H Heq; simple apply eq_sym in H
  end.
Tactic Notation "decomp_map_eq" ident(H) :=
  let Heq := fresh "Heq" in decomp_map_core H Heq; substitute_map_family Heq.
Tactic Notation "decomp_map_eq" ident(H) "eqn" ":" ident(Heq) := decomp_map_core H Heq; substitute_map_family Heq.

#[deprecated(since="ollibs 2.1.1", note="Use decomp_map_eq instead.")] (* TODO add [use] rocq#20444 *)
Tactic Notation "decomp_map" ident(H) :=
  let Heq := fresh "Heq" in decomp_map_core H Heq; substitute_map_family Heq.
#[deprecated(since="ollibs 2.1.1", note="Use decomp_map_eq instead.")] (* TODO add [use] rocq#20444 *)
Tactic Notation "decomp_map" ident(H) "eqn" ":" ident(Heq) := decomp_map_core H Heq; substitute_map_family Heq.


(** ** [Forall] *)

Ltac specialize_Forall H a := apply Forall_forall with (x:=a) in H; [ | assumption ].
Tactic Notation "specialize_Forall" hyp(H) "with" constr(x) := specialize_Forall H x.
Ltac specialize_Forall_all a := repeat
match goal with
| H : Forall ?P ?l |- _ => specialize_Forall H with a
end.


(** * Additional statements *)

(** ** [concat] *)

Lemma concat_eq_elt A (a : A) L l1 l2 :
  concat L = l1 ++ a :: l2 ->
  {'(L1, L2, l1', l2') | l1 = concat L1 ++ l1' /\ l2 = l2' ++ concat L2
                       & L = L1 ++ (l1' ++ a :: l2') :: L2 }.
Proof.
induction L as [|l' L IHL] in l1, l2 |- *; cbn; intro eq.
- destruct l1; inversion eq.
- decomp_elt_eq_app eq.
  + now esplit with (nil, L, l1, _); subst.
  + match goal with H : _ = concat L |- _ => symmetry in H; rewrite H in IHL end.
    specialize (IHL _ _ eq_refl) as [(((L1, L2), l1'), l2') [-> ->] ->].
    now split with (l' :: L1, L2, l1', l2'); [ split | ]; cbn; rewrite <- ?app_assoc.
Qed.

Lemma concat_Forall2T A B (L : list (list A)) (l : list B) R :
  Forall2T R (concat L) l -> { L' & concat L' = l & Forall2T (Forall2T R) L L' }.
Proof.
induction L as [|l' L IHL] in l, R |- *; cbn; intro F2R.
- inversion_clear F2R.
  now split with nil.
- destruct Forall2T_app_inv_l with A B R l' (concat L) l as [(l1, l2) [] ->]; [ assumption | ].
  destruct IHL with l2 R as [L' p1 p2]; [ assumption | ].
  split with (l1 :: L').
  + cbn. rewrite p1. reflexivity.
  + apply Forall2T_cons; assumption.
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

Lemma Forall_filter A f P (l : list A) : (forall a, Bool.reflect (P a) (f a)) -> Forall P (filter f l).
Proof.
intro Hspec. induction l as [|a l IHl]; [ constructor | cbn ].
destruct (Hspec a); [ constructor | ]; assumption.
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
  partition f (l1 ++ l2) = prod_map2 (@app A) (partition f l1) (partition f l2).
Proof.
induction l1 as [|a l1 IHl1]; cbn.
- destruct (partition f l2); reflexivity.
- destruct (f a); rewrite IHl1; destruct (partition f l1), (partition f l2); reflexivity.
Qed.

Lemma partition_incl1T A f (l : list A) : inclT (fst (partition f l)) l.
Proof. rewrite partition_as_filter. apply inclT_filter. Qed.

Lemma partition_incl2T A f (l : list A) : inclT (snd (partition f l)) l.
Proof. rewrite partition_as_filter. apply inclT_filter. Qed.


(** ** [incl] *)
Lemma incl_cons_cons A (a : A) l1 l2 : incl l1 l2 -> incl (a :: l1) (a :: l2).
Proof.
intro Hincl. change (a :: l1) with ((a :: nil) ++ l1). change (a :: l2) with ((a :: nil) ++ l2).
apply incl_app_app; [ intros ? ? | ]; assumption.
Qed.

#[export] Instance incl_preorder A : PreOrder (@incl A).
Proof. split; intro; [ apply incl_refl | apply incl_tran ]. Qed.


(** ** [NoDup] *)
Lemma NoDup_unit A (a : A) : NoDup (a :: nil).
Proof. constructor; [ intros [] | constructor ]. Qed.

Lemma NoDup_app_remove_m A (l1 l2 l3 : list A) : NoDup (l1 ++ l2 ++ l3) -> NoDup (l1 ++ l3).
Proof. induction l2 as [|a l2 IH]; [ exact id | ]. intros [Hnd _]%NoDup_remove. apply IH, Hnd. Qed.

Lemma NoDup_remove_iff A l l' (a : A) : NoDup (l ++ a :: l') <-> NoDup (l ++ l') /\ ~ In a (l ++ l').
Proof.
split; [ apply NoDup_remove | ].
intro Hnd. apply (@NoDup_Add _ a (l ++ l')); [ apply Add_app | assumption ].
Qed.


(** ** [last] *)
Lemma last_cons_default A (d d' : A) a l : last (a :: l) d = last (a :: l) d'.
Proof.
assert (a :: l <> nil) as Hnil by intros [=]. remember (a :: l) as l0 eqn:Heql. clear Heql a l.
induction l0 as [|a l0 IHl0] in Hnil |- *; cbn.
- contradiction Hnil. reflexivity.
- destruct l0; [ reflexivity | ].
  apply IHl0. intros [=].
Qed.

Lemma last_elt A (d : A) a l1 l2 : last (l1 ++ a :: l2) d = last (a :: l2) d.
Proof.
induction l1 as [|b l1 IHl1]; [ reflexivity | ].
rewrite <- app_comm_cons, <- IHl1. destruct l1; reflexivity.
Qed.

Lemma in_last A (d : A) l : l <> nil -> In (last l d) l.
Proof.
induction l as [|a l IHl]; intro Hnil.
- contradiction Hnil. reflexivity.
- cbn. destruct l as [|b l].
  + apply in_eq.
  + right. apply IHl. intros [=].
Qed.


(** ** [Forall] and [Exists] *)

Lemma Forall_map A B (f : A -> B) l :
  Forall (fun x => exists y, x = f y) l <-> exists l0, l = map f l0.
Proof.
induction l as [|b l IHl]; split; intro H.
- now exists (@nil A).
- constructor.
- inversion H as [|b' l' [y ->] HF]. subst.
  apply IHl in HF as [l0 ->].
  exists (y :: l0). reflexivity.
- destruct H as [[|a' l0] Heq]; inversion Heq. subst.
  constructor.
  + exists a'. reflexivity.
  + apply IHl.
    exists l0. reflexivity.
Qed.

Lemma Forall2_rev A B (R : A -> B -> Prop) l1 l2 : Forall2 R l1 l2 -> Forall2 R (rev l1) (rev l2).
Proof.
induction l1 as [|a l1 IH] in l2 |- *; intro HF; destruct l2 as [|b l2]; inversion_clear HF.
- constructor.
- cbn. apply Forall2_app.
  + apply IH. assumption.
  + now constructor.
Qed.

Lemma Forall_impl_ext A (P Q : A -> Prop) l :
  (forall a, In a l -> P a -> Q a) -> Forall P l -> Forall Q l.
Proof.
induction l as [|b l IHl]; cbn; intros HPQ HP; constructor; inversion_clear HP.
- now apply HPQ; [ left | ].
- apply IHl; [ | assumption ].
  intros a Ha. apply HPQ. right. assumption.
Qed.

Lemma Forall_remove A (eqdec : forall x y : A, {x = y} + {x <> y}) P a l :
  Forall P (remove eqdec a l) -> P a -> Forall P l.
Proof.
induction l as [|b l IHl]; cbn; intros HF HP; constructor.
- destruct (eqdec a b) as [ -> | ]; [ | inversion HF ]; assumption.
- refine (IHl _ HP).
  destruct (eqdec a b); [ | inversion HF ]; assumption.
Qed.

Lemma Forall_remove_impl A (eqdec : forall x y : A, {x = y} + {x <> y}) (P Q : A -> Prop) a l :
  Forall P (remove eqdec a l) -> (forall x, x <> a -> P x -> Q x) -> Q a -> Forall Q l.
Proof.
intros HP HPQ HQ.
apply (@Forall_remove _ eqdec _ a); [ | assumption ].
refine (Forall_impl_ext _ _ HP).
intros x Hx. apply HPQ.
apply in_remove in Hx. apply Hx.
Qed.

Lemma in_empty_remove_Forall A (eqdec : forall x y : A, {x = y} + {x <> y}) a l :
  remove eqdec a l = nil -> Forall (eq a) l.
Proof. now intros Hemp; apply (@Forall_remove _ eqdec _ a); [ rewrite Hemp | ]. Qed.


(** ** [ForallT] *)

(** Translation from [ForallT] to a list of dependent pairs *)

Fixpoint list_to_ForallT T P (l : list (sigT P)) : ForallT P (map (@projT1 T P) l) :=
  match l with
  | nil => ForallT_nil _
  | p :: l => ForallT_cons (projT1 p) (projT2 p) (list_to_ForallT l)
  end.

Fixpoint ForallT_to_list T P (l : list T) (Fl : ForallT P l) : list (sigT P) :=
  match Fl with
  | ForallT_nil _ => nil
  | ForallT_cons x Px Fl => (existT P x Px) :: (ForallT_to_list Fl)
  end.

Lemma ForallT_to_list_support T P L FL :
  map (@projT1 _ _) (@ForallT_to_list T P L FL) = L.
Proof. induction FL as [|? ? ? ? IHFL]; [ | cbn; rewrite IHFL ]; reflexivity. Defined.

Lemma ForallT_to_list_length T P (l : list T) (Fl : ForallT P l) :
  length (ForallT_to_list Fl) = length l.
Proof. induction Fl as [|? ? ? ? IHFl]; [ | cbn; rewrite IHFl ]; reflexivity. Defined.

Lemma ForallT_to_list_to_ForallT T P : forall L FL,
 rew (ForallT_to_list_support _) in list_to_ForallT (@ForallT_to_list T P L FL) = FL.
Proof.
intros L FL. induction FL as [|x l p FL IHFL]; [ reflexivity | ].
transitivity (ForallT_cons x p
             (rew [ForallT P] ForallT_to_list_support FL in
                 list_to_ForallT (ForallT_to_list FL))).
- clear. simpl. destruct (ForallT_to_list_support FL). reflexivity.
- rewrite IHFL. reflexivity.
Qed.


(** ** [Forall2T] *)

Lemma Forall2T_inT_l A B (R : A -> B -> Type) l1 l2 a :
  Forall2T R l1 l2 -> InT a l1 -> { b & InT b l2 & R a b }.
Proof.
intro HF. induction HF as [| x y ? ? ? ? IHF]; intros [].
- subst. now split with y; [ left | ].
- destruct IHF as [b Hinb HRab]; [ assumption | ].
  now split with b; [ right | ].
Qed.

Lemma Forall2T_inT_r A B (R : A -> B -> Type) l1 l2 b :
  Forall2T R l1 l2 -> InT b l2 -> { a & InT a l1 & R a b }.
Proof.
intro HF. induction HF as [| x y ? ? ? ? IHF]; intros [].
- subst. now split with x; [ left | ].
- destruct IHF as [a Hina HRab]; [ assumption | ].
  now split with a; [ right | ].
Qed.

Lemma Forall2T_rev A B (R : A -> B -> Type) l1 l2 : Forall2T R l1 l2 -> Forall2T R (rev l1) (rev l2).
Proof.
induction l1 as [|a l1 IH] in l2 |- *; intro HF; destruct l2 as [|b l2]; inversion_clear HF.
- constructor.
- cbn. apply Forall2T_app.
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
induction l1 as [|a l1 IHl1] in l2 |- *; intro Heq; [ assumption | ].
destruct l2 as [| b l2]; destr_eq Heq.
cbn. apply IHl1 in Heq as ->. reflexivity.
Qed.

Lemma length_map2 A B C (f : A -> B -> C) l1 l2 :
  length (map2 f l1 l2) <= length l1 /\ length (map2 f l1 l2) <= length l2.
Proof.
induction l1 as [|a l1 IHl1] in l2 |- *.
- split; apply le_0_n.
- destruct l2 as [| b l2].
  + split; apply le_0_n.
  + destruct (IHl1 l2).
    split; cbn; apply le_n_S; assumption.
Qed.

Lemma nth_map2 A B C (f : A -> B -> C) l1 l2 i a b c :
  i < length (map2 f l1 l2) ->
    nth i (map2 f l1 l2) c = f (nth i l1 a) (nth i l2 b).
Proof.
induction l1 as [|a' l1 IHl1] in i, l2 |- *; intro Hlt.
- inversion Hlt.
- destruct l2 as [| b' l2].
  + inversion Hlt.
  + destruct i; cbn; [ reflexivity | ].
    apply IHl1, Nat.succ_lt_mono, Hlt.
Qed.


(** ** [fold_right] *)

Lemma fold_right_id A l : fold_right (@cons A) nil l = l.
Proof. induction l; [ reflexivity | cbn; f_equal; assumption ]. Qed.

#[deprecated(since="ollibs 2.1.1", use=fold_right_id)]
Definition fold_id := fold_right_id.

Lemma fold_right_app_assoc2 A B f (g : B -> A) h (e : A) l1 l2 :
    (forall x y z, h (g x) (f y z) = f (h (g x) y) z) ->
    (f e (fold_right (fun x => h (g x)) e l2) = (fold_right (fun x => h (g x)) e l2)) ->
  fold_right (fun x => h (g x)) e (l1 ++ l2) =
  f (fold_right (fun x => h (g x)) e l1) (fold_right (fun x => h (g x)) e l2).
Proof.
intros Hassoc Hunit.
rewrite fold_right_app.
remember (fold_right (fun x => f (g x)) e l2) as r.
induction l1; cbn.
- symmetry. apply Hunit.
- rewrite <- Hassoc. f_equal. assumption.
Qed.

Lemma fold_right_app_assoc A f (e : A) l1 l2 :
  (forall x y z, f x (f y z) = f (f x y) z) -> (forall x, f e x = x) ->
  fold_right f e (l1 ++ l2) = f (fold_right f e l1) (fold_right f e l2).
Proof. intros Hassoc Hunit. apply fold_right_app_assoc2, Hunit. assumption. Qed.


(** ** [list_sum] and [repeat] *)

Lemma list_sum_repeat k n : list_sum (repeat k n) = n * k.
Proof. induction n as [|n IHn]; [ | simpl repeat; simpl list_sum; rewrite IHn ]; reflexivity. Qed.


(** ** Tactics for automatic solving *)

Ltac in_solve :=
  cbn; repeat split;
  repeat (apply in_or_app; cbn);
  repeat (
    repeat match goal with
    | H : ?P /\ ?Q |- _ => destruct H
    | H : ?P \/ ?Q |- _ => destruct H
    end;
    repeat match goal with
    | H : In _ _ |- _ => progress cbn in H
    end;
    repeat match goal with
    | H : In _ (_ :: _) |- _ => inversion H
    end;
    repeat match goal with
    | H : In _ _ |- _ => cbn in H; apply in_app_or in H as []
    end);
  intuition auto with *; fail.

Ltac Forall_simpl_hyp :=
  repeat (
    match goal with
    | H:Forall _ (_ ++ _) |- _ => let H1 := fresh H in assert (H1 := proj1 (proj1 (Forall_app _ _ _) H));
                                  let H2 := fresh H in assert (H2 := proj2 (proj1 (Forall_app _ _ _) H));
                                  clear H
    | H:Forall _ (_ :: _) |- _ => inversion H; clear H
    end).
Ltac Forall_solve_rec :=
  match goal with
  | |- Forall _ (_ ++ _) => apply (fun HF1 HF2 => proj2 (Forall_app _ _ _) (conj HF1 HF2)); Forall_solve_rec
  | |- Forall _ (_ :: _) => constructor; [ assumption | Forall_solve_rec ]
  | |- Forall _ nil => constructor
  | _ => try assumption
  end.
Ltac Forall_solve := Forall_simpl_hyp; cbn; Forall_solve_rec; fail.

Ltac ForallT_simpl_hyp :=
  repeat (
    match goal with
    | H:ForallT _ (_ ++ _) |- _ => let H1 := fresh H in assert (H1 := ForallT_app_l _ _ H);
                                   let H2 := fresh H in assert (H2 := ForallT_app_r _ _ H);
                                   clear H
    | H:ForallT _ (_ :: _) |- _ => inversion H; clear H
    end).
Ltac ForallT_solve_rec :=
  match goal with
  | |- ForallT _ (_ ++ _) => apply ForallT_app; ForallT_solve_rec
  | |- ForallT _ (_ :: _) => constructor; [ assumption | ForallT_solve_rec ]
  | |- ForallT _ nil => constructor
  | _ => try assumption
  end.
Ltac ForallT_solve := ForallT_simpl_hyp; cbn; ForallT_solve_rec; fail.


(** reflect *)

Lemma Forall_forallb_reflect A P f (l : list A) :
  (forall a, reflect (P a) (f a)) -> reflect (Forall P l) (forallb f l).
Proof.
intros Hspec.
induction l as [|a l IHl]; [ constructor; constructor | cbn ].
specialize (Hspec a).
destruct (f a), (forallb f l); inversion Hspec as [Hspect|Hspecf]; inversion IHl as [IHlt|IHlf]; constructor.
- constructor; assumption.
- intro HF. apply IHlf. inversion HF. assumption.
- intro HF. apply Hspecf. inversion HF. assumption.
- intro HF. apply IHlf. inversion HF. assumption.
Qed.

Lemma ForallT_forallb_reflectT A P f (l : list A) :
  (forall a, reflectT (P a) (f a)) -> reflectT (ForallT P l) (forallb f l).
Proof.
intro Hspec. induction l as [|a l IHl]; [ constructor; constructor | cbn ].
specialize (Hspec a).
destruct (f a), (forallb f l); inversion Hspec as [Hspect|Hspecf]; inversion IHl as [IHlt|IHlf]; constructor.
- constructor; assumption.
- intro HF. apply IHlf. inversion HF. assumption.
- intro HF. apply Hspecf. inversion HF. assumption.
- intro HF. apply IHlf. inversion HF. assumption.
Qed.


(** * Add-ons for [Lists.ListDec] *)
(* [Exists_dec] and [Forall_dec] exists in [Lists.List]
   we follow here the naming convention from [List.ListDec] *)

Lemma Forall_decidable_ext A (P : A -> Prop) l : (forall x, In x l -> decidable (P x)) -> decidable (Forall P l).
Proof.
intro Pdec. induction l as [|a l' Hrec].
- left. apply Forall_nil.
- destruct Hrec as [Hl'|Hl'].
  + intros x Hinx. apply Pdec. right. assumption.
  + destruct (Pdec a) as [Ha|Ha].
    * apply in_eq.
    * left. now apply Forall_cons.
    * right. abstract now inversion 1.
  + right. now inversion 1.
Qed.

Lemma Forall_decidable A (P : A -> Prop) (Pdec : forall x, decidable (P x)) l : decidable (Forall P l).
Proof. apply Forall_decidable_ext. intros x _. apply Pdec. Qed.

Lemma Exists_decidable_ext A (P : A -> Prop) l : (forall x, In x l -> decidable (P x)) -> decidable (Exists P l).
Proof.
intro Pdec. induction l as [|a l' Hrec].
- right. now rewrite Exists_nil.
- destruct Hrec as [Hl'|Hl'].
  + intros x Hinx. apply Pdec. right. assumption.
  + left. now apply Exists_cons_tl.
  + destruct (Pdec a) as [Ha|Ha].
    * apply in_eq.
    * left. now apply Exists_cons_hd.
    * right. now inversion 1.
Qed.

Lemma Exists_decidable A (P : A -> Prop) (Pdec : forall x, decidable (P x)) l : decidable (Exists P l).
Proof. apply Exists_decidable_ext. intros x _. apply Pdec. Qed.
