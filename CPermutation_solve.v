(** Automatic tactics for [CPermutation] *)

(** * Some tactics for tentative automatic solving of [CPermutation] goals
The main tactic is [CPermutation_solve] which fails is the goal is not solved. *)

From Stdlib Require Import CPermutation.
From OLlibs Require Import List_more.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


Ltac cperm_rot :=
  cons2app; rewrite <- ? app_assoc;
  eapply CPermutation_trans; [ apply CPermutation_app_rot | ].

(** The parameter [20] below is arbitrary:
 the higher, the longer, the more powerful *)
Ltac CPermutation_solve :=
  match goal with
  | |- CPermutation _ _ =>
    list_simpl; cons2app in *;
    first [
      try cperm_run;
      apply CPermutation_sym;
      cperm_run; fail
    | match goal with
      | H:CPermutation _ _ |- CPermutation _ _ =>
           list_simpl in H;
           try (apply (CPermutation_trans H); cperm_run; fail);
           try (apply CPermutation_sym;
                apply (CPermutation_trans H); cperm_run; fail);
           try (apply CPermutation_sym in H;
                apply (CPermutation_trans H); cperm_run; fail);
           try (apply CPermutation_sym; apply CPermutation_sym in H;
                apply (CPermutation_trans H); cperm_run; fail); fail
      end ]
  end
with cperm_run :=
  do 20 (
  cons2app; rewrite <- ? app_assoc;
  match goal with
  | |- CPermutation _ _ => apply CPermutation_refl
  | |- CPermutation (_ ++ _) _ => apply cperm
  | H:CPermutation _ _ |- CPermutation _ _ => list_simpl in H; apply H
  | |- CPermutation (_ ++ _ ++ _) _ => cperm_rot
  | |- CPermutation (_ ++ _ ) _ => eapply CPermutation_trans; [ apply cperm | ]
  | H:CPermutation ?l1 _ |- CPermutation ?l1 _
       => list_simpl in H;
          eapply CPermutation_trans; [ apply H | ]
  | H:CPermutation _ ?l1 |- CPermutation ?l1 _
       => list_simpl in H;
          apply CPermutation_sym in H;
          eapply CPermutation_trans; [ apply H | ]
  | _ => idtac
  end ).
