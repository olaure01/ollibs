(** Automatic tactics for [CPermutationT] *)

(** * Some tactics for tentative automatic solving of [CPermutationT] goals
The main tactic is [CPermutationT_solve] which fails is the goal is not solved. *)

From OLlibs Require Import List_more CPermutationT.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


Ltac cpermT_rot :=
  cons2app; rewrite <- ? app_assoc;
  eapply CPermutationT_trans; [ apply CPermutationT_app_rot | ].

(** The parameter [20] below is arbitrary:
 the higher, the longer, the more powerful *)
Ltac CPermutationT_solve :=
  match goal with
  | |- CPermutationT _ _ =>
    list_simpl; cons2app in *;
    first [
      try cpermT_run;
      apply CPermutationT_sym;
      cpermT_run; fail
    | match goal with
      | H:CPermutationT _ _ |- CPermutationT _ _ =>
           list_simpl in H;
           try (apply (CPermutationT_trans H); cpermT_run; fail);
           try (apply CPermutationT_sym;
                apply (CPermutationT_trans H); cpermT_run; fail);
           try (apply CPermutationT_sym in H;
                apply (CPermutationT_trans H); cpermT_run; fail);
           try (apply CPermutationT_sym; apply CPermutationT_sym in H;
                apply (CPermutationT_trans H); cpermT_run; fail); fail
      end ]
  end
with cpermT_run :=
  do 20 (
  cons2app; rewrite <- ? app_assoc;
  match goal with
  | |- CPermutationT _ _ => apply CPermutationT_refl
  | |- CPermutationT (_ ++ _) _ => apply cpermT
  | H:CPermutationT _ _ |- CPermutationT _ _ => list_simpl in H; apply H
  | |- CPermutationT (_ ++ _ ++ _) _ => cpermT_rot
  | |- CPermutationT (_ ++ _ ) _ => eapply CPermutationT_trans; [ apply cpermT | ]
  | H:CPermutationT ?l1 _ |- CPermutationT ?l1 _
       => list_simpl in H;
          eapply CPermutationT_trans; [ apply H | ]
  | H:CPermutationT _ ?l1 |- CPermutationT ?l1 _
       => list_simpl in H;
          apply CPermutationT_sym in H;
          eapply CPermutationT_trans; [ apply H | ]
  | _ => idtac
  end ).
