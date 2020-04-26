(* CPermutation_solve library *)
(* v 0.1  2017/07/18   Olivier Laurent *)



(* Release Notes
     v0.1: use of cons2app instead of cons_to_app_cperm
           cons2app added in hypotheses
           some simplifications
*)


(** * Some tactics for tentative automatic solving of [CPermutation] goals
The main tactic is [cperm_solve] which fails is the goal is not solved. *)

Require Import CPermutation.
Require Import List_more.


Ltac cperm_rot :=
  cons2app ;
  rewrite <- ? app_assoc ;
  eapply CPermutation_trans ;
    [ apply CPermutation_app_rot
    | instantiate ].

(** The parameter [20] below is an arbitrary
 the higher, the longer, the more powerful *)
Ltac cperm_solve :=
  match goal with
  | |- CPermutation _ _ =>
    list_simpl ;
    cons2app_all ;
    first [
      try cperm_run ;
      apply CPermutation_sym ;
      cperm_run ; fail 
    | match goal with
      | H:CPermutation _ _ |- CPermutation _ _ =>
           list_simpl in H ;
           try (apply (CPermutation_trans H) ; cperm_run ; fail) ;
           try (apply CPermutation_sym ;
                apply (CPermutation_trans H) ; cperm_run ; fail) ;
           try (apply CPermutation_sym in H ;
                apply (CPermutation_trans H) ; cperm_run ; fail) ;
           try (apply CPermutation_sym ; apply CPermutation_sym in H ;
                apply (CPermutation_trans H) ; cperm_run ; fail) ; fail
      end ]
  end
with cperm_run :=
  do 20 (
  cons2app ;
  rewrite <- ? app_assoc ;
  match goal with
  | |- CPermutation _ _ => apply CPermutation_refl
  | |- CPermutation (_ ++ _) _ => apply cperm
  | H:CPermutation _ _ |- CPermutation _ _ => list_simpl in H ; apply H
  | |- CPermutation (_ ++ _ ++ _) _ => cperm_rot
  | |- CPermutation (_ ++ _ ) _ => eapply CPermutation_trans ;
                                  [ apply cperm
                                  | instantiate ]
  | H:CPermutation ?l1 _ |- CPermutation ?l1 _
       => list_simpl in H ;
          eapply CPermutation_trans ;
          [ apply H
          | instantiate ]
  | H:CPermutation _ ?l1 |- CPermutation ?l1 _
       => list_simpl in H ;
          apply CPermutation_sym in H ;
          eapply CPermutation_trans ;
          [ apply H
          | instantiate ]
  | _ => idtac
  end ).
