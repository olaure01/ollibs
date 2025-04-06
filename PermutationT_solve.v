(** Automatic tactics for [PermutationT] *)

(** * Some tactics for tentative automatic solving of [PermutationT] goals
The main tactic is [PermutationT_solve] which fails is the goal is not solved. *)

From OLlibs Require Import List_more PermutationT_more.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


Ltac pre_simpl_hyp_permT H :=
  try apply PermutationT_cons_inv in H;
  try apply PermutationT_app_inv in H;
  try apply PermutationT_app_inv in H;
  try apply PermutationT_app_middle_inv in H;
  try apply PermutationT_cons_app_inv in H;
  try (rewrite app_assoc in H; apply PermutationT_cons_app_inv in H);
  try (rewrite app_comm_cons in H; apply PermutationT_cons_app_inv in H);
  try (rewrite app_comm_cons in H; rewrite app_assoc in H; apply PermutationT_cons_app_inv in H).
Ltac simpl_hyp_permT H :=
  list_simpl in H;
  try pre_simpl_hyp_permT H;
  try (apply PermutationT_sym in H; pre_simpl_hyp_permT H; apply PermutationT_sym in H).
Ltac simpl_hyp_perm_allT :=
  repeat (
    match goal with
    | H:PermutationT _ _ |- _ => simpl_hyp_permT H
    end).

Ltac permT_rot :=
  cons2app; rewrite <- ? app_assoc;
  eapply PermutationT_trans; [ apply PermutationT_app_rot | ].

(** The parameter [20] below is arbitrary:
 the higher, the longer, the more powerful *)
Ltac PermutationT_solve :=
  match goal with
  | |- PermutationT _ _ =>
    list_simpl; try simpl_hyp_perm_allT;
    cons2app in *; try simpl_hyp_perm_allT;
    first [
      try apply PermutationT_app_tail;
      try apply PermutationT_app_middle;
      try permT_run;
      apply PermutationT_sym;
      permT_run; fail
    | match goal with
      | H:PermutationT _ _ |- PermutationT _ _ =>
            try (apply (PermutationT_trans H); permT_run; fail);
            try (apply PermutationT_sym; apply (PermutationT_trans H); permT_run; fail);
            try (apply PermutationT_sym in H; apply (PermutationT_trans H); permT_run; fail);
            try (apply PermutationT_sym; apply PermutationT_sym in H;
                 apply (PermutationT_trans H); permT_run; fail); fail
    end ]
  end
with permT_run :=
  do 20 (
  cons2app; rewrite <- ? app_assoc;
  try apply PermutationT_app_head;
  match goal with
  | |- PermutationT _ _ => apply PermutationT_refl
  | |- PermutationT (_ ++ _) _ => apply PermutationT_app_comm
  | H:PermutationT _ _ |- PermutationT _ _ => apply H
  | H:PermutationT ?l1 _ |- PermutationT (?l1 ++ _) _
       => eapply PermutationT_trans; [ apply PermutationT_app_tail; apply H | ]
  | H:PermutationT _ ?l1 |- PermutationT (?l1 ++ _) _
       => apply PermutationT_sym in H;
          eapply PermutationT_trans; [ apply PermutationT_app_tail; apply H | ]
  | |- PermutationT (_ ++ _ ++ _) _ => permT_rot
  | |- PermutationT (_ ++ _ ) _ => eapply PermutationT_trans; [ apply PermutationT_app_comm | ]
  | H:PermutationT ?l1 _ |- PermutationT ?l1 _
       => eapply PermutationT_trans; [ apply H | ]
  | H:PermutationT _ ?l1 |- PermutationT ?l1 _
       => apply PermutationT_sym in H;
          eapply PermutationT_trans; [ apply H | ]
  | _ => idtac
  end ).
