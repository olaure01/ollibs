(* Adress https://github.com/coq/coq/issues/12394 *)

From Stdlib Require Import Eqdep_dec.
From OLlibs Require Import List_more.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


Lemma injection_list_Forall_inf_cons A P :
  (forall x y : A, { x = y } + { x <> y }) ->
  forall (a : A) l p p' (F F' : Forall_inf P l),
  Forall_inf_cons a p F = Forall_inf_cons a p' F' -> p = p' /\ F = F'.
Proof.
intros Hdec a l p p' F F'
  [= ->%(inj_pair2_eq_dec _ Hdec) ->%(inj_pair2_eq_dec _ (list_eq_dec Hdec))];
  split; reflexivity.
Qed.
