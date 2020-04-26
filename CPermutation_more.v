(** Additional results about [CPermutation] *)

Require Import CPermutation.
Require Import List_more.

Set Implicit Arguments.

Lemma CPermutation_app_app_inv A : forall (l1 : list A) l2 l3 l4,
  CPermutation (l1 ++ l2) (l3 ++ l4) ->
     (exists l3' l3'' l4' l4'',
        CPermutation l1 (l3' ++ l4')  /\ CPermutation l2 (l3'' ++ l4'')
     /\
        CPermutation l3 (l3' ++ l3'') /\ CPermutation l4 (l4' ++ l4''))
  \/ (exists l l',
        CPermutation l1 (l4 ++ l) /\ CPermutation l3 (l2 ++ l')
          /\ CPermutation l l')
  \/ (exists l l',
        CPermutation l2 (l4 ++ l) /\ CPermutation l3 (l1 ++ l')
          /\ CPermutation l l')
  \/ (exists l l',
        CPermutation l1 (l3 ++ l) /\ CPermutation l4 (l2 ++ l')
          /\ CPermutation l l')
  \/ (exists l l',
        CPermutation l2 (l3 ++ l) /\ CPermutation l4 (l1 ++ l')
          /\ CPermutation l l').
Proof.
intros l1 l2 l3 l4 HC; inversion HC as [lx ly Hx Hy].
dichot_app_exec Hx; dichot_app_exec Hy; subst.
- right; left.
  exists (l ++ l0), (l0 ++ l).
  repeat split; rewrite <- ? app_assoc; apply CPermutation_app_rot.
- dichot_app_exec Hy0; subst.
  + now left; exists l, l0, lx, l5; repeat split.
  + right; right; right; left; exists (l1 ++ lx), (lx ++ l1).
    repeat split; rewrite <- ? app_assoc; apply CPermutation_app_rot.
- dichot_app_exec Hy1; subst.
  + right; right; left; exists (ly ++ l2), (l2 ++ ly).
    repeat split; rewrite <- ? app_assoc; apply CPermutation_app_rot.
  + now left; exists l, ly, l3, l0; repeat split.
- right; right; right; right; exists (l5 ++ l0), (l0 ++ l5).
  repeat split; rewrite <- ? app_assoc; apply CPermutation_app_rot.
Qed.
