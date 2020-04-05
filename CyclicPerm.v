Require Import CPermutation List_more.

Lemma CPermutation_app_app_inv {A} : forall (l1 : list A) l2 l3 l4,
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
Proof with try assumption ; try reflexivity.
intros l1 l2 l3 l4 HC.
inversion HC as [lx ly Hx Hy].
dichot_app_exec Hx ; dichot_app_exec Hy ; subst.
- right ; left.
  exists (l ++ l0) ; exists (l0 ++ l).
  split ; [ | split ] ; 
    try (rewrite <- ? app_assoc ; apply cperm_app_rot)...
  apply cperm.
- dichot_app_exec Hy0 ; subst.
  + left.
    exists l ; exists l0 ; exists lx ; exists l5.
    split ; [ | split ; [ | split ]] ; try apply cperm...
  + right ; right ; right ; left.
    exists (l1 ++ lx) ; exists (lx ++ l1).
    split ; [ | split ] ; 
      try (rewrite <- ? app_assoc ; apply cperm_app_rot)...
    apply cperm.
- dichot_app_exec Hy1 ; subst.
  + right ; right ; left.
    exists (ly ++ l2) ; exists (l2 ++ ly).
    split ; [ | split ] ; 
      try (rewrite <- ? app_assoc ; apply cperm_app_rot)...
    apply cperm.
  + left.
    exists l ; exists ly ; exists l3 ; exists l0.
    split ; [ | split ; [ | split ]] ; try apply cperm...
- right ; right ; right ; right.
  exists (l5 ++ l0) ; exists (l0 ++ l5).
  split ; [ | split ] ; 
    try (rewrite <- ? app_assoc ; apply cperm_app_rot)...
  apply cperm.
Qed.

