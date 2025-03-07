(** Transposition function on elements of a list *)

From Coq Require Import List Lia.
From OLlibs Require Import funtheory Permutation_Type.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


(** Transpose elements of index [n] and [n + 1] in [l] *)
Fixpoint transp A n (l : list A) :=
match n, l with
| 0, x :: y :: r => y :: x :: r
| S n, x :: r => x :: transp n r
| _, r => r
end.
Arguments transp {_} _ _.

Lemma transp_cons A n l (a : A) : transp (S n) (a :: l) = a :: transp n l.
Proof. reflexivity. Qed.

Lemma transp_nil A n : transp n (@nil A) = @nil A.
Proof. destruct n; reflexivity. Qed.

Lemma transp_app A n (l l0 : list A) :
  transp (length l0 + n) (l0 ++ l) = l0 ++ transp n l.
Proof.
induction l0 as [|a l0 IHl0] in n, l |- * using rev_ind; [ reflexivity | ].
rewrite <- ? app_assoc, <- app_comm_cons. cbn. rewrite <- transp_cons, <- IHl0.
f_equal. rewrite last_length. lia.
Qed.

Lemma transp_transp A l1 l2 (a b : A) :
  transp (length l1) (l1 ++ a :: b :: l2) = l1 ++ b :: a :: l2.
Proof.
change (b :: a :: l2) with (transp 0 (a :: b :: l2)).
rewrite <- transp_app. f_equal. lia.
Qed.

Lemma transp_idem A n : retract (@transp A n) (@transp A n).
Proof.
induction n as [|n IHn]; intros [|? [|? l]]; trivial; cbn.
- rewrite ! transp_nil. reflexivity.
- rewrite ! IHn. reflexivity.
Qed.

Lemma transp_inj A n : injective (@transp A n).
Proof. apply section_injective with (transp n), transp_idem. Qed.

Lemma transp_refl A n (l : list A) : length l < n + 2 -> transp n l = l.
Proof.
revert l. induction n as [|n IHn]; intros [|? [|? l]] Hlt; cbn; trivial.
- exfalso. cbn in Hlt. lia.
- destruct n as [|n]; cbn; reflexivity.
- f_equal. apply IHn. cbn in *. lia.
Qed.

Lemma transp_decomp A n (l : list A) : n + 1 < length l ->
  {'(l', a, b) | l = firstn n l ++ a :: b :: l' & transp n l = firstn n l ++ b :: a :: l' }.
Proof.
revert l. induction n as [|n IHn]; intros [|c l] Hlt; cbn; try (exfalso; inversion Hlt; fail).
- destruct l as [|d l]; try (exfalso; cbn in Hlt; lia; fail).
  exists (l, c, d); [ | split ]; reflexivity.
- assert (n + 1 < length l) as Hlt2 by (cbn in Hlt; lia).
  destruct (IHn _ Hlt2) as [((l2, a'), b') Heq1 Heq2]; subst.
  exists (l2, a', b'); f_equal; assumption.
Qed.

Lemma transp_length A n (l : list A) : length (transp n l) = length l.
Proof.
revert l. induction n as [|n IHn]; intros [|? l]; [ | destruct l | | cbn; rewrite IHn ]; reflexivity.
Qed.

Lemma transp_map A B (f : A -> B) n l : transp n (map f l) = map f (transp n l).
Proof.
revert l. induction n as [|n IHn]; intros [|? l]; [ | destruct l | | cbn; rewrite IHn ]; reflexivity.
Qed.

Lemma transp_perm A n (l : list A) : Permutation_Type l (transp n l).
Proof.
revert l. induction n; intros [|? l]; cbn; auto.
destruct l; repeat constructor.
Qed.

Lemma perm_transp A (l1 l2 : list A) : Permutation_Type l1 l2 ->
  { l | l2 = fold_right transp l1 l }.
Proof.
intro HP. induction HP as [ | a l1 l2 _ [l0 ->] | | l1 l2 l3 HP1 IHHP1 HP2 [l2' ->]].
- exists nil. reflexivity.
- exists (map S l0).
  induction l0 as [|? ? IHl0]; [ | cbn; rewrite <- IHl0 ]; reflexivity.
- exists (0 :: nil). reflexivity.
- destruct IHHP1 as [l1' ->].
  exists (l2' ++ l1').
  symmetry. apply fold_right_app.
Qed.
