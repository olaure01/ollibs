(** [nat]-labeled binary trees and bijective embedding into [nat] *)

From Stdlib Require Import PeanoNat Cantor Lia.
From OLlibs Require Import funtheory.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


#[deprecated(since="ollibs 2.1.0", use=to_nat)]
Definition cpair n m := 2 ^ n * (2 * m + 1).

Lemma Private_cpair_surj k : {'(n, m) | S k = 2 ^ n * (2 * m + 1) }.
Proof.
induction k as [k IH] using (well_founded_induction Wf_nat.lt_wf).
rewrite (Nat.div2_odd (S k)) in *. remember (Nat.odd (S k)) as b eqn:Hodd. destruct b; cbn in *.
- exists (0, Nat.div2 (S k)). cbn. lia.
- destruct k as [|k]; [inversion Hodd|].
  destruct (IH (Nat.div2 k)) as [(n, m) ->].
  + apply Nat.lt_succ_r, Nat.div2_decr. lia.
  + exists (S n, m). cbn. lia.
Qed.

#[deprecated(since="ollibs 2.1.0", use=of_nat)]
Definition dpair1 k := fst (proj1_sig (Private_cpair_surj k)).
#[deprecated(since="ollibs 2.1.0", use=of_nat)]
Definition dpair2 k := snd (proj1_sig (Private_cpair_surj k)).
#[deprecated(since="ollibs 2.1.0", use=to_nat)]
Definition pcpair n m := pred (2 ^ n * (2 * m + 1)).


(** * Coding of [nat]-labeled binary trees into [nat] *)

Inductive nattree :=
| Lnt : nattree
| Bnt : nat -> nattree -> nattree -> nattree.

Fixpoint nattree2nat t :=
match t with
| Lnt => 0
| Bnt k t1 t2 => S (to_nat (k, to_nat (nattree2nat t1, nattree2nat t2)))
end.

Lemma nattree2nat_inj : injective nattree2nat.
Proof.
intro t1. induction t1 as [|n t1' IH' t1'' IH'']; intros [|m t2' t2''] Heq;
  [ reflexivity | discriminate Heq .. | ].
unfold nattree2nat in Heq.
fold (nattree2nat t1') in Heq. fold (nattree2nat t1'') in Heq.
fold (nattree2nat t2') in Heq. fold (nattree2nat t2'') in Heq.
apply Nat.succ_inj, to_nat_inj in Heq.
assert (Heq' := f_equal snd Heq). unfold snd in Heq'. apply to_nat_inj in Heq' as [= ->%IH' ->%IH''].
injection Heq as [= ->]. reflexivity.
Qed.

Lemma nattree2nat_surj : surjective nattree2nat.
Proof.
intro y. induction y as [[|y] IH] using (well_founded_induction Wf_nat.lt_wf).
- exists Lnt. reflexivity.
- destruct (retract_surjective cancel_to_of y) as [(n, m) Hy]. rewrite Hy.
  destruct (retract_surjective cancel_to_of m) as [(n', m') Hm]. rewrite Hm.
  assert (Hle := to_nat_non_decreasing n m).
  assert (Hle' := to_nat_non_decreasing n' m').
  assert (n' < S y) as [t1 ->]%IH by lia.
  assert (m' < S y) as [t2 ->]%IH by lia.
  exists (Bnt n t1 t2). reflexivity.
Qed.
