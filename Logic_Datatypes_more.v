(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.

(** * Logic *)

#[global]
Hint Unfold notT: core.

(* TODO make it universe polymorphic: cf CRelationClasses.iffT *)
Definition iffT (A B : Type) := ((A -> B) * (B -> A))%type.

Lemma sum_comm A B : A + B -> B + A.
Proof. intros [a | b]; [right | left]; assumption. Qed.

Lemma sum_assoc A B C : iffT ((A + B) + C) (A + (B + C)).
Proof.
split.
- intros [[a | b] | c]; [ left | right; left | right; right ]; assumption.
- intros [a | [b | c]]; [ left; left | left; right | right ]; assumption.
Qed.

Lemma prod_comm A B : A * B -> B * A.
Proof. intros [a b]. exact (b, a). Qed.

Lemma prod_assoc A B C : iffT ((A * B) * C) (A * (B * C)).
Proof.
split.
- intros [[a b] c]. exact (a, (b, c)).
- intros [a [b c]]. exact ((a, b), c).
Qed.

Definition prod_map A B (f : A -> B) p :=
  match p with
  | (a1, a2) => (f a1, f a2)
  end.

Definition prod_map2 A B C (f : A -> B -> C) p1 p2 :=
  match p1, p2 with
  | (a1, a2), (b1, b2) => (f a1 b1, f a2 b2)
  end.


(** * Datatypes *)

(* TODO compare with [ssrbool.isSome] *)
Definition is_Some T (o : option T) :=
match o with
| Some _ => True
| None => False
end.
