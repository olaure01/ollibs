(** Types with inhabitant declared in Type *)

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


(** * Inhabitation *)

Variant inhabitedT A : Type := inhabitsT : A -> inhabitedT A.

Definition inhabitantT A (Hinh : inhabitedT A) := match Hinh with inhabitsT a => a end.

Lemma inhabitedT_unit : inhabitedT unit.
Proof. exact (inhabitsT tt). Qed.

Lemma inhabitedT_bool : inhabitedT bool.
Proof. exact (inhabitsT false). Qed.

Lemma inhabitedT_nat : inhabitedT nat.
Proof. exact (inhabitsT 0). Qed.

Lemma inhabitedT_option A : inhabitedT (option A).
Proof. exact (inhabitsT None). Qed.

Lemma inhabitedT_suml A B : inhabitedT A -> inhabitedT (sum A B).
Proof. exact (fun Hinh => inhabitsT (inl (inhabitantT Hinh))). Qed.
Arguments inhabitedT_suml [_] {_} _.

Lemma inhabitedT_sumr A B : inhabitedT B -> inhabitedT (sum A B).
Proof. exact (fun Hinh => inhabitsT (inr (inhabitantT Hinh))). Qed.
Arguments inhabitedT_sumr {_} [_] _.

Lemma inhabitedT_prod A B : inhabitedT A -> inhabitedT B -> inhabitedT (prod A B).
Proof. exact (fun HinhA HinhB => inhabitsT (inhabitantT HinhA, inhabitantT HinhB)). Qed.

Lemma inhabitedT_list A : inhabitedT (list A).
Proof. exact (inhabitsT nil). Qed.

Lemma inhabitedT_fun A B (f : A -> B) : inhabitedT A -> inhabitedT B.
Proof. exact (fun Hinh => inhabitsT (f (inhabitantT Hinh))). Qed.

Lemma inhabitedT_img A B : inhabitedT B -> inhabitedT (A -> B).
Proof. exact (fun Hinh => inhabitsT (fun _ => (inhabitantT Hinh))). Qed.

Lemma inhabitedT_id A : inhabitedT (A -> A).
Proof. exact (inhabitsT (@id _)). Qed.
