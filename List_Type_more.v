(* List_Type_more Library *)

Require Import Lia.

(** * Add-ons for List library
Usefull properties apparently missing in the List library with Type-compatible outputs. *)

Require Export ListType.

(** ** Properties about Forall_Type *)

(** ** Translation from Forall_Type to a list of dependent pairs *)

Fixpoint list_to_Forall {T} {P} (l : list (sigT P)) : Forall_Type P (map (@projT1 T P) l) :=
  match l with
  | nil => Forall_Type_nil _
  | p :: l => Forall_Type_cons (projT1 p) (projT2 p) (list_to_Forall l)
  end.

Fixpoint Forall_to_list {T} {P} {l : list T} (Fl : Forall_Type P l) : list (sigT P) :=
  match Fl with
  | Forall_Type_nil _ => nil
  | Forall_Type_cons x Px Fl => (existT P x Px) :: (Forall_to_list Fl)
  end.

Lemma Forall_to_list_support {T} {P} L FL :
  map (@projT1 _ _) (@Forall_to_list T P L FL) = L.
Proof.
induction FL ; simpl ; try rewrite IHFL ; reflexivity.
Defined.

Lemma Forall_to_list_length {T} {P} (l : list T) (Fl : Forall_Type P l) :
  length (Forall_to_list Fl) = length l.
Proof.
  induction Fl.
  - reflexivity.
  - simpl; rewrite IHFl; reflexivity.
Qed.


Import EqNotations.

Lemma Forall_to_list_to_Forall {T} {P} : forall L FL,
 rew (Forall_to_list_support _ _) in list_to_Forall (@Forall_to_list T P L FL) = FL.
Proof.
induction FL ; simpl.
- reflexivity.
- transitivity (Forall_Type_cons x p
                (rew [Forall_Type P] Forall_to_list_support l FL in 
                    list_to_Forall (Forall_to_list FL))).
   + clear.
     destruct (Forall_to_list_support l FL) ; reflexivity.
   + rewrite IHFL ; reflexivity.
Qed.

(** ** Properties about Forall2_Type *)

Lemma Forall2_Type_length {A B} : forall l1 l2 (R : A -> B -> Type),
  Forall2_Type R l1 l2 -> length l1 = length l2.
Proof with try assumption ; try reflexivity.
  intros l1 l2 R HF; induction HF...
  simpl; rewrite IHHF...
Qed.

Lemma Forall2_Type_in_l {A B} : forall l1 l2 a (R : A -> B -> Type),
  Forall2_Type R l1 l2 -> In_Type a l1 -> {b & prod (In_Type b l2) (R a b)}.
Proof with try assumption ; try reflexivity.
  intros l1 l2 a R HF.
  induction HF ; intro Hin; inversion Hin.
  - subst.
    split with y.
    split...
    left...
  - destruct IHHF as (b & Hinb & HRab)...
    split with b.
    split...
    right...
Qed.

Lemma Forall2_Type_in_r {A B} : forall l1 l2 b (R : A -> B -> Type),
  Forall2_Type R l1 l2 -> In_Type b l2 -> {a & prod (In_Type a l1) (R a b)}.
Proof with try assumption ; try reflexivity.
  intros l1 l2 b R HF.
  induction HF ; intro Hin; inversion Hin.
  - subst.
    split with x.
    split...
    left...
  - destruct IHHF as (a & Hina & HRab)...
    split with a.
    split...
    right...
Qed.

(** ** Decomposition of lists *)

Lemma decomp_length_plus {A} : forall (l : list A) n m,
    length l = n + m ->
    {' (l1 , l2) : _ & prod (length l1 = n) (prod (length l2 = m) (l = l1 ++ l2))}.
Proof with try assumption; try reflexivity.
  intros l n.
  revert l.
  induction n; intros l m Heq.
  - split with (nil, l).
    split ; [ | split ]...
  - destruct l; try inversion Heq.
    specialize (IHn l m H0) as ((l1 & l2) & (Heql1 & (Heql2 & HeqL))).
    split with (a :: l1 , l2).
    split ; [ | split ]...
    + simpl; rewrite Heql1...
    + simpl; rewrite HeqL... 
Qed.

(** ** Inversions of list equalities *)

Lemma dichot_Type_app {A} : forall (l1 : list A) l2 l3 l4,
  l1 ++ l2 = l3 ++ l4 ->
     { l2' | l1 ++ l2' = l3 /\ l2 = l2' ++ l4 }
   + { l4' | l1 = l3 ++ l4' /\ l4' ++ l2 = l4 }.
Proof with try assumption ; try reflexivity.
induction l1 ; induction l3 ; intros ;
  simpl in H ; inversion H ; subst.
- right.
  exists (@nil A).
  split ; simpl...
- left.
  exists (a::l3).
  split...
- right.
  exists (a::l1).
  split ; simpl...
- inversion H.
  apply IHl1 in H1.
  destruct H1 as [(l2' & H2'1 & H2'2) | (l4' & H4'1 & H4'2)] ;
    [left | right].
  + exists l2'.
    split...
    simpl.
    rewrite H2'1...
  + exists l4'.
    split...
    simpl.
    rewrite H4'1...
Qed.

Ltac dichot_Type_app_exec H :=
  match type of H with
  | _ ++ _ = _ ++ _ => apply dichot_Type_app in H ;
                         let l2 := fresh "l" in
                         let l4 := fresh "l" in
                         let H1 := fresh H in
                         let H2 := fresh H in
                         destruct H as [(l2 & H1 & H2) | (l4 & H1 & H2)]
  end.

Lemma dichot_Type_elt_app {A} : forall l1 (a : A) l2 l3 l4,
  l1 ++ a :: l2 = l3 ++ l4 ->
     { l2' | l1 ++ a :: l2' = l3 /\ l2 = l2' ++ l4 }
   + { l4' | l1 = l3 ++ l4' /\ l4' ++ a :: l2 = l4 }.
Proof with try reflexivity.
induction l1 ; induction l3 ; intros ;
  simpl in H ; inversion H ; subst.
- right.
  exists (@nil A).
  split ; simpl...
- left.
  exists l3.
  split...
- right.
  exists (a::l1).
  split ; simpl...
- inversion H.
  apply IHl1 in H1.
  destruct H1 as [(l' & H'1 & H'2) | (l' & H'1 & H'2)] ;
    [left | right] ;
    exists l' ;
    (split ; try assumption) ;
    simpl ;
    rewrite H'1...
Qed.

Ltac dichot_Type_elt_app_exec H :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ => apply dichot_Type_elt_app in H ;
                              let l2 := fresh "l" in
                              let l4 := fresh "l" in
                              let H1 := fresh H in
                              let H2 := fresh H in
                              destruct H as [(l2 & H1 & H2) | (l4 & H1 & H2)]
  | _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H ;
                            apply dichot_Type_elt_app in H ;
                              let l2 := fresh "l" in
                              let l4 := fresh "l" in
                              let H1 := fresh H in
                              let H2 := fresh H in
                              destruct H as [(l2 & H1 & H2) | (l4 & H1 & H2)]
  end.

Lemma trichot_Type_elt_app {A} : forall l1 (a : A) l2 l3 l4 l5,
  l1 ++ a :: l2 = l3 ++ l4 ++ l5 ->
     { l2' | l1 ++ a :: l2' = l3 /\ l2 = l2' ++ l4 ++ l5 }
   + {'(l3', l4') | l1 = l3 ++ l3' /\ l3' ++ a :: l4' = l4 /\ l2 = l4' ++ l5 }
   + { l5' | l1 = l3 ++ l4 ++ l5' /\ l5' ++ a :: l2 = l5 }.
Proof with try reflexivity ; try assumption.
induction l1 ; induction l3 ; intros ;
  simpl in H ; inversion H ; subst.
- destruct l4 ; inversion H.
  + right ; exists nil ; split...
  + left ; right ; exists (nil,l4) ; split ; [ | split ]...
- left ; left ; exists l3 ; split...
- destruct l4 ; inversion H ; subst.
  + right ; exists (a :: l1) ; split...
  + dichot_Type_elt_app_exec H3 ; subst.
    * left ; right ; exists (a1 :: l1, l) ; split ; [ | split ]...
    * right ; exists l0 ; split...
- apply IHl1 in H2.
  destruct H2 as [[(l' & H'1 & H'2) | ([pl1 pl2] & H'2 & H'3)] | (l' & H'1 & H'2)] ;
    [ left ; left | left ; right | right ].
  + exists l' ; try rewrite <- H'1 ; split...
  + destruct H'3 ; subst ; exists (pl1,pl2) ; split ; [ | split ]...
  + exists l' ; try rewrite H'1 ; split...
Qed.

Ltac trichot_Type_elt_app_exec H :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ ++ _ => apply trichot_Type_elt_app in H ;
                                   let l2 := fresh "l" in
                                   let l4 := fresh "l" in
                                   let H1 := fresh H in
                                   let H2 := fresh H in
                                   destruct H as [ [ (l2 & H1 & H2) | ([l2 l4] & H1 & H2) ]
                                                   | (l4 & H1 & H2) ] ;
                                   simpl in H1 ; simpl in H2
  | _ ++ _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H ;
                                   apply trichot_Type_elt_app in H ;
                                   let l2 := fresh "l" in
                                   let l4 := fresh "l" in
                                   let H1 := fresh H in
                                   let H2 := fresh H in
                                   destruct H as [ [ (l2 & H1 & H2) | ([l2 l4] & H1 & H2) ]
                                                   | (l4 & H1 & H2) ] ;
                                   simpl in H1 ; simpl in H2
  end.

Lemma trichot_Type_elt_elt {A} : forall l1 (a : A) l2 l3 b l4,
  l1 ++ a :: l2 = l3 ++ b :: l4 ->
     { l2' | l1 ++ a :: l2' = l3 /\ l2 = l2' ++ b :: l4 }
   + { l1 = l3 /\ a = b /\ l2 = l4 }
   + { l4' | l1 = l3 ++ b :: l4' /\ l4' ++ a :: l2 = l4 }.
Proof with try assumption ; try reflexivity.
intros l1 a l2 l3 b l4 Heq.
change (b :: l4) with ((b :: nil) ++ l4) in Heq.
apply trichot_Type_elt_app in Heq ;
  destruct Heq as [[ | ([pl1 pl2] & H'1 & H'2 & H'3)] | ] ; subst ;
  [ left ; left | left ; right | right ]...
destruct pl1 ; inversion H'2 ; subst ; [ | destruct pl1 ; inversion H1 ].
split ; [ | split ]...
simpl ; rewrite app_nil_r...
Qed.

Ltac trichot_Type_elt_elt_exec H :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l1 ++ ?x :: ?l2 =>
      apply trichot_Type_elt_elt in H ;
        let l' := fresh "l" in
        let H1 := fresh H in
        let H2 := fresh H in
        let H3 := fresh H in
        destruct H as [[(l' & H1 & H2) | (H1 & H2 & H3)] | (l' & H1 & H2)] ;
        [ (try subst l1) ; (try subst lr)
        | (try subst x) ; (try subst l1) ; (try subst l2)
        | (try subst l2) ; (try subst lh) ]
  end.


(** ** Decomposition of [map] *)

Ltac decomp_map_Type_eq H Heq :=
  match type of H with
  | _ ++ _ = map _ _ => apply app_eq_map_Type in H ;
                          let l1 := fresh "l" in
                          let l2 := fresh "l" in
                          let H1 := fresh H in
                          let H2 := fresh H in
                          let Heq1 := fresh Heq in
                          destruct H as ((l1 & l2) & Heq1 & H1 & H2) ;
                          rewrite Heq1 in Heq ; clear Heq1 ;
                          decomp_map_Type_eq H1 Heq ; decomp_map_Type_eq H2 Heq
  | _ :: _ = map _ _ => apply cons_eq_map_Type in H ;
                          let x := fresh "x" in
                          let l2 := fresh "l" in
                          let H1 := fresh H in
                          let H2 := fresh H in
                          let Heq1 := fresh Heq in
                          destruct H as ((x & l2) & Heq1 & H1 & H2) ;
                          rewrite Heq1 in Heq ; clear Heq1 ;
                          decomp_map_Type_eq H2 Heq
  | _ => idtac
  end.

Ltac decomp_map_Type H :=
  match type of H with
  | _ = map _ ?l => let l' := fresh "l" in
                    let Heq := fresh H in
                    remember l as l' eqn:Heq in H ;
                    decomp_map_Type_eq H Heq ;
                    let H' := fresh H in
                    clear l' ;
                    rename Heq into H'
  end.


(** ** [concat] *)

Lemma concat_vs_elt {A} : forall (a : A) L l1 l2,
    concat L = l1 ++ a :: l2 ->
    {' (L1,L2,l1',l2') | l1 = concat L1 ++ l1' /\ l2 = l2' ++ concat L2
                      /\ L = L1 ++ (l1' ++ a :: l2') :: L2 }.
Proof.
  intros a L.
  induction L; intros l1 l2 eq.
  - destruct l1; inversion eq.
  - simpl in eq.
    dichot_Type_elt_app_exec eq.
    + split with (nil,L,l1,l).
      subst.
      split; [ | split]; reflexivity.
    + destruct IHL with l0 l2 as ((((L1,L2),l1'),l2') & (eqb & eqt & eq)) ; [symmetry ; apply eq1 |].
      split with ((a0 :: L1),L2,l1',l2').
      subst.
      split ; [ | split]; try reflexivity.
      apply app_assoc.
Qed.

Lemma concat_Forall2_Type {A B} : forall (L : list (list A)) (l : list B) R,
    Forall2_Type R (concat L) l ->
    { L' : _ & concat L' = l & Forall2_Type (Forall2_Type R) L L' }.
Proof with try assumption.
  induction L; intros l R F2R.
  - inversion F2R; subst.
    split with nil.
    + reflexivity.
    + apply Forall2_Type_nil.
  - simpl in F2R.
    destruct Forall2_Type_app_inv_l with A B R a (concat L) l...
    destruct x.
    destruct y.
    simpl in *.
    destruct IHL with l1 R as [L' p1 p2]...
    split with (l0 :: L').
    + simpl; rewrite p1...
      symmetry...
    + apply Forall2_Type_cons...
Qed.

(** ** [Forall] and [Exists] *)

Lemma existsb_Exists_Type {A} : forall P (l : list A),
  existsb P l = true -> Exists_Type (fun x => is_true (P x)) l.
Proof.
induction l; intros H; try (now inversion H).
simpl in H.
case_eq (P a); intros Ha.
- now constructor.
- rewrite Ha in H; simpl in H.
  apply Exists_Type_cons_tl; intuition.
Qed.

Lemma Exists_Type_existsb {A} : forall P (l : list A),
  Exists_Type (fun x => is_true (P x)) l -> existsb P l = true.
Proof with try assumption.
induction l; intros H; try (now inversion H).
inversion_clear H.
- simpl; rewrite H0; reflexivity.
- apply IHl in X.
  simpl; rewrite X.
  now rewrite Bool.orb_true_r.
Qed.

Lemma forallb_Forall_Type {A} : forall P (l : list A),
  forallb P l = true -> Forall_Type (fun x => is_true (P x)) l.
Proof.
intros P l Hf.
now apply forall_Forall_Type, forallb_forall_Type.
Qed.


Section In_Forall_Type.
  Context {A : Type}.
  Variable P : A -> Type.

  Fixpoint In_Forall_Type {l} (a : A) (Pa : P a) (Fl : Forall_Type P l) : Type :=
    match Fl with
    | Forall_Type_nil _ => False
    | Forall_Type_cons b Pb Fl => ((existT P a Pa) = (existT P b Pb)) + In_Forall_Type a Pa Fl
    end.

  Lemma In_Forall_Type_elt: forall l1 l2 a (Fl : Forall_Type P (l1 ++ a :: l2)),
      {Pa & In_Forall_Type a Pa Fl}.
  Proof with try assumption.
    intros l1.
    induction l1; intros l2 a' Fl.
    - simpl in Fl.
      remember (a' :: l2).
      destruct Fl; inversion Heql.
      subst.
      split with p.
      left.
      reflexivity.
    - remember ((a :: l1) ++ a' :: l2).
      destruct Fl; inversion Heql.
      subst.
      destruct IHl1 with l2 a' Fl as (Pa , Hin)...
      split with Pa.
      right...
  Qed.

  Lemma In_Forall_Type_in : forall l a (Fl : Forall_Type P l),
      In_Type a l ->
      {Pa & In_Forall_Type a Pa Fl}.
  Proof with try assumption.
    intros l.
    induction l; intros a' Fl Hin; inversion Hin.
    - subst.
      remember (a' :: l) as l'.
      destruct Fl; inversion Heql'.
      subst.
      split with p.
      left.
      reflexivity.
    - remember (a :: l) as l'.
      destruct Fl; inversion Heql'.
      subst.
      destruct IHl with a' Fl as (Pa & Hin')...
      split with Pa.
      right...
  Qed.

  Fixpoint Forall_Type_sum (f : forall a, P a -> nat) (l : list A) (Pl : Forall_Type P l) :=
    match Pl with
    | Forall_Type_nil _ => 0
    | @Forall_Type_cons _ _ x l Px Pl => (f x Px) + (Forall_Type_sum f l Pl)
    end.

  Fixpoint Forall_Type_App l1 l2 Pl1 Pl2 :=
    match Pl1 with
    | Forall_Type_nil _ => Pl2
    | @Forall_Type_cons _ _ x l Px Pl => @Forall_Type_cons _ P x (l ++ l2) Px (Forall_Type_App l l2 Pl Pl2)
    end.

  Lemma Forall_Type_sum_app : forall f l1 l2 Pl1 Pl2,
      Forall_Type_sum f (l1 ++ l2) (Forall_Type_App l1 l2 Pl1 Pl2)
    = Forall_Type_sum f l1 Pl1 + Forall_Type_sum f l2 Pl2.
  Proof.
    intros f l1 l2 Pl1 Pl2.
    induction Pl1.
    - reflexivity.
    - simpl; rewrite IHPl1.
      apply Plus.plus_assoc.
  Qed.

  Lemma In_Forall_Type_to_In_Type : forall l (L : list A) p (PL : Forall_Type P L),
    In_Forall_Type l p PL -> In_Type l L.
  Proof with try assumption ; try reflexivity.
    intros l L p PL Hin; induction PL; inversion Hin.
    - left; inversion H; subst...
    - right; apply IHPL...
  Qed.

End In_Forall_Type.
