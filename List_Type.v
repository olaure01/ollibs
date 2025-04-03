(** Properties of lists with output in [Type] *)

From Stdlib Require Import PeanoNat Compare_dec List.
Import ListNotations.
Open Scope list_scope.
From OLlibs Require Import Datatypes_more.

(* Set Mangle Names. Set Mangle Names Light. *)
Set Default Goal Selector "!".
Set Default Proof Using "Type".
Set Implicit Arguments.


#[local] Ltac Tauto.intuition_solver ::= auto with datatypes.


Section Lists.

  Variable A : Type.

  (** Informative version of [In] (output in [Type]) *)
  Fixpoint InT (a:A) (l:list A) : Type :=
    match l with
      | nil => False
      | b :: m => sum (b = a) (InT a m)
    end.

End Lists.

Section Facts.

  Variable A : Type.

  Theorem app_eq_unitT :
    forall (x y:list A) (a:A),
      x ++ y = [a] -> ((x = []) * (y = [a])) + ((x = [a]) * (y = [])).
  Proof.
    intros x y. destruct x as [| a l]; [ destruct y as [| a l] | destruct y as [| a0 l0] ]; cbn.
    - intros a [=].
    - left; split; auto.
    - intros b H. right; split; [ | reflexivity ].
      rewrite app_nil_r in H. assumption.
    - intros b H.
      injection H as [= H H0].
      symmetry in H0.
      apply app_cons_not_nil in H0 as [].
  Qed.

  (** Properties of [InT] *)
  Lemma inT_in : forall (a : A) l, InT a l -> In a l.
  Proof.
  intros a l. induction l; intros Hin; inversion Hin; try now constructor.
  right; intuition.
  Qed.

  Lemma notF_inT_notF_in : forall (F : Prop) (a : A) l,
    (InT a l -> F) -> In a l -> F.
  Proof.
  intros F a l. induction l as [| ? ? IHl]; intros Hnin Hin; inversion Hin; subst.
  - apply Hnin; now constructor.
  - apply IHl; [ | assumption ].
    intros Hin2; apply Hnin.
    now right.
  Qed.

  Lemma notT_inT_not_in : forall (a : A) l, notT (InT a l) -> ~ In a l.
  Proof.
  exact (@notF_inT_notF_in False).
  Qed.

  (** Facts about [InT] *)

  Theorem inT_eq : forall (a : A) (l : list A), InT a (a :: l).
  Proof.
    simpl; auto.
  Qed.

  Theorem inT_cons : forall (a b : A) (l : list A), InT b l -> InT b (a :: l).
  Proof.
    simpl; auto.
  Qed.

  Theorem notT_inT_cons (x a : A) (l : list A):
    iffT (notT (InT x (a::l))) ((x <> a) * notT (InT x l)).
  Proof.
    split.
    - intros Hnin. split; intros H; contradiction Hnin; [ left | right ]; auto.
    - intros [Heq Hin] [H|H]; auto.
  Qed.

  Theorem inT_nil : forall a:A, notT (InT a []).
  Proof.
    unfold not; intros a H; inversion_clear H.
  Qed.

  Lemma inT_app_sum : forall (l m : list A) (a : A),
    InT a (l ++ m) -> InT a l + InT a m.
  Proof.
    intros l m a.
    elim l; simpl; auto.
    intros a0 y H H0.
    now_show ((a0 = a) + InT a y + InT a m)%type.
    elim H0; auto.
    intro H1.
    now_show ((a0 = a) + InT a y + InT a m)%type.
    elim (H H1); auto.
  Qed.

  Lemma inT_sum_app : forall (l m : list A) (a : A),
    (InT a l + InT a m) -> InT a (l ++ m).
  Proof.
    intros l m a.
    elim l; simpl; intro H.
    - now_show (InT a m).
      elim H; auto; intro H0.
      now_show (InT a m).
      elim H0.
    - intros y H0 H1.
      destruct H1 ; intuition.
  Qed.

  Lemma inT_app_iff : forall l l' (a : A), iffT (InT a (l++l')) (InT a l + InT a l').
  Proof.
    split; auto using inT_app_sum, inT_sum_app.
  Qed.

  Theorem inT_split : forall x (l : list A), InT x l -> {'(l1,l2) | l = l1 ++ x :: l2 }.
  Proof.
  intros x l. induction l as [|a l IHl]; simpl; [ intros [] | intros [-> | Hi ] ].
  - exists (nil, l) ; auto.
  - destruct (IHl Hi) as ((l1,l2),H0).
    exists (a::l1, l2); simpl. apply f_equal. auto.
  Qed.

  Lemma inT_elt : forall (x : A) l1 l2, InT x (l1 ++ x :: l2).
  Proof. intros. apply inT_sum_app. right. apply inT_eq. Qed.

  Lemma inT_elt_inv : forall (x y : A) l1 l2,
    InT x (l1 ++ y :: l2) -> ((x = y) + InT x (l1 ++ l2))%type.
  Proof.
  intros x y l1 l2 Hin.
  apply inT_app_sum in Hin.
  destruct Hin as [Hin|[Hin|Hin]]; [right|left|right];
    try apply inT_sum_app; intuition.
  Qed.

  Lemma inT_inv : forall (a b : A) (l : list A),
    InT b (a :: l) -> ((a = b) + InT b l)%type.
  Proof. easy. Qed.


  Section FactsEqDec.

    Hypothesis eq_decT : forall x y : A, {x = y} + {x <> y}.

    Theorem inT_decT : forall (a:A) (l:list A), InT a l + notT (InT a l).
    Proof using eq_decT.
      intros a l. induction l as [| a0 l IHl].
      - right; apply inT_nil.
      - destruct (eq_decT a0 a); simpl; auto.
        destruct IHl; simpl; auto.
        right; unfold not; intros [Hc1| Hc2]; auto.
    Defined.

    Lemma in_inT : forall (a : A) l, In a l -> InT a l.
    Proof using eq_decT.
      intros a l Hin.
      destruct (inT_decT a l); [ assumption | ].
      exfalso; revert Hin.
      eapply notT_inT_not_in; assumption.
    Qed.

  End FactsEqDec.

End Facts.

#[export] Hint Resolve inT_eq inT_cons inT_inv inT_nil
                       inT_app_sum inT_sum_app: datatypes.



(*******************************************)
(** * Operations on the elements of a list *)
(*******************************************)

Section Elts.

  Variable A : Type.

  (*****************************)
  (** ** Nth element of a list *)
  (*****************************)

  Lemma nth_inT_sum_default :
    forall (n:nat) (l:list A) (d:A), (InT (nth n l d) l + (nth n l d = d))%type.
  Proof.
    intros n l d; revert n; induction l as [|? ? IHl].
    - intro n. right; destruct n; trivial.
    - intros [|n]; simpl.
      + left; auto.
      + destruct (IHl n); auto.
  Qed.

  Lemma nth_S_consT :
    forall (n:nat) (l:list A) (d a:A),
      InT (nth n l d) l -> InT (nth (S n) (a :: l) d) (a :: l).
  Proof.
    simpl; auto.
  Qed.

  (** Results about [nth] *)

  Lemma nth_InT :
    forall (n:nat) (l:list A) (d:A), n < length l -> InT (nth n l d) l.
  Proof.
    intro n. unfold lt; induction n as [| n hn]; simpl.
    - intro l. destruct l; simpl; [ inversion 2 | auto ].
    - intro l. destruct l; simpl.
      * inversion 2.
      * intros d ie; right; apply hn. now apply Nat.succ_le_mono.
  Qed.

  Lemma InT_nth l (x:A) d : InT x l ->
    { n | n < length l & nth n l d = x }.
  Proof.
    induction l as [|a l IH].
    - easy.
    - intros [H|H].
      + subst; exists 0; simpl; [ | reflexivity ]. apply Nat.lt_0_succ.
      + destruct (IH H) as [n Hn Hn'].
        apply Nat.succ_lt_mono in Hn. now exists (S n).
  Qed.

  Lemma nth_splitT n (l:list A) d : n < length l ->
    {'(l1, l2) | l = l1 ++ nth n l d :: l2 & length l1 = n }.
  Proof.
    revert l.
    induction n as [|n IH]; intros [|a l] H.
    - exists (nil, nil); now simpl.
    - exists (nil, l); now simpl.
    - exfalso; inversion H.
    - destruct (IH l) as [(l1, l2) Hl Hl1].
      + now apply Nat.succ_lt_mono.
      + exists (a::l1, l2); simpl; now f_equal.
  Qed.

  (** Results about [nth_error] *)

  Lemma nth_error_InT l n (x:A) : nth_error l n = Some x -> InT x l.
  Proof.
    revert n. induction l as [|a l IH]; intros [|n]; simpl; try easy.
    - injection 1; auto.
    - eauto.
  Qed.

 Lemma InT_nth_error l (x:A) : InT x l -> { n | nth_error l n = Some x }.
  Proof.
    induction l as [|a l IH].
    - easy.
    - intros [H|[n ?] %IH].
      + subst; now exists 0.
      + now exists (S n).
  Qed.

  Lemma nth_error_splitT l n (a:A) : nth_error l n = Some a ->
    {'(l1, l2) | l = l1 ++ a :: l2 & length l1 = n }.
  Proof.
    revert l.
    induction n as [|n IH]; intros [|x l] H; simpl in *; try easy.
    - exists (nil, l); auto. now injection H as [= ->].
    - destruct (IH _ H) as [ (l1, l2) H1 H2 ].
      exists (x::l1, l2); simpl; now f_equal.
  Qed.

End Elts.


Section ListOps.

  Variable A : Type.

  (*************************)
  (** ** Reverse           *)
  (*************************)

  Lemma inT_rev : forall l (x:A), InT x l -> InT x (rev l).
  Proof.
    intro l. induction l; simpl; intros; intuition.
    subst.
    apply inT_sum_app; right; simpl; auto.
  Qed.

(*********************************************)
(** Reverse Induction Principle on Lists  *)
(*********************************************)

  Section Reverse_Induction.

    Lemma rev_list_rect : forall P:list A-> Type,
      P [] ->
      (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
      forall l:list A, P (rev l).
    Proof.
      intros P H a l. induction l; auto.
    Qed.

    Theorem rev_rect : forall P:list A -> Type,
      P [] ->
      (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
    Proof.
      intros P Hnil Hind l.
      rewrite <- (rev_involutive l).
      apply (rev_list_rect P); simpl; auto.
    Qed.

    Lemma rev_list_rec : forall P:list A-> Set,
      P [] ->
      (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
      forall l:list A, P (rev l).
    Proof.
      intros; now apply rev_list_rect.
    Qed.

    Theorem rev_rec : forall P:list A -> Set,
      P [] ->
      (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
    Proof.
      intros; now apply rev_rect.
    Qed.

    Lemma rev_caseT (l : list A) : (l = nil) + {'(a, tl) | l = tl ++ [a] }.
    Proof.
      induction l as [|x l IHl] using rev_rect; [ left | right ]; auto.
      now exists (x, l).
    Qed.

  End Reverse_Induction.

  (*************************)
  (** ** Concatenation     *)
  (*************************)

  Lemma inT_concat : forall l y (x : list A),
    InT x l -> InT y x -> InT y (concat l).
  Proof.
    intro l. induction l as [ | a l IHl]; simpl; intros y x Hx Hy.
    - contradiction.
    - apply inT_sum_app.
      destruct Hx as [Hx | Hx]; subst; auto.
      right; now apply (IHl y x).
  Qed.

  Lemma inT_concat_inv : forall l (y : A),
    InT y (concat l) -> { x & InT x l & InT y x }.
  Proof.
    intro l. induction l as [ | a l IHl]; simpl; intros y Hy.
    - contradiction.
    - destruct (inT_app_sum _ _ _ Hy) as [Hi|Hi].
      + exists a; auto.
      + destruct (IHl y Hi) as [x ? ?].
        exists x; auto.
  Qed.

End ListOps.

(************)
(** ** Map  *)
(************)

Section Map.
  Variables (A : Type) (B : Type).
  Variable f : A -> B.

  Lemma inT_map :
    forall (l:list A) (x:A), InT x l -> InT (f x) (map f l).
  Proof.
    intro l. induction l; firstorder (subst; auto).
  Qed.

  Lemma inT_map_inv : forall l y, InT y (map f l) -> { x & f x = y & InT x l }.
  Proof.
    intro l. induction l; firstorder (subst; auto).
  Qed.

  Lemma map_eq_consT : forall l l' b,
    map f l = b :: l' -> {'(a, tl) | l = a :: tl & f a = b /\ map f tl = l' }.
  Proof.
    intros l l' b Heq.
    destruct l as [|a l]; inversion_clear Heq.
    exists (a, l); repeat split.
  Qed.

  Lemma map_eq_appT : forall l l1 l2,
    map f l = l1 ++ l2 ->
    {'(l1', l2') | l = l1' ++ l2' & map f l1' = l1 /\ map f l2' = l2 }.
  Proof.
    intro l. induction l as [| a l IHl]; simpl; intros l1 l2 Heq.
    - symmetry in Heq; apply app_eq_nil in Heq; destruct Heq; subst.
      exists (nil, nil); repeat split.
    - destruct l1; simpl in Heq; inversion Heq as [[Heq2 Htl]].
      + exists (nil, a :: l); repeat split.
      + destruct (IHl _ _ Htl) as [ (l1', l2') ? [? ?]]; subst.
        exists (a :: l1', l2'); repeat split.
  Qed.

  (** [flat_map] *)

  Lemma inT_flat_map : forall (f:A->list B) l y x,
    InT x l -> InT y (f x) -> InT y (flat_map f l).
  Proof.
    intros g l. induction l as [|? ? IHl]; simpl; intros y x Hin1 Hin2; auto.
    apply inT_sum_app.
    destruct Hin1 as [ Heq | Hin1 ].
    - subst; auto.
    - right ; apply (IHl y x Hin1 Hin2).
  Qed.

  Lemma inT_flat_map_inv : forall (f:A->list B) l y,
    InT y (flat_map f l) -> { x & InT x l & InT y (f x) }.
  Proof.
    intros g l. induction l as [|a l IHl]; simpl.
    - contradiction.
    - intros y Hi. destruct (inT_app_sum _ _ _ Hi) as [|Hi'].
      + exists a; auto.
      + destruct (IHl y Hi') as [x H1 H2].
        exists x; auto.
  Qed.

End Map.

Lemma map_ext_inT :
  forall (A B : Type)(f g:A->B) l, (forall a, InT a l -> f a = g a) -> map f l = map g l.
Proof.
  intros A B f g l. induction l as [|a l IHl]; simpl; auto.
  intros H; rewrite H by intuition; rewrite IHl; auto.
Qed.

Lemma ext_inT_map :
  forall (A B : Type)(f g:A->B) l, map f l = map g l -> forall a, InT a l -> f a = g a.
Proof.
  intros A B f g l Heq a Hin; apply inT_in in Hin.
  now apply ext_in_map with l.
Qed.


  Section Bool.
    Variable A : Type.
    Variable f : A -> bool.

    Lemma existsb_existsT :
      forall l, existsb f l = true -> { x & InT x l & f x = true }.
    Proof.
      intro l. induction l as [|a l IHl]; simpl.
      - intros [=].
      - case_eq (f a); intros H Ha.
        + exists a; intuition.
        + simpl in Ha.
          apply IHl in Ha.
          destruct Ha as [x Hin Ht].
          exists x; intuition.
    Qed.

    Lemma exists_existsbT :
      forall l x, InT x l -> f x = true -> existsb f l = true.
    Proof.
      intro l. induction l as [|a l IHl]; simpl; intros x H Hx.
      - contradiction.
      - destruct H as [->|Hi]; rewrite ? Hx; cbn; intuition.
        rewrite (IHl x Hi Hx).
        now destruct (f a).
    Qed.

    Lemma forallb_forallT :
      forall l, forallb f l = true <-> (forall x, InT x l -> f x = true).
    Proof.
      intro l. induction l as [| ? l IHl]; simpl; split; try now intuition.
      - intros Handb x [Heq|Hin]; destruct (andb_prop _ _ Handb); subst; intuition.
      - intros Hx.
        assert (forallb f l = true) by (apply IHl; intuition).
        rewrite Hx; auto.
    Qed.

    Lemma filter_InT : forall x l, InT x l -> f x = true -> InT x (filter f l).
    Proof.
      intros x l. induction l as [|a]; simpl.
      - intuition.
      - case_eq (f a); intros; simpl; intuition congruence.
    Qed.

    Lemma filter_InT_inv : forall x l, InT x (filter f l) ->
      InT x l * (f x = true)%type.
    Proof.
      intros x l. induction l as [|a l IHl]; simpl.
      - intuition.
      - case_eq (f a); intros Hi; simpl; intuition; inversion_clear Hi; intuition congruence.
    Qed.

  (** [find] *)

    Lemma find_someT l x : find f l = Some x -> InT x l * (f x = true)%type.
    Proof.
      induction l as [|a l IH]; simpl; [easy| ].
      case_eq (f a); intros Ha Eq.
      - injection Eq as [= ->]; auto.
      - destruct (IH Eq); auto.
    Qed.

    Lemma find_noneT l : find f l = None -> forall x, InT x l -> f x = false.
    Proof.
      induction l as [|a l IH]; simpl; [easy|].
      case_eq (f a); intros Ha Eq x IN; [easy|].
      destruct IN as [<-|IN]; auto.
    Qed.

  (** [partition] *)

  Theorem elements_inT_partition l l1 l2:
    partition f l = (l1, l2) ->
    forall x:A, (InT x l -> InT x l1 + InT x l2)
              * (InT x l1 + InT x l2 -> InT x l).
  Proof.
    revert l1 l2. induction l as [| a l' Hrec]; simpl; intros l1 l2 Eq x.
    - injection Eq as [= <- <-]. tauto.
    - destruct (partition f l') as (left, right).
      specialize (Hrec left right eq_refl x).
      destruct (f a); injection Eq as [= <- <-]; simpl; tauto.
  Qed.

  End Bool.


  (*******************************)
  (** ** Further filtering facts *)
  (*******************************)

  Section Filtering.
    Variables (A : Type).

    Lemma filter_ext_inT : forall (f g : A -> bool) (l : list A),
      (forall a, InT a l -> f a = g a) -> filter f l = filter g l.
    Proof.
      intros f g l H. rewrite filter_map. apply map_ext_inT. auto.
    Qed.

    Lemma ext_inT_filter : forall (f g : A -> bool) (l : list A),
      filter f l = filter g l -> (forall a, InT a l -> f a = g a).
    Proof.
      intros f g l H. rewrite filter_map in H. apply ext_inT_map. assumption.
    Qed.

  End Filtering.


  Section ListPairs.
    Variables (A : Type) (B : Type).

  (** [split] derives two lists from a list of pairs *)

    Lemma inT_split_l : forall (l:list (A*B))(p:A*B),
      InT p l -> InT (fst p) (fst (split l)).
    Proof.
      intro l. induction l as [|a l IHl]; simpl; intros p Hi; auto.
      destruct p; destruct a; destruct (split l); simpl in *.
      destruct Hi as [e|i].
      - injection e; auto.
      - right; apply (IHl _ i).
    Qed.

    Lemma inT_split_r : forall (l:list (A*B))(p:A*B),
      InT p l -> InT (snd p) (snd (split l)).
    Proof.
      intro l. induction l as [|a l IHl]; simpl; intros p Hi; auto.
      destruct p; destruct a; destruct (split l); simpl in *.
      destruct Hi as [e|i].
      - injection e; auto.
      - right; apply (IHl _ i).
    Qed.

  (** [combine] is the opposite of [split]. *)

    Lemma inT_combine_l : forall (l:list A)(l':list B)(x:A)(y:B),
      InT (x,y) (combine l l') -> InT x l.
    Proof.
      intro l. induction l as [|? l IHl].
      - simpl; auto.
      - intro l'. destruct l' as [|? l']; simpl; auto; intros x y Hin.
        + contradiction.
        + destruct Hin as [e|i].
          * injection e; auto.
          * right; apply IHl with l' y; auto.
    Qed.

    Lemma inT_combine_r : forall (l:list A)(l':list B)(x:A)(y:B),
      InT (x,y) (combine l l') -> InT y l'.
    Proof.
      intro l. induction l as [|? ? IHl].
      - simpl; intros; contradiction.
      - intro l'. destruct l' as [|? l']; simpl; auto; intros x y Hin.
        destruct Hin as [e|i].
        + injection e; auto.
        + right; apply IHl with x; auto.
    Qed.

  (** [list_prod] has the same signature as [combine] *)

    Lemma inT_prod_aux :
      forall (x:A) (y:B) (l:list B),
      InT y l -> InT (x, y) (map (fun y0:B => (x, y0)) l).
    Proof.
      intros x y l. induction l;
      [ simpl; auto
        | simpl; destruct 1 as [H1| ];
          [ left; rewrite H1; trivial | right; auto ] ].
    Qed.

    Lemma inT_prod :
      forall (l:list A) (l':list B) (x:A) (y:B),
        InT x l -> InT y l' -> InT (x, y) (list_prod l l').
    Proof.
      intros l. induction l;
      [ simpl; tauto
        | simpl; intros ? ? ? Hin ?; apply inT_sum_app; destruct Hin as [->|i];
          [ left; apply inT_prod_aux; assumption | right; auto ] ].
    Qed.

    Lemma inT_prod_inv :
      forall (l:list A)(l':list B)(x:A)(y:B),
        InT (x,y) (list_prod l l') -> InT x l * InT y l'.
    Proof.
      intros l l' x y.
      induction l as [|a l IHl]; cbn; [easy|].
      intros [[? [= -> ->]] %inT_map_inv|] %inT_app_sum; tauto.
    Qed.

  End ListPairs.


(******************************)
(** ** Set inclusion on list  *)
(******************************)

Section SetIncl.

  Variable A : Type.

  Definition inclT (l m:list A) := forall a:A, InT a l -> InT a m.
  Hint Unfold inclT : core.

  Lemma inclT_incl (l m:list A) : inclT l m -> incl l m.
  Proof.
    intros Hincl x.
    apply notF_inT_notF_in; intros Hin.
    now apply inT_in, Hincl.
  Qed.

  Lemma inclT_nil_l : forall l, inclT nil l.
  Proof.
    intros l a Hin; inversion Hin.
  Qed.

  Lemma inclT_l_nil : forall l, inclT l nil -> l = nil.
  Proof.
    intro l. destruct l as [|a l]; intros Hincl.
    - reflexivity.
    - exfalso; apply Hincl with a; simpl; auto.
  Qed.

  Lemma inclT_refl : forall l:list A, inclT l l.
  Proof.
    auto.
  Qed.
  Hint Resolve inclT_refl : core.

  Lemma inclT_tl : forall (a:A) (l m:list A), inclT l m -> inclT l (a :: m).
  Proof.
    auto with datatypes.
  Qed.
  Hint Immediate inclT_tl : core.

  Lemma inclT_tran : forall l m n:list A, inclT l m -> inclT m n -> inclT l n.
  Proof.
    auto.
  Qed.

  Lemma inclT_appl : forall l m n:list A, inclT l n -> inclT l (n ++ m).
  Proof.
    auto with datatypes.
  Qed.
  Hint Immediate inclT_appl : core.

  Lemma inclT_appr : forall l m n:list A, inclT l n -> inclT l (m ++ n).
  Proof.
    auto with datatypes.
  Qed.
  Hint Immediate inclT_appr : core.

  Lemma inclT_cons :
    forall (a:A) (l m:list A), InT a m -> inclT l m -> inclT (a :: l) m.
  Proof.
    unfold incl; simpl; intros a l m H H0 a0 H1.
    now_show (InT a0 m).
    elim H1.
    - now_show (a = a0 -> InT a0 m).
      intro; subst; auto.
    - now_show (InT a0 l -> InT a0 m).
      auto.
  Qed.
  Hint Resolve inclT_cons : core.

  Lemma inclT_cons_inv : forall (a:A) (l m:list A),
    inclT (a :: l) m -> InT a m * inclT l m.
  Proof.
    intros a l m Hi.
    split; [ | intros ? ? ]; apply Hi; simpl; auto.
  Qed.

  Lemma inclT_app : forall l m n:list A,
    inclT l n -> inclT m n -> inclT (l ++ m) n.
  Proof.
    unfold incl; simpl; intros l m n H H0 a H1.
    now_show (InT a n).
    elim (inT_app_sum _ _ _ H1); auto.
  Qed.
  Hint Resolve inclT_app : core.

  Lemma inclT_app_app : forall l1 l2 m1 m2:list A,
    inclT l1 m1 -> inclT l2 m2 -> inclT (l1 ++ l2) (m1 ++ m2).
  Proof.
    intros.
    apply inclT_app; [ apply inclT_appl | apply inclT_appr]; assumption.
  Qed.

  Lemma inclT_app_inv : forall l1 l2 m : list A,
    inclT (l1 ++ l2) m -> inclT l1 m * inclT l2 m.
  Proof.
    intro l1. induction l1 as [|? l1 IHl1]; intros l2 m Hin; split; auto.
    - apply inclT_nil_l.
    - intros b Hb; inversion_clear Hb; subst; apply Hin.
      + now constructor.
      + simpl; apply inT_cons.
        apply inclT_appl with l1; [ apply inclT_refl | assumption ].
    - apply IHl1.
      apply inclT_cons_inv in Hin.
      now destruct Hin.
  Qed.

  Lemma inclT_filter f l : inclT (filter f l) l.
  Proof. intros x Hin; apply filter_InT_inv in Hin; intuition. Qed.

End SetIncl.

Lemma inclT_map A B (f : A -> B) l1 l2 : inclT l1 l2 -> inclT (map f l1) (map f l2).
Proof.
  intros Hincl x Hinx.
  destruct (inT_map_inv _ _ _ Hinx) as [y <- Hiny].
  apply inT_map; intuition.
Qed.

#[export] Hint Resolve inclT_refl inclT_tl inclT_tran
                       inclT_appl inclT_appr inclT_cons inclT_app: datatypes.


Section Add.

  Variable A : Type.

  (* [AddT a l l'] means that [l'] is exactly [l], with [a] added
     once somewhere *)
  Inductive AddT (a:A) : list A -> list A -> Type :=
    | AddT_head l : AddT a l (a::l)
    | AddT_cons x l l' : AddT a l l' -> AddT a (x::l) (x::l').

  Lemma AddT_Add a l1 l2 : AddT a l1 l2 -> Add a l1 l2.
  Proof.
    intros HA; induction HA; now constructor.
  Qed.

  Lemma notF_AddT_notF_Add (F:Prop) a l1 l2 : (AddT a l1 l2 -> F) -> Add a l1 l2 -> F.
  Proof.
    intros HnA HA; induction HA as [|? ? ? ? IHHA].
    - apply HnA; constructor.
    - apply IHHA; intros HAT; apply HnA; now constructor.
  Qed.

  Lemma notT_AddT_not_Add a l1 l2 : notT (AddT a l1 l2) -> ~ Add a l1 l2.
  Proof.
    exact (@notF_AddT_notF_Add False a l1 l2).
  Qed.

  Lemma AddT_app a l1 l2 : AddT a (l1++l2) (l1++a::l2).
  Proof.
    induction l1; simpl; now constructor.
  Qed.

  Lemma AddT_split a l l' :
    AddT a l l' -> {'(l1, l2) | l = l1++l2 & l' = l1++a::l2 }.
  Proof.
   induction 1 as [l|x ? ? ? IH].
   - exists (nil, l); split; trivial.
   - destruct IH as [(l1, l2) Hl Hl'].
     exists (x::l1, l2); simpl; f_equal; trivial.
  Qed.

  Lemma AddT_inT a l l' : AddT a l l' ->
   forall x, InT x l' -> InT x (a::l).
  Proof.
   induction 1; intros; simpl in *; firstorder.
  Qed.

  Lemma AddT_inT_inv a l l' : AddT a l l' ->
   forall x, InT x (a::l) -> InT x l'.
  Proof.
   induction 1; intros; simpl in *; intuition.
  Qed.

  Lemma AddT_length a l l' : AddT a l l' -> length l' = S (length l).
  Proof.
   induction 1; simpl; auto.
  Qed.

  Lemma AddT_inv a l : InT a l -> { l' & AddT a l' l }.
  Proof.
   intro Ha. destruct (inT_split _ _ Ha) as [(l1,l2) ->].
   exists (l1 ++ l2). apply AddT_app.
  Qed.

  Lemma inclT_AddT_inv a l u v :
    notT (InT a l) -> inclT (a::l) v -> AddT a u v -> inclT l u.
  Proof.
   intros Ha H AD y Hy.
   assert (Hy' : InT y (a::u)).
   { apply (AddT_inT AD). apply H; simpl; auto. }
   destruct Hy'; [ subst; now elim Ha | trivial ].
  Qed.

End Add.


Section ReDun.

  Variable A : Type.

  Inductive NoDupT : list A -> Type :=
    | NoDupT_nil : NoDupT nil
    | NoDupT_cons : forall x l, notT (InT x l) -> NoDupT l -> NoDupT (x::l).

  Lemma NoDup_NoDupT : forall l : list A, NoDup l -> NoDupT l.
  Proof.
  intro l. induction l as [|? ? IHl]; intros Hnd; constructor.
  - intros Hnin.
    apply inT_in in Hnin.
    inversion Hnd; intuition.
  - apply IHl; now inversion Hnd.
  Qed.

  Lemma NoDupT_NoDup : forall l : list A, NoDupT l -> NoDup l.
  Proof.
  intro l. induction l as [|? ? IHl]; intros Hnd; constructor.
  - apply notT_inT_not_in; intros Hnin.
    inversion Hnd; intuition.
  - apply IHl; now inversion Hnd.
  Qed.

  Theorem NoDupT_cons_imp a l:
    NoDupT (a::l) -> notT (InT a l) * NoDupT l.
  Proof.
    intros Hd; inversion Hd; subst; split; assumption.
  Qed.

  Lemma NoDupT_length_inclT l l' :
    NoDupT l -> length l' <= length l -> inclT l l' -> inclT l' l.
  Proof.
   intros N. revert l'. induction N as [|a l Hal N IH].
   - intro l'. destruct l'; auto.
     simpl; intro Hl; exfalso; inversion Hl.
   - intros l' E H x Hx.
     destruct (AddT_inv a l') as (l'', AD). { apply H; simpl; auto. }
     apply (AddT_inT AD) in Hx. simpl in Hx.
     destruct Hx as [Hx|Hx]; [left; trivial|right].
     revert x Hx. apply (IH l''); trivial.
     * apply le_S_n. now rewrite <- (AddT_length AD).
     * now apply inclT_AddT_inv with a l'.
  Qed.

End ReDun.


Section NatSeq.

  (** [seq] computes the sequence of [len] contiguous integers *)


  Lemma inT_seq len start n :
    start <= n < start+len -> InT n (seq start len).
  Proof.
    revert start. induction len as [|len IHlen]; intros start.
    - rewrite Nat.add_0_r.
      intros (H,H'). apply (Nat.lt_irrefl start).
      eapply Nat.le_lt_trans; eassumption.
    - intros [H1 H2].
      destruct (le_lt_eq_dec _ _ H1).
      + right. rewrite Nat.add_succ_r in H2. now apply IHlen.
      + left. assumption.
  Qed.

  Lemma inT_seq_inv len start n :
    InT n (seq start len) -> start <= n < start+len.
  Proof.
   revert start. induction len as [|? IHlen]; simpl; intros start H.
   - inversion H.
   - rewrite Nat.add_succ_r.
     destruct H as [e|i]; subst.
     + split; [ reflexivity | ].
       rewrite <- Nat.add_succ_l. apply Nat.le_add_r.
     + apply IHlen in i as [H1 H2]. split.
       * transitivity (S start); [ | assumption ]. apply Nat.le_succ_diag_r.
       * rewrite <- Nat.add_succ_l. assumption.
  Qed.

 End NatSeq.

Section Exists_Forall.

  (** * Existential and universal predicates over lists *)

  Variable A:Type.

  Section One_predicate_Type.

    Variable P:A->Type.

    Inductive Exists_inf : list A -> Type :=
      | Exists_inf_cons_hd : forall x l, P x -> Exists_inf (x::l)
      | Exists_inf_cons_tl : forall x l, Exists_inf l -> Exists_inf (x::l).

    Hint Constructors Exists_inf : core.

    Lemma Exists_inf_exists (l:list A) :
      Exists_inf l -> { x  & InT x l & P x }.
    Proof.
      induction 1; firstorder.
    Qed.

    Lemma exists_Exists_inf (l:list A) x :
      InT x l -> P x -> Exists_inf l.
    Proof.
      induction l; firstorder; subst; auto.
    Qed.

    Lemma Exists_inf_nth l :
      Exists_inf l -> {'(i, d) & i < length l & P (nth i l d) }.
    Proof.
      intros HE; apply Exists_inf_exists in HE.
      destruct HE as [a Hin HP].
      apply InT_nth with (d := a) in Hin; destruct Hin as [i Hl Heq].
      rewrite <- Heq in HP.
      now exists (i, a).
    Qed.

    Lemma nth_Exists_inf l i d :
      i < length l -> P (nth i l d) -> Exists_inf l.
    Proof.
      intros Hl HP.
      refine (exists_Exists_inf _ _ HP).
      apply nth_InT; assumption.
    Qed.

    Lemma Exists_inf_nil : notT (Exists_inf nil).
    Proof. inversion 1. Qed.

    Lemma Exists_inf_cons x l:
      Exists_inf (x::l) -> P x + Exists_inf l.
    Proof. inversion 1; auto. Qed.

    Lemma Exists_inf_app l1 l2 :
      Exists_inf (l1 ++ l2) -> Exists_inf l1 + Exists_inf l2.
    Proof.
      induction l1; simpl; intros HE; try now intuition.
      inversion_clear HE; intuition.
    Qed.

    Lemma Exists_inf_app_l l1 l2 :
      Exists_inf l1 -> Exists_inf (l1 ++ l2).
    Proof.
      induction l1; simpl; intros HE; try now intuition.
      inversion_clear HE; intuition.
    Qed.

    Lemma Exists_inf_app_r l1 l2 :
      Exists_inf l2 -> Exists_inf (l1 ++ l2).
    Proof.
      induction l1; simpl; intros HE; try now intuition.
    Qed.

    Lemma Exists_inf_rev l : Exists_inf l -> Exists_inf (rev l).
    Proof.
      induction l; intros HE; intuition.
      inversion_clear HE; simpl.
      - apply Exists_inf_app_r; intuition.
      - apply Exists_inf_app_l; intuition.
    Qed.

    Lemma Exists_inf_decT l:
      (forall x:A, P x + notT (P x)) -> Exists_inf l + notT (Exists_inf l).
    Proof.
      intro Pdec. induction l as [|a l' Hrec].
      - right. now apply Exists_inf_nil.
      - destruct Hrec as [Hl'|Hl'].
        * left. now apply Exists_inf_cons_tl.
        * destruct (Pdec a) as [Ha|Ha].
          + left. now apply Exists_inf_cons_hd.
          + right. now inversion_clear 1.
    Defined.

    Lemma Exists_inf_fold_right l :
      Exists_inf l -> fold_right (fun x => sum (P x)) False l.
    Proof.
      induction l; simpl; intros HE; try now inversion HE; intuition.
    Qed.

    Lemma fold_right_Exists_inf l :
      fold_right (fun x => sum (P x)) False l -> Exists_inf l.
    Proof.
      induction l; simpl; intros HE; try now inversion HE; intuition.
    Qed.

    Lemma inclT_Exists_inf l1 l2 : inclT l1 l2 -> Exists_inf l1 -> Exists_inf l2.
    Proof.
      intros Hincl HE.
      apply Exists_inf_exists in HE; destruct HE as [a Hin HP].
      apply exists_Exists_inf with a; intuition.
    Qed.

    Inductive Forall_inf : list A -> Type :=
      | Forall_inf_nil : Forall_inf nil
      | Forall_inf_cons : forall x l, P x -> Forall_inf l -> Forall_inf (x::l).

    Hint Constructors Forall_inf : core.

    Lemma Forall_inf_forall (l:list A):
      Forall_inf l -> forall x, InT x l -> P x.
    Proof.
      induction 1; firstorder; subst; auto.
    Qed.

    Lemma forall_Forall_inf (l:list A):
      (forall x, InT x l -> P x) -> Forall_inf l.
    Proof.
      induction l; intuition.
    Qed.

    Lemma Forall_inf_nth l :
      Forall_inf l -> forall i d, i < length l -> P (nth i l d).
    Proof.
      intros HF i d Hl.
      apply Forall_inf_forall with (x := nth i l d) in HF.
      - assumption.
      - apply nth_InT; assumption.
    Qed.

    Lemma nth_Forall_inf l :
      (forall i d, i < length l -> P (nth i l d)) -> Forall_inf l.
    Proof.
      intros HF.
      apply forall_Forall_inf; intros a Hin.
      apply InT_nth with (d := a) in Hin; destruct Hin as [i Hl <-]; intuition.
    Qed.

    Lemma Forall_inf_inv : forall (a:A) l, Forall_inf (a :: l) -> P a.
    Proof.
      intros ? ? H; inversion H; trivial.
    Qed.

    Theorem Forall_inf_inv_tail : forall (a:A) l, Forall_inf (a :: l) -> Forall_inf l.
    Proof.
      intros ? ? H; inversion H; trivial.
    Qed.

    Lemma Forall_inf_app_l l1 l2 :
      Forall_inf (l1 ++ l2) -> Forall_inf l1.
    Proof.
      induction l1; simpl; intros HF; try now intuition.
      inversion_clear HF; intuition.
    Qed.

    Lemma Forall_inf_app_r l1 l2 :
      Forall_inf (l1 ++ l2) -> Forall_inf l2.
    Proof.
      induction l1; simpl; intros HF; try now intuition.
      inversion_clear HF; intuition.
    Qed.

    Lemma Forall_inf_app l1 l2 :
      Forall_inf l1 -> Forall_inf l2 -> Forall_inf (l1 ++ l2).
    Proof.
      induction l1; simpl; intros HF1 HF2; try now intuition.
      inversion_clear HF1; intuition.
    Qed.

    Lemma Forall_inf_elt a l1 l2 : Forall_inf (l1 ++ a :: l2) -> P a.
    Proof.
      intros HF; apply Forall_inf_app_r in HF; now inversion HF.
    Qed.

    Lemma Forall_inf_rev l : Forall_inf l -> Forall_inf (rev l).
    Proof.
      induction l; intros HF; intuition.
      inversion_clear HF; simpl; apply Forall_inf_app; intuition.
    Qed.

    Lemma Forall_inf_rect' : forall (Q : list A -> Type),
      Q [] -> (forall b l, P b -> Q (b :: l)) -> forall l, Forall_inf l -> Q l.
    Proof.
      intros Q H H' l; induction l; intro; [|eapply H', Forall_inf_inv]; eassumption.
    Qed.

    Lemma Forall_inf_decT :
      (forall x:A, P x + notT (P x)) -> forall l:list A, Forall_inf l + notT (Forall_inf l).
    Proof.
      intros Pdec l. induction l as [|a l' Hrec].
      - left. apply Forall_inf_nil.
      - destruct Hrec as [Hl'|Hl'].
        + destruct (Pdec a) as [Ha|Ha].
          * left. now apply Forall_inf_cons.
          * right. abstract now inversion 1.
        + right. abstract now inversion 1.
    Defined.

    Lemma Forall_inf_fold_right l :
      Forall_inf l -> fold_right (fun x => prod (P x)) True l.
    Proof.
      induction l; simpl; intros HF; try now inversion HF; intuition.
    Qed.

    Lemma fold_right_Forall_inf l :
      fold_right (fun x => prod (P x)) True l -> Forall_inf l.
    Proof.
      induction l; simpl; intros HF; try now inversion HF; intuition.
    Qed.

    Lemma inclT_Forall_inf l1 l2 : inclT l2 l1 -> Forall_inf l1 -> Forall_inf l2.
    Proof.
      intros Hincl HF.
      apply forall_Forall_inf; intros a Ha.
      apply Forall_inf_forall with (x:=a) in HF; intuition.
    Qed.

  End One_predicate_Type.

  Lemma Exists_inf_Exists (P:A->Prop) l : Exists_inf P l -> Exists P l.
  Proof. now induction 1; constructor. Qed.

  Lemma Forall_inf_Forall (P:A->Prop) l : Forall_inf P l -> Forall P l.
  Proof. now induction 1; constructor. Qed.

  Theorem Exists_inf_arrow : forall (P Q : A -> Type), (forall a : A, P a -> Q a) ->
    forall l, Exists_inf P l -> Exists_inf Q l.
  Proof.
    intros P Q H l H0.
    induction H0 as [x l p|x ? ? IH].
    - apply (Exists_inf_cons_hd Q x l (H x p)).
    - apply (Exists_inf_cons_tl x IH).
  Qed.

  Lemma Exists_inf_sum : forall (P Q : A -> Type) l,
    Exists_inf P l + Exists_inf Q l -> Exists_inf (fun x => P x + Q x)%type l.
  Proof.
    intros P Q l. induction l as [|? ? IHl]; intros [H | H]; inversion H; subst.
    1,3: apply Exists_inf_cons_hd; auto.
    all: apply Exists_inf_cons_tl, IHl; auto.
  Qed.

  Lemma Exists_inf_sum_inv : forall (P Q : A -> Type) l,
    Exists_inf (fun x => P x + Q x)%type l -> Exists_inf P l + Exists_inf Q l.
  Proof.
    intros P Q l. induction l as [|? ? IHl]; intro Hl; inversion Hl as [ ? ? H | ? ? H ]; subst.
    - inversion H; now repeat constructor.
    - destruct (IHl H); now repeat constructor.
  Qed.

  Lemma Forall_inf_arrow : forall (P Q : A -> Type), (forall a, P a -> Q a) ->
    forall l, Forall_inf P l -> Forall_inf Q l.
  Proof.
    intros P Q HPQ l. induction l; intros H; inversion H; constructor; auto.
  Qed.

  Lemma Forall_inf_prod : forall (P Q : A -> Type) l,
    Forall_inf P l -> Forall_inf Q l -> Forall_inf (fun x => P x * Q x)%type l.
  Proof.
    intros P Q l. induction l; intros HP HQ; constructor; inversion HP; inversion HQ; auto.
  Qed.

  Lemma Forall_inf_prod_inv : forall (P Q : A -> Type) l,
    Forall_inf (fun x => P x * Q x)%type l -> Forall_inf P l * Forall_inf Q l.
  Proof.
    intros P Q l. induction l; intro Hl; split; constructor; inversion Hl; firstorder.
  Qed.

  Lemma Forall_inf_Exists_inf_notT (P:A->Type)(l:list A) :
   Forall_inf (fun x => notT (P x)) l -> notT (Exists_inf P l).
  Proof.
   induction l; intros HF HE; inversion HE; inversion HF; [ contradiction | apply IHl; assumption ].
  Qed.

  Lemma Exists_inf_notT_Forall_inf (P:A->Type)(l:list A) :
   notT (Exists_inf P l) -> Forall_inf (fun x => notT (P x)) l.
  Proof.
   induction l as [|? ? IHl]; intros HE; constructor.
   - intros Ha; apply HE.
     now constructor.
   - apply IHl; intros HF; apply HE.
     now constructor.
  Qed.

  Lemma Exists_inf_Forall_inf_notT (P:A->Type)(l:list A) :
    Exists_inf (fun x => notT (P x)) l -> notT (Forall_inf P l).
  Proof.
   induction l; intros HE HF; inversion HE; inversion HF; [ contradiction | apply IHl; assumption ].
  Qed.

  Lemma Forall_inf_notT_Exists_inf (P:A->Type)(l:list A) :
    (forall x, P x + notT (P x)) ->
    notT (Forall_inf P l) -> Exists_inf (fun x => notT (P x)) l.
  Proof.
   intro Dec.
   induction l as [|a l IHl]; intros HF.
   - contradiction HF. constructor.
   - destruct (Dec a) as [ Ha | Hna ].
     + apply Exists_inf_cons_tl, IHl.
       intros HFl.
       apply HF; now constructor.
     + now apply Exists_inf_cons_hd.
  Qed.

  Lemma Forall_inf_Exists_inf_decT (P:A->Type) :
    (forall x:A, P x + notT (P x)) ->
    forall l:list A, Forall_inf P l + Exists_inf (fun x => notT (P x)) l.
  Proof.
    intros Dec l.
    destruct (Forall_inf_decT P Dec l); [left|right]; trivial.
    now apply Forall_inf_notT_Exists_inf.
  Defined.

  Lemma inclT_Forall_inf_inT l l' :
    inclT l l' -> Forall_inf (fun x => InT x l') l.
  Proof. now intros; apply forall_Forall_inf. Qed.

  Lemma Forall_inf_inT_inclT l l' :
    Forall_inf (fun x => InT x l') l -> inclT l l'.
  Proof. now intros HF x Hin; apply Forall_inf_forall with (x:= x) in HF. Qed.

End Exists_Forall.

#[export] Hint Constructors Exists_inf Forall_inf : core.

Lemma exists_Forall_inf A B : forall (P : A -> B -> Type) l,
  { k & Forall_inf (P k) l } -> Forall_inf (fun x => { k & P k x }) l.
Proof.
  intros P l. induction l as [|? ? IHl]; intros [k HF]; constructor; inversion_clear HF.
  - now exists k.
  - now apply IHl; exists k.
Qed.

Lemma Forall_inf_image A B : forall (f : A -> B) l,
  Forall_inf (fun y => { x | y = f x }) (map f l).
Proof.
  intros f l. induction l as [ | a l IHl ]; constructor.
  - now exists a.
  - now apply IHl; exists l.
Qed.

Lemma Forall_inf_image_inv A B : forall (f : A -> B) l,
  Forall_inf (fun y => { x | y = f x }) l -> { l' | l = map f l' }.
Proof.
  intros f l. induction l as [ | a l IHl ]; intros HF.
  - exists nil; reflexivity.
  - inversion_clear HF as [| ? ? [x ->] HFtl].
    destruct (IHl HFtl) as [l' ->].
    now exists (x :: l').
Qed.

Lemma concat_nil_Forall_inf A : forall (l : list (list A)),
  concat l = nil -> Forall_inf (fun x => x = nil) l.
Proof.
  intro l. induction l; simpl; intros Hc; auto.
  apply app_eq_nil in Hc.
  constructor; firstorder.
Qed.

Lemma Forall_inf_concat_nil A : forall (l : list (list A)),
  Forall_inf (fun x => x = nil) l -> concat l = nil.
Proof.
  intro l. induction l as [|? ? IHl]; simpl; intros Hc; auto.
  inversion Hc; subst; simpl.
  now apply IHl.
Qed.

Lemma inT_flat_map_Exists_inf A B : forall (f : A -> list B) x l,
  InT x (flat_map f l) -> Exists_inf (fun y => InT x (f y)) l.
Proof.
  intros f x l Hin.
  destruct (inT_flat_map_inv _ _ _ Hin) as [y Hin1 Hin2].
  now apply exists_Exists_inf with y.
Qed.

Lemma Exists_inf_inT_flat_map A B : forall (f : A -> list B) x l,
  Exists_inf (fun y => InT x (f y)) l -> InT x (flat_map f l).
Proof.
  intros f x l HE.
  destruct (Exists_inf_exists HE) as [y Hin1 Hin2].
  now apply inT_flat_map with y.
Qed.

Lemma notT_inT_flat_map_Forall_inf A B : forall (f : A -> list B) x l,
  notT (InT x (flat_map f l)) -> Forall_inf (fun y => notT (InT x (f y))) l.
Proof.
  intros f x l Hnin.
  apply Exists_inf_notT_Forall_inf.
  now intros HE; apply Exists_inf_inT_flat_map in HE.
Qed.

Lemma Forall_inf_notT_inT_flat_map A B : forall (f : A -> list B) x l,
  Forall_inf (fun y => notT (InT x (f y))) l -> notT (InT x (flat_map f l)).
Proof.
  intros f x l HF Hin.
  apply Forall_inf_Exists_inf_notT in HF.
  apply HF, inT_flat_map_Exists_inf, Hin.
Qed.


Section Forall2_inf.

  (** [Forall2_inf]: stating that elements of two lists are pairwise related. *)

  Variables A B : Type.
  Variable R : A -> B -> Type.

  Inductive Forall2_inf : list A -> list B -> Type :=
    | Forall2_inf_nil : Forall2_inf [] []
    | Forall2_inf_cons : forall x y l l',
      R x y -> Forall2_inf l l' -> Forall2_inf (x::l) (y::l').

  Hint Constructors Forall2_inf : core.

  Theorem Forall2_inf_refl : Forall2_inf [] [].
  Proof. intros; apply Forall2_inf_nil. Qed.

  Theorem Forall2_inf_app_inv_l : forall l1 l2 l,
    Forall2_inf (l1 ++ l2) l ->
    {'(l1', l2') : _ & (Forall2_inf l1 l1' * Forall2_inf l2 l2')%type
                     & l = l1' ++ l2' }.
  Proof.
    intro l1. induction l1 as [|a l1 IHl1]; intros l1' l2' HF.
    - exists (nil, l2'); auto.
    - simpl in HF; inversion_clear HF as [|? y ? ? ? HF'].
      apply IHl1 in HF' as [(l1'',l2'') [HF1 HF2] ->].
      assert (Forall2_inf (a :: l1) (y :: l1'')) as HF3 by auto.
      exists (y :: l1'', l2''); auto.
  Qed.

  Theorem Forall2_inf_app_inv_r : forall l1 l2 l,
    Forall2_inf l (l1 ++ l2) ->
    {'(l1', l2') : _ & (Forall2_inf l1' l1 * Forall2_inf l2' l2)%type
                     & l = l1' ++ l2' }.
  Proof.
    intro l1. induction l1 as [|a l1 IHl1]; intros l1' l2' HF.
    - exists (nil, l2'); auto.
    - simpl in HF; inversion_clear HF as [|x ? ? ? ? HF'].
      apply IHl1 in HF' as [(l1'',l2'') [HF1 HF2] ->].
      assert (Forall2_inf (x :: l1'') (a :: l1)) as HF3 by auto.
      exists (x :: l1'', l2''); auto.
  Qed.

  Theorem Forall2_inf_app : forall l1 l2 l1' l2',
    Forall2_inf l1 l1' -> Forall2_inf l2 l2' -> Forall2_inf (l1 ++ l2) (l1' ++ l2').
  Proof.
    intros l1 l2 l1' l2' HF1 HF2. induction l1 in l1', HF1, HF2 |- *; inversion HF1; subst; simpl; auto.
  Qed.

  Lemma Forall2_inf_length : forall l1 l2,
    Forall2_inf l1 l2 -> length l1 = length l2.
  Proof.
    intros l1 l2 HF; induction HF as [|? ? ? ? ? ? IHHF]; auto.
    now simpl; rewrite IHHF.
  Qed.

End Forall2_inf.

#[export] Hint Constructors Forall2_inf : core.

Lemma Forall2_inf_Forall2 {A B} (R : A -> B -> Prop) l1 l2 :
  Forall2_inf R l1 l2 -> Forall2 R l1 l2.
Proof. induction 1 ; auto. Qed.


Section ForallPairs_inf.

  (** [ForallPairs_inf] : specifies that a certain relation should
    always hold when inspecting all possible pairs of elements of a list. *)

  Variable A : Type.
  Variable R : A -> A -> Type.

  Definition ForallPairs_inf l :=
    forall a b, InT a l -> InT b l -> R a b.

  (** [ForallOrdPairs_inf] : we still check a relation over all pairs
     of elements of a list, but now the order of elements matters. *)

  Inductive ForallOrdPairs_inf : list A -> Type :=
    | FOP_inf_nil : ForallOrdPairs_inf nil
    | FOP_inf_cons : forall a l,
      Forall_inf (R a) l -> ForallOrdPairs_inf l -> ForallOrdPairs_inf (a::l).

  Hint Constructors ForallOrdPairs_inf : core.

  Lemma ForallOrdPairs_inf_InT : forall l,
    ForallOrdPairs_inf l ->
    forall x y, InT x l -> InT y l -> ((x=y) + R x y + R y x)%type.
  Proof.
    induction 1 as [|? ? f].
    - inversion 1.
    - intros x y. simpl; destruct 1; destruct 1; subst; auto.
      + left. right.
        apply Forall_inf_forall with _ _ _ y in f; eauto.
      + right.
        apply Forall_inf_forall with _ _ _ x in f; eauto.
  Qed.

  (** [ForallPairs_inf] implies [ForallOrdPairs_inf].
    The reverse implication is true only when [R] is symmetric and reflexive. *)

  Lemma ForallPairs_inf_ForallOrdPairs_inf l:
    ForallPairs_inf l -> ForallOrdPairs_inf l.
  Proof.
    induction l as [|? ? IHl]; auto. intros H.
    constructor.
    - apply forall_Forall_inf. intros; apply H; simpl; auto.
    - apply IHl. red; intros; apply H; simpl; auto.
  Qed.

  Lemma ForallOrdPairs_inf_ForallPairs_inf :
    (forall x, R x x) ->
    (forall x y, R x y -> R y x) ->
    forall l, ForallOrdPairs_inf l -> ForallPairs_inf l.
  Proof.
    intros Refl Sym l Hl x y Hx Hy.
    destruct (ForallOrdPairs_inf_InT Hl _ _ Hx Hy); subst; intuition.
    subst; intuition.
  Qed.

End ForallPairs_inf.

Lemma ForallPairs_inf_ForallPairs {A} (R : A -> A -> Prop) l :
  ForallPairs_inf R l -> ForallPairs R l.
Proof.
intros HFP x y Hinx.
apply notF_inT_notF_in; intros Hiny.
revert Hinx; apply notF_inT_notF_in; intros Hinx.
now apply HFP.
Qed.

Lemma ForallPairs_ForallPairs_inf {A} (R : A -> A -> Prop) l :
  ForallPairs R l -> ForallPairs_inf R l.
Proof.
intros HFP x y Hinx Hiny.
apply HFP; now apply inT_in.
Qed.

Lemma ForallOrdPairs_inf_ForallOrdPairs {A} (R : A -> A -> Prop) l :
  ForallOrdPairs_inf R l -> ForallOrdPairs R l.
Proof.
  induction 1; constructor; intuition.
  now apply Forall_inf_Forall.
Qed.

Section Repeat.

  Variable A : Type.

  Theorem repeat_specT n (x y : A): InT y (repeat x n) -> y = x.
  Proof.
    induction n as [|k Hrec]; simpl; destruct 1; auto.
  Qed.

End Repeat.


(** Max of elements of a list of [nat]: [list_max] *)

Lemma list_max_le_inf : forall l n,
  list_max l <= n -> Forall_inf (fun k => k <= n) l.
Proof.
intro l. induction l as [|? ? IHl]; simpl; intros n; intros H; intuition.
apply Nat.max_lub_iff in H.
now constructor; [ | apply IHl ].
Qed.

Lemma list_max_lt_inf : forall l n, l <> nil ->
  list_max l < n -> Forall_inf (fun k => k < n) l.
Proof.
intro l. induction l as [|? l IHl]; simpl; intros n Hnil; intros H; intuition.
destruct l.
- repeat constructor.
  now simpl in H; rewrite Nat.max_0_r in H.
- apply Nat.max_lub_lt_iff in H.
  now constructor; [ | apply IHl ].
Qed.
