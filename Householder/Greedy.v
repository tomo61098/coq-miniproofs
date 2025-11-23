From Coq Require Import List Arith Bool Lia.
Import ListNotations.

(* --- 1) Sorted sequence (non-increasing: head >= next >= ... ) --- *)
Inductive sorted_desc : list nat -> Prop :=
| sd_nil  : sorted_desc []
| sd_one  : forall x, sorted_desc [x]
| sd_cons : forall x y l,
    x >= y ->
    sorted_desc (y :: l) ->
    sorted_desc (x :: y :: l)
.

Ltac demake H := inversion H; subst; clear H.

Lemma sorted_desc_desc:
  forall (x: nat) (l: list nat),
  sorted_desc (x::l) -> sorted_desc l
.
Proof.
  intros. demake H; auto using sd_nil.
Qed.

Lemma sorted_desc_skip:
  forall x y l,
    x >= y -> sorted_desc (y::l) ->
    sorted_desc (x::l)
.
Proof.
  intros x y l. revert x y.
  induction l.
    -- constructor.
    -- intros.
       demake H0.
       apply sd_cons.
        + apply (Nat.le_trans _ _ _ H3 H). 
        + apply H5.
Qed.

Inductive ge_list_desc : nat -> list nat -> Prop :=
  | gl_nil : forall a, ge_list_desc a []
  | gl_cons : forall a x l,
      a >= x ->
      ge_list_desc a l ->
      ge_list_desc a (x::l)
.

Lemma ge_list_sorted :
  forall x l,
    sorted_desc (x::l) -> ge_list_desc x l
.
Proof.
  intros x l. revert x.
  induction l.
    -- constructor.
    -- intros. apply gl_cons; demake H.
       + trivial.
       + assert (A:= sorted_desc_skip _ _ _ H2 H4).
         apply (IHl _ A).
Qed.

Lemma ge_sorted_list :
  forall x l,
    sorted_desc l -> ge_list_desc x l ->
    sorted_desc (x::l)
.
Proof.
  intros x l. revert x.
  induction l.
    - constructor.
    - intros.
      demake H0.
      constructor; auto.
Qed.

(* --- 2) Sorting a list in *reversed* (i.e., non-increasing) order --- *)
Fixpoint insert_desc (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | y :: ys =>
      (* place x before the first y with y <= x to keep non-increasing order *)
      if y <=? x then x :: y :: ys
      else y :: insert_desc x ys
  end.


Lemma L1:
  forall x a l, a >= x ->
    ge_list_desc a l -> ge_list_desc a (insert_desc x l)
.
Proof.
  intros x a l. revert x a.
  induction l.
    - constructor; auto.
    - intros.
      simpl.
      destruct (lt_dec x a).
      -- assert (A:=leb_correct_conv _ _ l0).
         rewrite A.
         constructor; demake H0.
          + lia.
          + apply IHl; auto.
      -- assert (B: x >= a) by lia.
         assert (C:= leb_correct _ _ B).
         rewrite C. constructor; auto.
Qed.

Theorem sorted_insert_sorted :
  forall (x : nat) (l : list nat),
 (sorted_desc l) -> sorted_desc (insert_desc x l).
Proof.
  intros x l. revert x.
  induction l; intros.
    - apply sd_one.
    - simpl.
      destruct (lt_dec x a).
      -- assert (D:=leb_correct_conv _ _ l0).
         rewrite D.
         assert (E:= sorted_desc_desc _ _ H).
         assert (A:= IHl x E).
         apply ge_sorted_list; auto.
         apply L1. + lia. + auto using ge_list_sorted.
      -- assert (B: x >= a) by lia.
         assert (C:= leb_correct _ _ B).
         rewrite C.
         constructor; auto.
Qed.

Fixpoint sort_desc (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => insert_desc x (sort_desc xs)
  end.

Theorem sort_desc_sorted:
  forall l, sorted_desc (sort_desc l)
.
Proof.
  induction l.
  - constructor. - simpl. auto using sorted_insert_sorted.
Qed.

(* --- 3) Sum of elements in a list --- *)
Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

Fixpoint subsequence {X: Type} (a : list X) (b: list bool) : list X :=
  match a, b with
    | x::xs, y::ys => if y then x::(subsequence xs ys) else subsequence xs ys
    | _,_ => []
  end
.

Definition is_subsequence {X: Type} (a: list X) (b: list X):=
  exists c, subsequence a c = b
.