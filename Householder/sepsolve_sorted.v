Load sepsolve_vec.
Open Scope R_scope.
Open Scope vec_scope.

Ltac demake H := inversion H; subst; clear H.

(* --- 1) Sorted sequence (non-increasing: head >= next >= ... ) --- *)
Inductive sorted_desc : forall {n}, vec n -> Prop :=
| sd_nil  : sorted_desc []
| sd_one  : forall x, sorted_desc [x]
| sd_cons : forall n (x y: R) (l: vec n),
    x >= y ->
    sorted_desc (y :: l) ->
    sorted_desc (x :: y :: l)
.

Theorem three_sorted :
  forall n x y (l: vec n),
    sorted_desc (x::y::l) ->
      x >= y /\ sorted_desc (y :: l)
.
Proof.
  intros. demake H.
  apply (inj_pair2_eq_dec _ (Nat.eq_dec)) in H4.
  subst. auto.
Qed.

Ltac unmake_desc H := destruct (three_sorted _ _ _ _ H).


Lemma sorted_desc_desc:
  forall (n: nat) (x: R) (l: vec n),
  sorted_desc (x::l) -> sorted_desc l
.
Proof.
  intros. demake H; auto using sd_nil.
Qed.

Lemma sorted_desc_skip:
  forall (n: nat) (x y: R) (l: vec n),
    x >= y -> sorted_desc (y::l) ->
    sorted_desc (x::l)
.
Proof.
  intros n x y l. revert x y.
  induction l.
    -- constructor.
    -- intros.
       unmake_desc H0.
       apply sd_cons.
        + lra.
        + apply H2.
Qed.

Inductive ge_list_desc : forall {n}, R -> vec n -> Prop :=
  | gl_nil : forall (a: R), ge_list_desc a []
  | gl_cons : forall n a x (l: vec n),
      a >= x ->
      ge_list_desc a l ->
      ge_list_desc a (x::l)
.

Lemma ge_list_sorted :
  forall n x (l: vec n),
    sorted_desc (x::l) -> ge_list_desc x l
.
Proof.
  intros n x l. revert x.
  induction l.
    -- constructor.
    -- intros. unmake_desc H. apply gl_cons.
       + trivial.
       + assert (A:= sorted_desc_skip _ _ _ _ H0 H1).
         apply (IHl _ A).
Qed.

Lemma ge_sorted_list :
  forall n x (l: vec n),
    sorted_desc l -> ge_list_desc x l ->
    sorted_desc (x::l)
.
Proof.
  intros n x l. revert x.
  induction l.
    - constructor.
    - intros.
      demake H0.
      constructor; auto.
Qed.

(* --- 2) Sorting a list in *reversed* (i.e., non-increasing) order --- *)
Fixpoint insert_desc {n: nat} (x : R) (l : vec n) : vec (S n) :=
  match l with
  | [] => [x]
  | y :: ys =>
      (* place x before the first y with y <= x to keep non-increasing order *)
      match Rle_gt_dec y x with
        | left _ => x :: y :: ys
        | right _ => y :: insert_desc x ys
      end
  end.


Lemma L1:
  forall n x a (l: vec n), a >= x ->
    ge_list_desc a l -> ge_list_desc a (insert_desc x l)
.
Proof.
  intros n x a l. revert x a.
  induction l.
    - constructor; auto.
    - intros.
      simpl.
      destruct (Rle_gt_dec h x).
      -- constructor; auto.
      -- demake H0. apply (inj_pair2_eq_dec _ (Nat.eq_dec)) in H3.
         subst. constructor; auto.
Qed.

Theorem sorted_insert_sorted :
  forall (n: nat) (x : R) (l : vec n),
 (sorted_desc l) -> sorted_desc (insert_desc x l).
Proof.
  intros n x l. revert x.
  induction l; intros.
    - apply sd_one.
    - simpl.
      destruct (Rle_gt_dec h x).
      -- constructor; auto.
         lra.
      -- apply ge_sorted_list; auto.
         + apply IHl.
           demake H.
           ++ constructor.
           ++ auto.
         + apply L1.
           ++ lra.
           ++ auto using ge_list_sorted.
Qed.

Fixpoint sort_desc {n: nat} (l : vec n) : vec n :=
  match l with
  | [] => []
  | x :: xs => insert_desc x (sort_desc xs)
  end.

Theorem sort_desc_sorted:
  forall (n: nat) (l: vec n), sorted_desc (sort_desc l)
.
Proof.
  induction l.
  - constructor. - simpl. auto using sorted_insert_sorted.
Qed.


Inductive sorted : forall {n}, vec n -> Prop :=
  | s_nil : sorted []
  | s_one : forall x, sorted [x]
  | s_cons : forall n (x y: R) (l: vec n),
    x <= y ->
    sorted (y :: l) ->
    sorted (x :: y :: l)
.

Theorem three_sorted2 :
  forall n x y (l: vec n),
    sorted (x::y::l) ->
      x <= y /\ sorted (y :: l)
.
Proof.
  intros. demake H.
  apply (inj_pair2_eq_dec _ (Nat.eq_dec)) in H4.
  subst. auto.
Qed.

Ltac unmake_sorted H := destruct (three_sorted2 _ _ _ _ H).


Lemma sorted_asc_asc:
  forall (n: nat) (x: R) (l: vec n),
  sorted (x::l) -> sorted l
.
Proof.
  intros. demake H; auto using s_nil.
Qed.

Lemma sorted_asc_skip:
  forall (n: nat) (x y: R) (l: vec n),
    x <= y -> sorted (y::l) ->
    sorted (x::l)
.
Proof.
  intros n x y l. revert x y.
  induction l.
    -- constructor.
    -- intros.
       unmake_sorted H0.
       apply s_cons.
        + lra.
        + apply H2.
Qed.

Inductive le_list_asc : forall {n}, R -> vec n -> Prop :=
  | ll_nil : forall (a: R), le_list_asc a []
  | ll_cons : forall n a x (l: vec n),
      a <= x ->
      le_list_asc a l ->
      le_list_asc a (x::l)
.

Lemma le_list_sorted :
  forall n x (l: vec n),
    sorted (x::l) -> le_list_asc x l
.
Proof.
  intros n x l. revert x.
  induction l.
    -- constructor.
    -- intros. unmake_sorted H. apply ll_cons.
       + trivial.
       + assert (A:= sorted_asc_skip _ _ _ _ H0 H1).
         apply (IHl _ A).
Qed.

Lemma le_sorted_list :
  forall n x (l: vec n),
    sorted l -> le_list_asc x l ->
    sorted (x::l)
.
Proof.
  intros n x l. revert x.
  induction l.
    - constructor.
    - intros.
      demake H0.
      constructor; auto.
Qed.

(* --- 2) Sorting a list in *reversed* (i.e., non-increasing) order --- *)
Fixpoint insert_asc {n: nat} (x : R) (l : vec n) : vec (S n) :=
  match l with
  | [] => [x]
  | y :: ys =>
      (* place x before the first y with y <= x to keep non-increasing order *)
      match Rle_gt_dec x y with
        | left _ => x :: y :: ys
        | right _ => y :: insert_asc x ys
      end
  end.


Lemma L2:
  forall n x a (l: vec n), a <= x ->
    le_list_asc a l -> le_list_asc a (insert_asc x l)
.
Proof.
  intros n x a l. revert x a.
  induction l.
    - constructor; auto.
    - intros.
      simpl.
      destruct (Rle_gt_dec x h).
      -- constructor; auto.
      -- demake H0. apply (inj_pair2_eq_dec _ (Nat.eq_dec)) in H3.
         subst. constructor; auto.
Qed.

Theorem sorted_insert_sorted2 :
  forall (n: nat) (x : R) (l : vec n),
 (sorted l) -> sorted (insert_asc x l).
Proof.
  intros n x l. revert x.
  induction l; intros.
    - apply s_one.
    - simpl.
      destruct (Rle_gt_dec x h).
      -- constructor; auto.
      -- apply le_sorted_list; auto.
         + apply IHl.
           demake H.
           ++ constructor.
           ++ auto.
         + apply L2.
           ++ lra.
           ++ auto using le_list_sorted.
Qed.

Fixpoint sort {n: nat} (l : vec n) : vec n :=
  match l with
  | [] => []
  | x :: xs => insert_asc x (sort xs)
  end.

Theorem sort_asc_sorted:
  forall (n: nat) (l: vec n), sorted (sort l)
.
Proof.
  induction l.
  - constructor. - simpl. auto using sorted_insert_sorted2.
Qed.

Close Scope vec_scope.
Close Scope R_scope.