Load Cprops.

Open Scope R.
Open Scope vec_scope.

Structure NormV {n} := make_normV {
  norm_f :> vec n -> R ;
  triIneq: forall (x y: vec n), (norm_f (plusvecs x y) <= norm_f x + norm_f y)%R ;
  absHomo: forall(c: C), forall y: vec n, norm_f (c * y) = (Cnorm c * norm_f y)%R ;
  posDef: forall (x: vec n), norm_f x = 0%R -> x = 0
}.

Definition is_normV {n} (norm: vec n -> R) :=
  (forall x y: vec n, (norm (plusvecs x y) <= norm x + norm y)%R) /\
  (forall c: C, forall y: vec n, norm (c * y) = (Cnorm c * norm y)%R) /\
  forall x: vec n, norm x = 0%R -> x = 0.

Lemma seminormV0: forall {n: nat} (norm: vec n -> R),
  (forall c: C, forall y: vec n, norm (c * y) = (Cnorm c * norm y)%R) ->
  norm 0 = (0%R).
Proof.
  intros. assert (A:= H (0%R) 0).
  rewrite vec_mult_0 in A.
  rewrite Cnorm_0 in A. rewrite Rmult_0_l in A.
  auto.
Qed.

Lemma normV0: forall {n: nat} (norm: @NormV n),
  norm 0 = (0%R).
Proof. intros; apply (seminormV0 _ (absHomo _)). Qed.

Lemma seminormVNonneg: forall {n: nat}, forall norm: vec n -> R,
  (forall x y: vec n, (norm (plusvecs x y) <= norm x + norm y)%R) ->
  (forall c: C, forall y: vec n, norm (c * y) = (Cnorm c * norm y)%R) ->
  forall x: vec n, 0 <= norm x.
Proof.
  intros n norm A B x.
  specialize (A x (-x)).
  rewrite vec_plus_sub in A.
  rewrite vec_sub_sub in A.
  rewrite (seminormV0 _ B) in A.
  rewrite <- vec_mult_neg1 in A. Search (norm _).
  rewrite B in A.
  rewrite Cnorm_neg in A.
  replace (Cnorm 1%C) with 1%R in A.
  2:{ simpl. rewrite 2 Rmult_1_l. rewrite Rmult_0_l.
  rewrite Rplus_0_r. rewrite sqrt_1. exact (eq_refl 1%R). }
  rewrite Rmult_1_l in A.
  lra.
Qed.

Lemma normVNonneg: forall {n: nat}, forall norm: NormV,
  forall (x: vec n), 0 <= norm x.
Proof. intros; apply (seminormVNonneg _ (triIneq _) (absHomo _)). Qed.

Fixpoint normV2_L2 {n} (x: vec n): R :=
  match x with
    | [] => 0
    | x::xs => Cnorm2 x + normV2_L2 xs
  end
.

Definition normV_L2 {n} (x: vec n) := sqrt (normV2_L2 x).
Fixpoint normV_L1 {n} (x: vec n): R :=
  match x with
    | [] => 0
    | x::xs => Cnorm x + normV_L1 xs end.
Fixpoint normV_Linf {n} (x: vec n): R :=
  match x with
    | [] => 0
    | x::xs => Rmax (Cnorm x) (normV_Linf xs) end.
(*
Lemma norm_L1_is_norm: forall {n: nat}, is_normV (@normV_L1 n).
Proof.
  intros. split; try split; induction n.
    - intros. rewrite (eta0 x), (eta0 y).
      cbn. intuition.
    - intros. rewrite (eta x), (eta y).
      cbn. rewrite Rplus_assoc. rewrite (Rplus_comm (normV_L1 _)).
      rewrite <-2 Rplus_assoc. cbn.
      assert (A:=Rabs_triang).
      rewrite (Rplus_assoc (_ + _)).
      apply (Rplus_le_compat _ (Rabs _ + Rabs _)); auto.
      rewrite Rplus_comm.
      apply IHn.
    - intros. rewrite (eta0 _), (eta0 y). cbn. lra.
    - intros. rewrite (eta y).
      simpl. rewrite Rmult_plus_distr_l.
      f_equal. { apply Rabs_mult. }
      apply IHn.
    - intro. rewrite (eta0 x). intuition.
    - intros. rewrite (eta x) in H. rewrite (eta x).
      simpl in H. simpl.
      assert (A:= Rplus_eq_0_l (Rabs (hd x)) (normV_L1 (tl x))).
      assert (a0: 0 <= Rabs (hd x)). { apply Rabs_pos. }
      assert (a1: forall {n} z, 0 <= @normV_L1 n z). {
      induction z. * cbn. lra. * simpl. assert (e0:= Rabs_pos h).
      apply Rplus_le_le_0_compat; auto. }
      assert (B:= A a0 (a1 _ _) H).
      rewrite B in H. rewrite Rplus_0_l in H.
      assert (forall x: R, Rabs x = 0 -> x = 0)%R.
      { intros. destruct (Req_dec x0 0); auto. assert (c1:= Rabs_no_R0 _ H1). lra. }
      specialize (H0 _ B).
      f_equal; auto.
Qed.

Lemma normV_L1_Linf: forall {n},
  forall x: vec n, normV_Linf x <= normV_L1 x <= INR n * normV_Linf x.
Proof.
  induction x.
    - cbn. lra.
    - split.
      + simpl. destruct (Rle_dec (Rabs h) (normV_Linf x)).
        ++ rewrite (Rmax_right _ _ r).
           destruct IHx. rewrite <- (Rplus_0_l (normV_Linf _)). apply (Rplus_le_compat _ _ _ _ (Rabs_pos _)).
           lra.
        ++ rewrite (Rmax_left). { destruct (@norm_L1_is_norm n) as [A [B D]].
              replace (_ <= _) with (Rabs h + 0 <= Rabs h + normV_L1 x). apply (Rplus_le_compat).
              * lra. * apply seminormVNonneg; auto. * rewrite Rplus_0_r. trivial. }
              lra.
     + replace ((_ * _)%R) with ((normV_Linf (h :: x) + (INR n * normV_Linf (h :: x))%R)%R).
       { simpl. apply Rplus_le_compat. * apply Rmax_l. * intuition.
         assert (A:= Rmax_r (INR n * Rabs h) (INR n * normV_Linf x)).
         rewrite (RmaxRmult _ _ _ (pos_INR _)) in A. lra. }
      simpl. destruct n; intuition; simpl; lra.
Qed.
*)
Open Scope mat_scope.

Structure NormM {n} := make_normM {
  normM_f :> sqmatrix n -> R ;
  triIneqM: forall x y: sqmatrix n, (normM_f (plusmat x y) <= normM_f x + normM_f y)%R ;
  absHomoM: forall c: C, forall y: sqmatrix n, normM_f (c * y) = (Cnorm c * normM_f y)%R ;
  posDefM:  forall x: sqmatrix n, normM_f x = 0%R -> x = 0 ;
  subMult: forall (x y: sqmatrix n), normM_f (x @@ y) <= normM_f x * normM_f y
}.

Definition is_normM {n m} (norm: matrix n m -> R) :=
  (forall x y: matrix n m, (norm (plusmat x y) <= norm x + norm y)%R) /\
  (forall c: C, forall y: matrix n m, norm (c * y) = (Cnorm c * norm y)%R) /\
  forall x: matrix n m, norm x = 0%R -> x = 0.

Fixpoint mat_sum_sqr {n m} (M: matrix n m) : R :=
  match M with
    | [] => 0
    | v::Ms => normV2_L2 v + mat_sum_sqr Ms end.

Definition normM_Fro {n m} (M: matrix n m) :=  sqrt (mat_sum_sqr M).

Structure inducedNormM {n} (norm: NormV) := make_inducedNormM {
  indNormM_f :> NormM ;
  has_maxX: forall (A: sqmatrix n),
    { x | norm x = R1 /\
      indNormM_f A = norm (A @ x) /\
      forall y, norm y = R1 -> norm (A @ y) <= norm (A @ x) };
}.

Lemma indNormIis1: forall {n} (vnorm: @NormV n) (norm: inducedNormM vnorm),
  norm I = R1.
Proof.
  intros.
  destruct (has_maxX vnorm norm I) as [x [e [ex mx]]].
  rewrite ex.
  rewrite vec_mult_I.
  apply e.
Qed.
(*
Lemma indNormInv: forall {n} (vnorm: NormV) (norm: inducedNormM vnorm),
  forall (A B: sqmatrix n),
  B @@ A = I -> 1%R / (norm B) <= norm A.
Proof.
  intros.
  assert (C := indNormIis1 vnorm norm).
  rewrite <- H in C.
  Search normM_f.
  symmetry in C.
  assert(D := subMult norm B A).
  assert(F: 1 <= norm B * norm A) by lra.
  lra.
Qed.
*)


Axiom Fundamental_Theorem_of_Linear_Algebra:
  forall {n} (A: sqmatrix n),
    exists (lam: C) (v: vec n),
      (v <> 0)%Vec /\ A @ v = (lam * v)%Vec.

Lemma FTLA_norm: forall {n} (norm: NormV) (A: sqmatrix n),
  exists (lam: C) (v: vec n), norm v = 1%R /\ A @ v = (lam * v)%Vec.
Proof.
  intros. destruct (Fundamental_Theorem_of_Linear_Algebra A) as [lam [v [F G]]].
  exists lam, (1/norm v * v)%Vec.
  split.
    - rewrite absHomo.
      assert (N: 0 <= norm v).
      { apply seminormVNonneg. apply triIneq. apply absHomo. }
      destruct N.
      2:{ symmetry in H. apply posDef in H. contradiction. }
      assert (NN: 0 < / norm v).
      { apply Rinv_0_lt_compat. exact H. }
      assert (NNN: 0 < 1 / norm v) by lra.
      rewrite Cnorm_Rabs.
      rewrite (Rabs_pos_eq _ (or_introl NNN)).
      replace (1 / norm v) with (/ norm v) by lra.
      rewrite Rinv_l; lra.
    - rewrite mat_scalar_comm.
      rewrite vec_scalar_scalar.
      rewrite Cmult_comm.
      rewrite <- vec_scalar_scalar.
      rewrite mat_vec_scalar_dist.
      f_equal. exact G.
Qed.

Definition is_eigval {n} (lam: C) (A: sqmatrix n):=
  exists (v: vec n), A @ v = (lam * v)%Vec.
Definition is_eigvec {n} (v: vec n) (A: sqmatrix n) :=
  exists (lam: C), A @ v = (lam * v)%Vec.
Definition is_eigpair {n} (lam: C) (v: vec n) (A: sqmatrix n) :=
  A @ v = (lam * v)%Vec.

Close Scope mat_scope.
Close Scope vec_scope.
Close Scope R.


(*
Section GeneralizedNorms.
Open Scope R.
Open Scope vec_scope.

Structure NormV := make_normV {
  norm_f :> forall {n}, vec n -> R ;
  triIneq: forall {n} (x y: vec n), (norm_f (plusvecs x y) <= norm_f x + norm_f y)%R ;
  absHomo: forall {n} (c: R), forall y: vec n, norm_f (c * y) = (Rabs c * norm_f y)%R ;
  posDef: forall {n} (x: vec n), norm_f x = 0%R -> x = 0
}.

Definition is_normV {n} (norm: vec n -> R) :=
  (forall x y: vec n, (norm (plusvecs x y) <= norm x + norm y)%R) /\
  (forall c: R, forall y: vec n, norm (c * y) = (Rabs c * norm y)%R) /\
  forall x: vec n, norm x = 0%R -> x = 0.

Lemma seminormV0: forall {n: nat} (norm: vec n -> R),
  (forall c: R, forall y: vec n, norm (c * y) = (Rabs c * norm y)%R) ->
  norm 0 = (0%R).
Proof.
  intros. assert (A:= H (0%R) 0).
  rewrite vec_mult_0 in A.
  rewrite Rabs_R0 in A. rewrite Rmult_0_l in A.
  auto.
Qed.

Lemma normV0: forall {n: nat} (norm: NormV),
  norm n 0 = (0%R).
Proof. intros; apply (seminormV0 _ (absHomo _)). Qed.

Lemma seminormVNonneg: forall {n: nat}, forall norm: vec n -> R,
  (forall x y: vec n, (norm (plusvecs x y) <= norm x + norm y)%R) ->
  (forall c: R, forall y: vec n, norm (c * y) = (Rabs c * norm y)%R) ->
  forall x: vec n, 0 <= norm x.
Proof.
  intros n norm A B x.
  specialize (A x (-x)).
  rewrite vec_plus_sub in A.
  rewrite vec_sub_sub in A.
  rewrite (seminormV0 _ B) in A.
  rewrite <- vec_mult_neg1 in A.
  rewrite B in A.
  assert  (c0:=pow_1_abs 1).
  cbn in c0. rewrite Rmult_1_r in c0.
  rewrite c0 in A. rewrite Rmult_1_l in A.
  lra.
Qed.

Lemma normVNonneg: forall {n: nat}, forall norm: NormV,
  forall (x: vec n), 0 <= norm n x.
Proof. intros; apply (seminormVNonneg _ (triIneq _) (absHomo _)). Qed.

Definition normV_L2 {n} (x: vec n) := sqrt (dot x x).
Fixpoint normV_L1 {n} (x: vec n): R :=
  match x with
    | [] => 0
    | x::xs => Rabs x + normV_L1 xs end.
Fixpoint normV_Linf {n} (x: vec n): R :=
  match x with
    | [] => 0
    | x::xs => Rmax (Rabs x) (normV_Linf xs) end.

Lemma norm_L1_is_norm: forall {n: nat}, is_normV (@normV_L1 n).
Proof.
  intros. split; try split; induction n.
    - intros. rewrite (eta0 x), (eta0 y).
      cbn. intuition.
    - intros. rewrite (eta x), (eta y).
      cbn. rewrite Rplus_assoc. rewrite (Rplus_comm (normV_L1 _)).
      rewrite <-2 Rplus_assoc. cbn.
      assert (A:=Rabs_triang).
      rewrite (Rplus_assoc (_ + _)).
      apply (Rplus_le_compat _ (Rabs _ + Rabs _)); auto.
      rewrite Rplus_comm.
      apply IHn.
    - intros. rewrite (eta0 _), (eta0 y). cbn. lra.
    - intros. rewrite (eta y).
      simpl. rewrite Rmult_plus_distr_l.
      f_equal. { apply Rabs_mult. }
      apply IHn.
    - intro. rewrite (eta0 x). intuition.
    - intros. rewrite (eta x) in H. rewrite (eta x).
      simpl in H. simpl.
      assert (A:= Rplus_eq_0_l (Rabs (hd x)) (normV_L1 (tl x))).
      assert (a0: 0 <= Rabs (hd x)). { apply Rabs_pos. }
      assert (a1: forall {n} z, 0 <= @normV_L1 n z). {
      induction z. * cbn. lra. * simpl. assert (e0:= Rabs_pos h).
      apply Rplus_le_le_0_compat; auto. }
      assert (B:= A a0 (a1 _ _) H).
      rewrite B in H. rewrite Rplus_0_l in H.
      assert (forall x: R, Rabs x = 0 -> x = 0)%R.
      { intros. destruct (Req_dec x0 0); auto. assert (c1:= Rabs_no_R0 _ H1). lra. }
      specialize (H0 _ B).
      f_equal; auto.
Qed.

Lemma normV_L1_Linf: forall {n},
  forall x: vec n, normV_Linf x <= normV_L1 x <= INR n * normV_Linf x.
Proof.
  induction x.
    - cbn. lra.
    - split.
      + simpl. destruct (Rle_dec (Rabs h) (normV_Linf x)).
        ++ rewrite (Rmax_right _ _ r).
           destruct IHx. rewrite <- (Rplus_0_l (normV_Linf _)). apply (Rplus_le_compat _ _ _ _ (Rabs_pos _)).
           lra.
        ++ rewrite (Rmax_left). { destruct (@norm_L1_is_norm n) as [A [B D]].
              replace (_ <= _) with (Rabs h + 0 <= Rabs h + normV_L1 x). apply (Rplus_le_compat).
              * lra. * apply seminormVNonneg; auto. * rewrite Rplus_0_r. trivial. }
              lra.
     + replace ((_ * _)%R) with ((normV_Linf (h :: x) + (INR n * normV_Linf (h :: x))%R)%R).
       { simpl. apply Rplus_le_compat. * apply Rmax_l. * intuition.
         assert (A:= Rmax_r (INR n * Rabs h) (INR n * normV_Linf x)).
         rewrite (RmaxRmult _ _ _ (pos_INR _)) in A. lra. }
      simpl. destruct n; intuition; simpl; lra.
Qed.

Open Scope mat_scope.

Structure NormM := make_normM {
  normM_f :> forall {n m}, matrix n m -> R ;
  triIneqM: forall {n m}, forall x y: matrix n m, (normM_f (plusmat x y) <= normM_f x + normM_f y)%R ;
  absHomoM: forall {n m}, forall c: R, forall y: matrix n m, normM_f (c * y) = (Rabs c * normM_f y)%R ;
  posDefM: forall {n m}, forall x: matrix n m, normM_f x = 0%R -> x = 0 ;
  subMult: forall {n m r}, forall (x: matrix n r) (y: matrix r m), normM_f (x @@ y) <= normM_f x * normM_f y
}.

Definition is_normM {n m} (norm: matrix n m -> R) :=
  (forall x y: matrix n m, (norm (plusmat x y) <= norm x + norm y)%R) /\
  (forall c: R, forall y: matrix n m, norm (c * y) = (Rabs c * norm y)%R) /\
  forall x: matrix n m, norm x = 0%R -> x = 0.

Fixpoint mat_sum_sqr {n m} (M: matrix n m) : R :=
  match M with
    | [] => 0
    | v::Ms => dot v v + mat_sum_sqr Ms end.

Definition normM_Fro {n m} (M: matrix n m) :=  sqrt (mat_sum_sqr M).

Structure inducedNormM (norm: NormV) := make_inducedNormM {
  indNormM_f :> NormM ;
  has_maxX: forall {n m} (A: matrix n m),
    exists x, norm m x = R1 /\
      indNormM_f n m A = norm n (A @ x) /\
      forall y, norm m y = R1 -> norm n (A @ y) <= norm n (A @ x) ;
}.

Lemma indNormIis1: forall {n} (vnorm: NormV) (norm: inducedNormM vnorm),
  norm n n I = R1.
Proof.
  intros.
  destruct (@has_maxX vnorm norm n n I) as [x [e [ex mx]]].
  rewrite ex.
  rewrite vec_mult_I.
  apply e.
Qed.

Lemma indNormInv: forall {n m} (vnorm: NormV) (norm: inducedNormM vnorm),
  forall (A: matrix n m) (B: matrix m n),
  B @@ A = I -> R1 / (norm _ _ B) <= norm _ _ A.
Proof.
  intros.
  assert (C := @indNormIis1 m vnorm norm).
  rewrite <- H in C.
  Search normM_f.
  symmetry in C.
  assert(D := @subMult norm m m n B A).
  assert(F: 1 <= norm m n B * norm n m A) by lra.
Qed.

Close Scope mat_scope.
Close Scope vec_scope.
Close Scope R.
End GeneralizedNorms.
*)