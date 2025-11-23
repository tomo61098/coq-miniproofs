Load sepsolve_sorted.
Open Scope R_scope.
Open Scope vec_scope.

Definition convex (f: R -> R):=
  forall (a: R) (x y: R),
    0 <= a <= 1 ->
      f (a * x + (1-a)*y)%R <= a * f x + (1-a) * f y
.

Definition secant_eq (f: R -> R) (x y: R) :=
  (f x - f y) / (x - y)
.

Lemma mult_neg_dist_neg_mult:
  forall (x y a b: R),
  ((x - y) * (a - b) = (y - x) * (b - a))%R
.
Proof.
  intros.
  rewrite !Rminus_def.
  lra.
Qed.

Lemma convex_secant_leq:
  forall (f: R -> R) (x y z: R),
    convex f -> x < y <= z ->
    secant_eq f x y <= secant_eq f x z
.
Proof.
  unfold convex, secant_eq.
  intros f x y z Convx [A2 B3].
  assert (A: (z-x)%R <> 0%R) by lra.
  assert (B2: 0 < (z-x)) by lra.
  assert (B:= Rinv_0_lt_compat _ B2).
  assert (C: 0 <= z - y) by lra.
  assert (D:= Rmult_le_pos _ (z - y)%R (Rlt_le _ _ B) C).
  clear C.
  assert (D2: 0 <= (z - y) / (z - x)) by lra.
  assert (E: z - y <= z - x) by lra.
  assert (F:= Rmult_le_compat_r _ _ _ (Rlt_le _ _ B) E).
  clear E.
  rewrite (Rmult_inv_r _ A) in F.
  rewrite <- Rdiv_def in F.
  specialize (Convx ((z - y)/(z-x)) x z (conj D2 F)).
  clear D D2 F.
  assert (G: ((z - x) - (z - y) = (y - x))%R) by lra.
  apply (f_equal (fun n => n * / (z - x)))%R in G.
  rewrite Rmult_minus_distr_r in G.
  rewrite (Rmult_inv_r _ A) in G.
  rewrite <- 2Rdiv_def in G.
  rewrite G in Convx. clear G.
  assert (C: ((z - y) * x + (y - x) * z = (z - x) * y)%R) by lra.
  apply (f_equal (fun n => n * / (z - x)))%R in C.
  rewrite Rmult_plus_distr_r in C.
  rewrite 3Rmult_assoc in C.
  rewrite 3(Rmult_comm _ (/(z-x))) in C.
  rewrite <- 3Rmult_assoc in C.
  rewrite (Rmult_inv_r _ A) in C.
  rewrite Rmult_1_l in C.
  rewrite <- 2Rdiv_def in C.
  rewrite C in Convx.
  clear C.
  apply (Rmult_le_compat_r _ _ _ (Rlt_le _ _ B2)) in Convx.
  rewrite Rmult_plus_distr_r in Convx.
  rewrite 2(Rmult_assoc _ _ (z - x)) in Convx.
  rewrite (Rmult_comm (f x) _), (Rmult_comm (f z) _) in Convx.
  rewrite <- 2Rmult_assoc in Convx.
  rewrite <- 2(Rmult_div_swap _ (z-x) _) in Convx.
  rewrite 2Rdiv_def in Convx.
  rewrite 2(Rmult_inv_r_id_l _ _ A) in Convx.
  rewrite Rmult_minus_distr_l in Convx.
  rewrite 2Rmult_minus_distr_r in Convx.
  apply (Rplus_le_compat_r (f x * x)) in Convx.
  rewrite !(Rmult_comm _ (f _)) in Convx.
  assert (Convx2 : f x * x - f y * x + (f y * z - f x * z)
    <= f x * x - f z * x + (f z * y - f x * y)) by lra.
  rewrite <- !Rmult_minus_distr_r in Convx2.
  rewrite <- 2(Ropp_minus_distr'_depr _ (f x)) in Convx2.
  rewrite 2Ropp_mult_distr_l_reverse in Convx2.
  rewrite <- !Rminus_def in Convx2.
  rewrite <- !Rmult_minus_distr_l in Convx2.
  assert (C: x - z < 0) by lra.
  apply Rinv_neg in C.
  apply (Rmult_le_compat_neg_l _ _ _ (Rlt_le _ _ C)) in Convx2.
  assert (D: (/ (x - z) * ((f x - f y) * (x - z)) = (f x - f y) * (x - z) * / (x - z))%R) by lra.
  rewrite D in Convx2.
  clear D.
  assert (A3: ((x - z) <> 0)%R) by lra.
  rewrite (Rmult_inv_r_id_l _ _ A3) in Convx2.
  clear A3 C.
  assert (D: (x - y) < 0) by lra.
  apply Rinv_neg in D.
  apply (Rmult_le_compat_neg_l _ _ _ (Rlt_le _ _ D)) in Convx2.
  clear D.
  assert (E: (/ (x - y) * (/ (x - z) * ((f x - f z) * (x - y))) =
  (/ (x - z) * ((f x - f z) * (x - y) * / (x - y))))%R) by lra.
  rewrite E in Convx2.
  clear E.
  assert (A3: ((x - y) <> 0)%R) by lra.
  rewrite (Rmult_inv_r_id_l _ _ A3) in Convx2.
  lra.
Qed.

(*
Theorem convex_secant:
  forall (f: R -> R) (x y z: R),
    convex f -> x <> y -> x <> z -> y <= z ->
    secant_eq f x y <= secant_eq f x z
.
Proof.
  unfold convex, secant_eq.
  intros f x y z Convx Y Z [B|B].
    - destruct (Rle_gt_dec x y) as [[C|C]|C].
      + apply (convex_secant_leq _ _ _ _ Convx). lra.
      + lra.
      + destruct (Rle_gt_dec x z) as [[D|D]|D].
        * assert (A: y < x <= z) by lra.
          assert (E:= convex_secant_leq _ _ _ _ Convx A).
          unfold secant_eq in E.
          assert (C2: (y - x) <= 0) by lra.
          apply (Rmult_le_compat_neg_l _ _ _ C2) in E.
          clear C2.
          rewrite 2Rmult_div_assoc in E.
          assert (C2: ((y - x) <> 0)%R) by lra.          
          rewrite (Rmult_div_r _ _ C2) in E.
          clear C2.
          assert (C2: (y - z) <= 0) by lra.
          apply (Rmult_le_compat_neg_l _ _ _ C2) in E.
          clear C2.
          assert (C2: ((y - z) * ((y - x) * (f y - f z) / (y - z)) = ((y - x) * ((f y - f z) * (y - z) *  / (y - z))))%R) by lra.
          rewrite C2 in E.
          clear C2.
          assert (C2: (y - z)%R<>0%R) by lra.
          rewrite (Rmult_inv_r_id_l _ _ C2) in E.
          clear C2.
        * lra.
        * assert
          assert (convex_secant_leq _ _ _ Convx
    - rewrite B. lra.
Qed.

Fixpoint n_majos {n : nat} (x y : vec n) : Prop.
destruct n.
  - apply True.
  - apply ((dot x onesV >= dot y onesV) /\
    n_majos n (tl x) (tl y)).
Defined.

Definition majorizes {n: nat} (x: vec n) (y: vec n) :=
  sorted_desc x /\ sorted_desc y /\ n_majos x y
  /\ (dot x onesV = dot y onesV)
.

Theorem Karamata_inequality :
  forall (f: R -> R) (n: nat) (x y: vec n),
    convex f ->
    majorizes x y ->
      dot (map f x) onesV >= dot (map f y) onesV
.
Proof.
  induction n; intros.
    - rewrite (eta0 (map _ x)).
      rewrite (eta0 (map _ _)).
      lra.
    - rewrite (eta x), (eta y), 2dot_step.
      simpl. rewrite !Rmult_1_r.
*)

Close Scope vec_scope.
Close Scope R_scope.