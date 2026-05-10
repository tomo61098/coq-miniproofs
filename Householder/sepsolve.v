Require Import Psatz.
Load Karamata.
Load sepsolve_vec.
Open Scope R_scope.
Open Scope vec_scope.

Definition gaussian {n: nat} := (vec n * vec n)%type.

Fixpoint is_ca_separated {n m: nat} (c: R) (a: vec n)
  (g: @gaussian n) (l: Vector.t (@gaussian n) m): Prop.
destruct l.
  - apply True.
  - inversion g as [mu sigm].
    destruct h as [mu2 sigm2].
    apply (
      c * dot a sigm  <= dot a (sqvec (mu - mu2)) /\
      c * dot a sigm2 <= dot a (sqvec (mu - mu2)) /\
      is_ca_separated n n0 c a g l
    ).
Defined.

Fixpoint c_separates {n m: nat} (c: R) (a: vec n)
  (l: Vector.t (@gaussian n) m) : Prop.
destruct l.
  - apply True.
  - apply (
      is_ca_separated c a h l /\
      c_separates n n0 c a l
    ).
Defined.

Goal forall (n m: nat) (c: R) (l: Vector.t (@gaussian n) m),
  c_separates c 0 l.
Proof.
  induction l.
    - reflexivity.
    - simpl. constructor; auto.
      cut (forall n m c (g: @gaussian n) (l: Vector.t _ m), @is_ca_separated n _ c 0 g l); auto.
      intros. induction l0.
      + reflexivity.
      + simpl. destruct g, h0. constructor; auto.
        ++ rewrite 2dot_0. lra.
        ++ constructor; auto. rewrite 2dot_0. lra.
Qed.

(* Equal-cardinality partition: binary selector, exactly m entries,
   and selected sum is half of total sum. *)
Definition is_ec_partition {d : nat} (a s : vec d) : Prop :=
  is_binary a /\
  dot a 1 = INR d / 2 /\
  dot a s = dot s 1 / 2
.

Definition has_ec_partition {d : nat} (s : vec d) : Prop :=
  exists a, is_ec_partition a s.


(* The three Gaussians from the reduction. *)
Definition red_g1 {d : nat} : @gaussian d :=
  (0, 1).

Definition red_g2 {d : nat} (s : vec d) : @gaussian d :=
  (INR d / 2 * sqrtvec s, INR d / 2 * 1).

Definition red_g3 {d : nat} (s : vec d) : @gaussian d :=
  (- (dot s 1 / 2 * 1), INR d / 2 * s).

Definition red_instance {d : nat} (s: vec d)
  : Vector.t (@gaussian d) 3 :=
  [red_g1; red_g2 s; red_g3 s].

Definition c_separated_valid {n k: nat}
  (c: R) (m: nat) (a: vec n) (l: Vector.t gaussian k) :=
  is_binary a /\
  dot a 1 = (INR m) /\
  c_separates c a l
.

Lemma red_12:
  forall {n: nat} (d: nat) (a s: vec n),
  dot a (sqvec (0 - INR (2 * d) / 2 * sqrtvec s))
  = (INR d * INR d * dot a (sqvec (sqrtvec s)))%R
.
Proof.
  intros n d a s.
  rewrite vec_0_neg.
  rewrite sqvec_neg.
  replace (INR (2 * d) / 2) with (INR d).
  - rewrite sqvec_dist.
    apply dot_mult_dist_r.
  - rewrite mult_INR.
    simpl. lra.
Qed.

Lemma red_13:
  forall {n: nat} (a s: vec n),
  dot a (sqvec (0 - - (dot s 1 / 2 * 1))) = (dot s 1%Vec / 2 * (dot s 1%Vec / 2) * dot a 1%Vec)%R
.
Proof.
  intros n a s.
  rewrite vec_0_neg.
  rewrite 2 sqvec_neg.
  rewrite sqvec_dist.
  rewrite dot_mult_dist_r.
  rewrite sqvec_1.
  reflexivity.
Qed.

Theorem red_instance_correct_left :
  forall {d : nat} (a s : vec (2 * d)),
    perf_square_vec s ->
    c_separated_valid
      (dot s 1 / 2) d a (red_instance s)
    ->
    is_ec_partition a s
.
Proof.
  intros d a s Hsqrt Hvalid.
  unfold c_separated_valid in Hvalid.
  destruct Hvalid as [Ha [Hcard Hsep]].

  unfold red_instance, red_g1, red_g2, red_g3 in Hsep.
  simpl in Hsep.

  destruct Hsep as [Hfrom1 _].
  simpl in Hfrom1.

  (* From pair (1,2), using the second variance inequality. *)
  destruct Hfrom1 as [_ [H12 [_ [H13 _]]]].
  replace (INR (d + (d + 0))%nat) with (INR (2 * d)%nat) in H12, H13 by (f_equal; lia).
  rewrite red_12 in H12.
  rewrite red_13 in H13.
  replace (INR (2 * d) / 2) with (INR d) in H12, H13.
  2:{ rewrite mult_INR. simpl. lra. }
  rewrite dot_mult_dist_r in H12, H13.
  destruct (Nat.eq_dec d 0).
  { subst. simpl in a, s. rewrite (nil_spec a), (nil_spec s). split; [constructor|]. split; simpl; lra. }
  assert (Nd : 0 < INR d).
  { rewrite <- INR_0. apply lt_INR. lia. }

  assert (Hlower : dot s 1 / 2 <= dot a s).
  {
    rewrite sq_sqrt_vec in H12 by (auto using perf_square_non_neg).
    apply (Rmult_le_reg_l (INR d) _ _ Nd).
    rewrite <- Hcard at 1.
    rewrite (Rmult_comm (dot a 1)).
    apply (Rmult_le_reg_l (INR d) _ _ Nd).
    rewrite <- 2 Rmult_assoc.
    rewrite (Rmult_comm _ (dot _ _ / 2)).
    rewrite (Rmult_assoc (dot _ _ / 2)). apply H12.
  }

  assert (Hupper : dot a s <= dot s 1 / 2).
  {
    destruct (Req_dec (dot s 1) 0).
    + apply (non_neg_dot_0 _ (perf_square_non_neg _ Hsqrt)) in H.
      subst. rewrite (dot_comm _ 0).
      rewrite 2 dot_0. lra.
    + assert (B:= non_neg_dot_1 _ (perf_square_non_neg _ Hsqrt)).
      assert (B2: 0 < dot s 1 / 2) by lra.
      apply (Rmult_le_reg_l (INR d) _ _ Nd).
      rewrite <- Hcard at 2.
      rewrite (Rmult_comm (dot a 1)).
      apply (Rmult_le_reg_l (dot s 1 / 2) _ _ B2).
      rewrite <- (Rmult_assoc _ _ (dot a 1)). apply H13.
  }

  unfold is_ec_partition.
  constructor; auto.
  constructor.
  + rewrite mult_INR. simpl INR. lra.
  + lra.
Qed.

Lemma red_23 :
  forall {m} (a b c: vec m),
    is_binary a ->
    is_vec_leq 0 b ->
    is_vec_leq 0 c ->
      dot a (sqvec b) <= dot a (sqvec (b + c))
.    
Proof.
  induction m; intros a b c Ha Hb Hc.
  - rewrite (eta0 a), (eta0 b), (eta0 c).
    simpl. lra.
  - rewrite (eta a), (eta b), (eta c) in *.
    inversion Ha as [| ? ? ? Ha_hd Ha_tl]; subst; clear Ha.
    inversion Hb as [| ? ? ? ? ? Hb_hd Hb_tl]; subst; clear Hb.
    inversion Hc as [| ? ? ? ? ? Hc_hd Hc_tl]; subst; clear Hc.
    repeat match goal with
    | H : existT _ _ _ = existT _ _ _ |- _ =>
        apply (inj_pair2_eq_dec _ Nat.eq_dec) in H; subst; clear H
    end.
    rewrite !dot_step.
    simpl.
    specialize (IHm _ _ _ Ha_tl Hb_tl Hc_tl).
    destruct Ha_hd as [Ha | Ha]; subst; rewrite Ha; unfold sqvec in IHm.
    + rewrite 2 Rmult_0_l. rewrite 2 Rplus_0_l. apply IHm.
    + rewrite 2 Rmult_1_l. apply Rplus_le_compat; auto.
      nra.
Qed.

Theorem red_instance_correct_right :
  forall {d : nat} (a s : vec (2 * d)),
    perf_square_vec s ->
    is_ec_partition a s ->
    c_separated_valid (dot s 1 / 2) d a (red_instance s)
.
Proof.
  intros d a s P [B [D Sm]].
  split; auto.
  rewrite mult_INR in D. simpl in D.
  replace ((1+1) * INR d / 2) with (INR d) in D by lra.
  split.
    - apply D.
    - split.
    -- split.
    { rewrite red_12.
      rewrite (sq_sqrt_vec _ _ (perf_square_non_neg _ P)).
      rewrite Sm. rewrite Rmult_comm. apply Rmult_le_compat_r.
      - apply Rle_mult_inv_pos; [|lra].
        apply non_neg_dot_1.
        apply perf_square_non_neg; auto.
      - replace (dot a 1) with (INR d).
        rewrite <- mult_INR. apply le_INR.
        destruct (Nat.eq_dec d 0).
        { subst. lia. }
        apply Nat.le_mul_r. lia.
    }
    split.
    { rewrite red_12.
      rewrite (sq_sqrt_vec _ _ (perf_square_non_neg _ P)).
      replace (INR (2 * d) / 2) with (INR d).
      2:{ rewrite mult_INR. simpl. lra. }
      rewrite dot_mult_dist_r.
      rewrite Sm.
      replace (dot a 1) with (INR d). lra.
    }
    split.
    { rewrite red_13.
      replace (dot a 1) with (INR d).
      apply (Rmult_le_compat_r _ _ _ (pos_INR _)).
      assert (F: forall m (u v: vec m), is_binary u -> perf_square_vec v -> exists q, dot u v = INR q).
      { induction m; intros u v Bi Pe.
        + exists O. rewrite (nil_spec u). trivial.
        + rewrite (eta u) in Bi. rewrite (eta v) in Pe.
          inv (Bi, Pe). 
          destruct (IHm _ _ H3 H1).
          destruct H2.
          ++ exists (x0)%nat.
             rewrite dot_step.
             rewrite H, H2, <- H0. lra.
          ++ exists (x*x + x0)%nat.
             rewrite dot_step.
             rewrite H, H2, <- H0.
              rewrite <- mult_INR. rewrite plus_INR. lra.
      }
      destruct (F _ _ _ B P).
      destruct x.
      + simpl in H. replace (dot a s) with 0%R in Sm.
        rewrite <- Sm. lra.
      + assert (Sn: 1 <= dot s 1 / 2).
        { replace (dot a s) with (1 + INR x)%R in Sm.
          2:{ rewrite S_INR in H. lra. }
          assert (G:= pos_INR x). lra.
        } rewrite <- Rmult_1_l at 1. apply Rmult_le_compat_r; lra.
    }
    split; [|exact I].
    rewrite red_13.
    replace (INR (2*d) / 2) with (INR d).
    2:{ rewrite mult_INR. simpl. lra. }
    rewrite dot_mult_dist_r.
    rewrite <- D.
    rewrite Sm.
    rewrite (Rmult_comm (dot a 1)).
    lra.
    --
    split; [|auto].
    split.
    {
      replace (INR (2 * d) / 2) with (INR d).
      2:{ rewrite mult_INR. simpl. lra. }
      rewrite vec_sub_neg.
      eapply Rle_trans.
      2:{
        apply red_23; auto.
        - apply vec_sqrt_nonneg.
          + apply pos_INR.
          + apply perf_square_non_neg. exact P.
        - apply vec_nonneg_mult_1.
          apply Rle_mult_inv_pos; [|lra].
          apply non_neg_dot_1.
          apply perf_square_non_neg. exact P.
      }
      rewrite sqvec_dist.
      rewrite !dot_mult_dist_r.
      rewrite (sq_sqrt_vec _ _ (perf_square_non_neg _ P)).
      rewrite Sm.
      replace (dot a 1) with (INR d).
      lra.
    }
    {
      replace (INR (2 * d) / 2) with (INR d).
      2:{ rewrite mult_INR. simpl. lra. }
      rewrite vec_sub_neg.
      rewrite dot_mult_dist_r.
      rewrite Sm. simpl.
      split; [|trivial].
      eapply Rle_trans.
      2:{
        rewrite vec_plus_comm.
        apply red_23; auto.
        - apply vec_nonneg_mult_1.
          apply Rle_mult_inv_pos; [|lra].
          apply non_neg_dot_1.
          apply perf_square_non_neg. exact P.
        - apply vec_sqrt_nonneg.
          + apply pos_INR.
          + apply perf_square_non_neg. exact P.
      }
      rewrite sqvec_dist.
      rewrite dot_mult_dist_r.
      rewrite sqvec_1.
      rewrite D.
      lra.
    }
    split; exact I.
Qed.


Definition hinge (c D S : R) : R :=
  Rmax 0%R (c - D / S)
.

Fixpoint sumR (xs : list R) : R :=
  match xs with
  | List.nil => 0
  | List.cons x xs => x + sumR xs
  end.

Definition gaussian_pair_stats {d : nat}
  (a : vec d) (p : @gaussian d * @gaussian d) : R * R :=
  let (g1, g2) := p in
  let (mu1, sig1) := g1 in
  let (mu2, sig2) := g2 in
    (dot a (sqvec (mu1 - mu2)),
     Rmax (dot a sig1) (dot a sig2)).

Definition gaussian_pair_hinge {d : nat}
  (c : R) (a : vec d) (g1 g2 : @gaussian d) : R :=
  let (D, S) := gaussian_pair_stats a (g1, g2) in
    hinge c D S.

Fixpoint hinge_against {d : nat}
  (c : R) (a : vec d) (g : @gaussian d) (L : list (@gaussian d)) : R :=
  match L with
  | List.nil => 0
  | List.cons h L' => gaussian_pair_hinge c a g h + hinge_against c a g L'
  end.

Fixpoint hinge_form {d : nat}
  (c : R) (a : vec d) (L : list (@gaussian d)) : R :=
  match L with
  | List.nil => 0
  | List.cons g L' => hinge_against c a g L' + hinge_form c a L'
  end.

Lemma gaussian_pair_stats_ordered :
  forall {d : nat} (a mu1 sig1 mu2 sig2 : vec d),
    is_vec_leq 0 a ->
    is_vec_leq sig1 sig2 ->
    gaussian_pair_stats a ((mu1, sig1), (mu2, sig2)) =
      (dot a (sqvec (mu1 - mu2)), dot a sig2).
Proof.
  intros d a mu1 sig1 mu2 sig2 Ha Hsig.
  unfold gaussian_pair_stats.
  rewrite Rmax_right.
  - reflexivity.
  - apply dot_vec_noneg; assumption.
Qed.

(* Recursive binary-well Gaussian schedule.  The class at index [i] has
   mean [m^i * 1].  For [i = 0] its covariance is [1]; for later indices
   it accumulates the pairwise separation scales against the earlier
   classes, all pointed at coordinate [i]. *)
Fixpoint gaussian_schedule_sigma_sum {d : nat}
  (m : R) (i k : nat) : vec d :=
  match k with
  | O => 0
  | S k' =>
      gaussian_schedule_sigma_sum m i k' +
      (((m ^ i - m ^ k') * (m ^ i - m ^ k'))%R *
       (m * canon_e i + 1))%Vec
  end.

Definition gaussian_schedule_mu {d : nat} (m : R) (i : nat) : vec d :=
  (m ^ i)%R * 1.

Definition gaussian_schedule_sigma {d : nat} (m : R) (i : nat) : vec d :=
  match i with
  | O => 1
  | S _ => gaussian_schedule_sigma_sum m i i
  end.

Definition gaussian_schedule_class {d : nat} (m : R) (i : nat)
  : @gaussian d :=
  (gaussian_schedule_mu m i, gaussian_schedule_sigma m i).

Fixpoint gaussian_schedule_from {d : nat} (m : R) (start n : nat)
  : Vector.t (@gaussian d) n :=
  match n with
  | O => []
  | S n' =>
      gaussian_schedule_class m start ::
      gaussian_schedule_from m (S start) n'
  end.

Definition gaussian_schedule {d : nat} (m : R) (n : nat)
  : Vector.t (@gaussian d) n :=
  gaussian_schedule_from m O n.


Close Scope vec_scope.
Close Scope R_scope.
