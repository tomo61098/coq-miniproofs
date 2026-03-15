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
  
Definition is_binary {n: nat} (u: vec n) :=
  Forall (fun x: R => x = 0 \/ x = 1)%R u
.

Definition c_separated_valid {n k: nat}
  (c: R) (m: nat) (a: vec n) (l: Vector.t gaussian k) :=
  is_binary a /\
  dot a 1 = (INR m) /\
  c_separates c a l
.

Definition is_partition {n: nat} (a s: vec n) :=
  is_binary a /\ dot a s = dot s 1 / 2
.

Definition is_positive {n: nat} (u: vec n) :=
  Forall (fun x => 0 < x)%R u
.


Inductive is_vec_leq : forall {n: nat}, vec n -> vec n -> Prop :=
  | vclq_nil : is_vec_leq [] []
  | vclq_con : forall (n: nat) (a b: R) (x y: vec n),
    a <= b -> is_vec_leq x y -> is_vec_leq (a::x) (b::y)
.

Lemma pos_leq: forall (n: nat) (x: vec n),
  is_positive x -> is_vec_leq 0 x.
Proof.
  induction x.
    - constructor.
    - intros. inv H.
      app_inj_nat H2.
      subst. constructor; auto. lra.
Qed.

Lemma dot_vec_noneg:
  forall (n: nat) (a x y: vec n),
  is_vec_leq 0 a ->
  is_vec_leq x y -> dot a x <= dot a y
.
Proof.
  induction n; intros.
    - rewrite (eta0 _). simpl. lra.
    - inv H.
      inv H0.
      app_inj_nat H3.
      app_inj_nat H2.
      app_inj_nat H7.
      app_inj_nat H4.
      subst.
      rewrite !dot_step. simpl.
      specialize (IHn _ _ _ H6 H9).
      apply (Rmult_le_compat_l _ _ _ H5) in H8.
      lra.
Qed.

Lemma dot_vec_noneg_0: forall (n: nat) (x y: vec n),
  is_vec_leq 0 x -> is_vec_leq 0 y ->
  0 <= dot x y.
Proof.
  induction n; intros.
    - rewrite (eta0 x). simpl. lra.
    - inv H. inv H0.
      app_inj_nat H8.
      app_inj_nat H7.
      app_inj_nat H4.
      app_inj_nat H3.
      subst. rewrite dot_step. simpl.
      specialize (IHn _ _ H6 H10).
      assert (A:= Rmult_le_pos _ _ H5 H9).
      lra.
Qed.

Lemma sqrtvec_dist:
  forall (n: nat) (c: R) (v: vec n),
    (0 <= c) -> (is_vec_leq 0 v) ->
    sqrtvec (c * v) = (sqrt c) * sqrtvec v
.
Proof.
  induction n; intros.
    - rewrite (eta0). apply eta0.
    - rewrite (eta v). cbn.
      specialize (IHn c (tl v)).
      unfold sqrtvec in IHn.
      unfold multvec in IHn.
      rewrite (IHn H).
      f_equal.
      inv H0.
      --
      app_inj_nat H3.
      app_inj_nat H4.
      subst. simpl.
      apply (sqrt_mult _ _ H H5).
      -- inv H0.
         app_inj_nat H3.
         app_inj_nat H4.
         subst. auto.
Qed.

Lemma sq_sqrt_vec: forall (n: nat) (u: vec n),
  is_vec_leq 0 u ->
  sqvec (sqrtvec u) = u
.
Proof.
  induction n; intros.
    - rewrite eta0. apply eta0.
    - inv H.
      app_inj_nat H2.
      app_inj_nat H3.
      subst. cbn.
      specialize (IHn y H5).
      unfold sqvec, sqrtvec in IHn.
      rewrite IHn.
      f_equal. apply sqrt_def. apply H4.
Qed.

Definition partition_to_gaussians {n: nat} (m: nat) (s: vec n) : Vector.t (@gaussian n) 3 :=
[
  (0,zipvecs Rmin ((2*(INR m))*s) 1) ;
  (sqrt (2*(INR m)/dot s 1) * (sqrtvec s), 1) ;
  (- ((sqrt (dot s 1)) * 1), (2*(INR m)) * s)
].

Theorem cm_separated_NP_completness_left:
  forall (n: nat) (s: vec n),
  is_positive s ->
  (exists a m, (0 < m)%nat /\
    c_separated_valid (1%R) m a (partition_to_gaussians m s))
  -> exists a, is_partition a s
.
Proof.
  unfold c_separated_valid, is_partition.
  simpl.
  intros n s P [a [m [M [A [B [[_ [E [_ [G _]]]] [[_ [_ _]] _]]]]]]].
  exists a.
  apply (conj A).
  rewrite vec_0_neg in E.
  rewrite vec_sub_neg in G.
  rewrite (vec_plus_comm 0 _) in G. 
  rewrite vec_plus_0 in G.
  rewrite Rmult_1_l in E, G.
  rewrite sqvec_dist in G.
  assert (B2: forall (n: nat) (f: vec (S n)), is_positive f -> 0 < dot f 1). 
  { intros. inv H.
    app_inj_nat H1.
    subst. rewrite dot_step. simpl.
    apply pos_leq in H3.
    assert (B3: forall n, is_vec_leq 0 (1: vec n)).
    { induction n1. - constructor. - constructor; auto. lra. }
    assert (B4:= dot_vec_noneg_0 _ _ _ H3 (B3 _)).
    lra.
  }
  destruct n.
  - rewrite (eta0 s). simpl. rewrite (eta0 a). simpl. lra.
  -
  specialize (B2 _ s P).
  assert (A2: 0 <= dot s 1) by lra.
  rewrite (sqrt_def _ A2) in G.
  rewrite sqvec_1 in G.
  rewrite 2dot_mult_dist_r in G.
  rewrite B in G.
  rewrite sqvec_neg in E.
  rewrite sqvec_dist in E.
  rewrite (sq_sqrt_vec _ _ (pos_leq _ _ P)) in E.
  assert (A3:= Rinv_0_lt_compat _ (B2)).
  apply (Rmult_lt_compat_l _ _ _ (lt_INR _ _ M)) in A3.
  rewrite Rmult_0_r in A3.
  assert (Dum: 0 < 2) by lra.
  apply (Rmult_lt_compat_l _ _ _ Dum) in A3.
  rewrite Rmult_0_r in A3.
  replace ((2 * ((INR m) * / dot s 1%Vec))%R) with (2 * (INR m) / dot s 1) in A3 by lra.
  rewrite (sqrt_def _ (Rlt_le _ _ A3)) in E.
  rewrite B in E.
  rewrite dot_mult_dist_r in E.
  replace (2 * (INR m) * dot a s)%R with (2 * dot a s * (INR m))%R in G by lra.
  apply (Rmult_le_reg_r _ _ _ (lt_INR _ _ M)) in G.
  rewrite <- (Rmult_1_l (INR m)) in E at 1.
  replace (2 * (INR m) / dot s (1%Vec) * dot a s)%R with (2 * / dot s 1%Vec * dot a s * (INR m))%R in E by lra.
  apply (Rmult_le_reg_r _ _ _ (lt_INR _ _ M)) in E.
  clear A3 Dum.
  apply (Rmult_le_compat_r _ _ _ A2) in E.
  rewrite Rmult_1_l in E.
  replace (2 * / dot s (1%Vec) * dot a s * dot s (1%Vec))%R with (2 * (dot a s * dot s (1%Vec) * / dot s (1%Vec)))%R in E by lra.
  assert (C2: (dot s 1%Vec <> 0)%R) by lra.
  rewrite (Rmult_inv_r_id_l _ _ C2) in E.
  assert (C3: (2 * dot a s = dot s (1%Vec))%R) by lra.
  rewrite <- C3.
  lra.
Qed.

Fixpoint is_binary_to_nat_sum {n: nat} (l: vec n): nat.
destruct l.
  - apply O.
  - destruct (Req_dec_T 1 h).
    -- apply (S (is_binary_to_nat_sum _ l)).
    -- apply (is_binary_to_nat_sum _ l).
Defined.

Lemma pos_and_bin_dot:
  forall (n: nat) (a l: vec n),
  is_binary a -> is_positive l ->
  0 < dot a l -> (0 < is_binary_to_nat_sum a)%nat
.
Proof.
  induction n; intros.
    - rewrite (eta0 a) in H1.
      simpl in H1. lra.
    - inv H; app_inj_nat H3;
      inv H0; app_inj_nat H3;
      rewrite dot_step in H1; simpl in H1;
      destruct H4; subst.
      + rewrite Rmult_0_l in H1.
        rewrite Rplus_0_l in H1.
        specialize (IHn _ _ H5 H7 H1).
        simpl. destruct Req_dec_T; auto.
      + simpl. destruct Req_dec_T.
        * lia.
        * lra.
Qed. 

Lemma pos_dot_1: forall (n: nat) (p: vec (S n)),
  is_positive p -> 0 < dot p 1
.
Proof.
  induction n; intros.
    - inv H. app_inj_nat H1.
      rewrite dot_step, (eta0 v). simpl. lra.
    - inv H. app_inj_nat H1.
      specialize (IHn _ H3).
      rewrite dot_step.
      simpl. rewrite Rmult_1_r.
      rewrite <- (Rplus_0_l 0).
      apply Rplus_lt_compat; auto.
Qed.

Lemma bin_sum_dot_1: forall (n: nat) (a: vec n),
  is_binary a ->
  INR (is_binary_to_nat_sum a) = dot a 1
.
Proof.
  induction a; intros.
    - auto.
    - simpl.
      inv H; app_inj_nat H2;
      cbn; destruct (Req_dec_T), H3; subst.
      + lra.
      + rewrite S_INR. rewrite (IHa H4). lra.
      + rewrite Rmult_0_l, Rplus_0_l. apply IHa.
        apply H4.
      + contradiction.
Qed.

Lemma is_bin_is_pos_dot_leq : forall (n: nat) (a b: vec n),
  is_binary a -> is_positive b ->
    dot a b <= dot b 1
.
Proof.
  induction n; intros.
    - rewrite (eta0 a), (eta0 b). simpl. lra.
    - inv H; app_inj_nat H2;
      inv H0; app_inj_nat H2.
      destruct H3; subst;
      specialize (IHn _ _ H4 H6);
      rewrite dot_step; cbn; lra.
Qed.

Lemma zipvec_pos_min_leq: forall (n: nat) (u v w: vec n),
  is_vec_leq 0 u ->
  dot u (zipvecs Rmin v w) <= dot u w
.
Proof.
  induction n; intros.
    - rewrite (eta0 (zipvecs _ _ _)), (eta0 u).
      simpl. lra.
    - rewrite (eta u), (eta v), (eta w).
      rewrite 2(dot_step (hd _ :: _) _).
      inv H. app_inj_nat H2. app_inj_nat H3.
      simpl hd. simpl tl.
      specialize (IHn y (tl v) (tl w) H5).
      assert (A:= Rmin_r (hd v) (hd w)).
      apply (Rmult_le_compat_l _ _ _ H4) in A.
      lra.
Qed.

Lemma bin_is_vec_leq: forall (n: nat) (a: vec n),
  is_binary a -> is_vec_leq 0 a
.
Proof.
  induction a.
    - constructor.
    - intros.
      inv H. app_inj_nat H2.
      constructor; auto; lra.
Qed.

Lemma zipvecs_min_comm: forall (n: nat) (u v: vec n),
  zipvecs Rmin u v = zipvecs Rmin v u
.
Proof.
  induction n; intros.
    - rewrite eta0. apply eta0.
    - rewrite (eta u), (eta v).
      cbn.
      rewrite IHn.
      f_equal.
      apply Rmin_comm.
Qed.


Lemma sqvec_plus_leq: forall {n: nat} (a u v: vec n),
  is_vec_leq 0 a ->
  is_vec_leq 0 u ->
  is_vec_leq 0 v ->
  dot a (sqvec u) <= dot a (sqvec (u + v)) 
.
Proof.
  induction n; intros.
    - rewrite (eta0 a). simpl. lra.
    - inv H. inv H0. inv H1.
      app_inj_nat H4.
      app_inj_nat H5.
      app_inj_nat H13.
      app_inj_nat H12.
      app_inj_nat H8.
      app_inj_nat H9.
      specialize (IHn _ _ _ H7 H11 H15).
      assert (E:= Rle_0_sqr b0).
      rewrite Rsqr_def in E.
      assert (F: (b0 <= b0 + b1)%R) by lra.
      assert (E2:= Rle_0_sqr (b0 + b1)).
      rewrite Rsqr_def in E2.
      apply (Rmult_le_compat_l _ _ _ H6) in E, E2.
      rewrite Rmult_0_r in E, E2.
      assert (F2:= Rmult_le_compat _ _ _ _ H10 H10 F F).
      apply (Rmult_le_compat_l _ _ _ H6) in F2.
      cbn.
      unfold sqvec, plusvecs in IHn.
      lra.
Qed.

Lemma is_vec_leq_1: forall (n: nat),
  @is_vec_leq n 0 1
.
Proof.
  induction n; constructor.
  - lra.
  - apply IHn.
Qed.

Lemma L3: forall (n: nat) (a: R) (s: vec n),
  is_positive s ->
  0 <= a ->
  @is_vec_leq n 0 (sqrt (a + dot s 1) * 1)
.
Proof.
  induction n; intros.
  - constructor.
  - inv H. app_inj_nat H2.
    rewrite dot_step.
    simpl hd. simpl tl. rewrite Rmult_1_r.
    assert (A:= dot_vec_noneg_0 n v 1 (pos_leq _ v H4) (is_vec_leq_1 n)).
    assert (A2: 0 <= x + dot v 1) by lra.
    rewrite vec_mult_step.
    simpl hd. simpl tl.
    cbn.
    apply vclq_con.
  + rewrite Rmult_1_r. apply sqrt_positivity. lra.
  + rewrite <- Rplus_assoc. apply IHn; auto.
    lra.
Qed. 

Lemma L4: forall (n: nat) (a: R) (b: vec n),
  0 <= a -> is_vec_leq 0 b ->
  is_vec_leq 0 (a * b)
.
Proof.
  induction n; intros.
    - rewrite eta0. constructor.
    - inv H0. app_inj_nat H3. app_inj_nat H4.
      simpl. cbn. apply vclq_con.
    + apply (Rmult_le_compat_l _ _ _ H) in H5. lra.
    + apply IHn; auto.
Qed.

Lemma L5: forall (n: nat) (b: vec n),
  is_vec_leq 0 b -> is_vec_leq 0 (sqrtvec b)
.
Proof.
  induction b.
  - constructor.
  - intros. inv H. app_inj_nat H2.
    app_inj_nat H5.
    cbn.
    constructor.
  + apply (sqrt_positivity _ H4).
  + apply (IHb H6).
Qed. 

Theorem cm_separated_NP_completness_right:
  forall (n: nat) (s: vec (S n)),
  is_positive s ->
  (exists a, is_partition a s) ->
  (exists a m, (0 < m)%nat /\
    c_separated_valid (1%R) m a (partition_to_gaussians m s))
.
Proof.
  unfold is_partition, c_separated_valid.
  intros n s P [a [Ba Pa]].
  exists a, (is_binary_to_nat_sum a).
  assert (A:= pos_dot_1 _ _ P).
  assert (B:=is_bin_is_pos_dot_leq _ _ _ Ba P).
  assert (C: 0 < dot s 1 / 2).
  { apply Rdiv_lt_0_compat; lra. }
  assert (C2: 0 < dot a s) by lra.
  assert (C3:= pos_and_bin_dot _ _ _ Ba P C2). 
  apply (conj C3).
  apply (conj Ba).
  assert (C4:= (eq_sym (bin_sum_dot_1 _ _ Ba))).
  apply (conj C4).
  apply lt_INR in C3.
  simpl (INR 0) in C3.
  unfold partition_to_gaussians.
  rewrite (bin_sum_dot_1 _ _ Ba).
  assert (D: 0 < dot s 1) by lra.
  unfold c_separates.
  apply conj.
  + apply conj.
  * rewrite vec_0_neg.
    rewrite sqvec_neg.
    rewrite sqvec_dist.
    rewrite (sq_sqrt_vec _ _ (pos_leq _ _ P)).
    assert (E:= Rinv_0_lt_compat _ D).
    assert (E2: 0 < dot a 1) by lra.
    apply (Rmult_lt_compat_l _ _ _ E) in E2.
    rewrite Rmult_0_r in E2.
    assert (E3: 0 < 2 * dot a 1 / dot s 1) by lra.
    rewrite (sqrt_def _ (Rlt_le _ _ E3)).
    rewrite dot_mult_dist_r.
    rewrite Pa.
    rewrite 2Rdiv_def.
    replace ((2 * dot a 1%Vec * / dot s 1%Vec * (dot s 1%Vec * / 2))%R) with ((2 * / 2 * dot s 1%Vec * / dot s 1%Vec * dot a 1%Vec)%R) by lra.
    rewrite Rmult_inv_r by lra.
    rewrite 2Rmult_1_l.
    rewrite Rmult_inv_r by lra.
    rewrite Rmult_1_l.
    apply zipvec_pos_min_leq.
    apply bin_is_vec_leq. auto.
  * apply conj.
  - rewrite Rmult_1_l.
    rewrite vec_0_neg.
    rewrite sqvec_neg.
    rewrite sqvec_dist.
    rewrite (sq_sqrt_vec _ _ (pos_leq _ _ P)).
    assert (E:= Rinv_0_lt_compat _ D).
    assert (E2: 0 < dot a 1) by lra.
    apply (Rmult_lt_compat_l _ _ _ E) in E2.
    rewrite Rmult_0_r in E2.
    assert (E3: 0 < 2 * dot a 1 / dot s 1) by lra.
    rewrite (sqrt_def _ (Rlt_le _ _ E3)).
    rewrite dot_mult_dist_r.
    rewrite Pa.
    rewrite 2Rdiv_def.
    replace ((2 * dot a 1%Vec * / dot s 1%Vec * (dot s 1%Vec * / 2))%R) with ((2 * / 2 * dot s 1%Vec * / dot s 1%Vec * dot a 1%Vec)%R) by lra.
    rewrite Rmult_inv_r by lra.
    rewrite Rmult_1_l.
    rewrite Rmult_inv_r by lra.
    rewrite Rmult_1_l.
    lra.
  - apply conj.
  -- rewrite Rmult_1_l.
     rewrite vec_sub_neg.
     rewrite vec_plus_comm.
     rewrite vec_plus_0.
     rewrite sqvec_dist.
     rewrite (sqrt_def _ (Rlt_le _ _ D)).
     rewrite sqvec_1.
     rewrite dot_mult_dist_r.
     assert (E:= zipvec_pos_min_leq _ a 1 (2 * dot a 1 * s) (bin_is_vec_leq _ _ Ba)).
     rewrite zipvecs_min_comm in E.
     rewrite dot_mult_dist_r in E.
     rewrite Pa in E. lra.
  -- apply conj.
  ++ rewrite Rmult_1_l.
     rewrite vec_sub_neg.
     rewrite vec_plus_comm.
     rewrite vec_plus_0.
     rewrite sqvec_dist.
     rewrite (sqrt_def _ (Rlt_le _ _ D)).
     rewrite sqvec_1.
     rewrite 2dot_mult_dist_r.
     rewrite Pa. lra.
  ++ apply I.
  + apply conj.
  * apply conj.
  -- rewrite Rmult_1_l.
     rewrite vec_sub_neg.
     rewrite vec_plus_comm.
     assert (E2:= L3 _ 0 s P (or_intror (eq_refl 0%R))).
     rewrite Rplus_0_l in E2.
     assert (F4: 0 <= (2 * dot a 1 / dot s 1)).
    { rewrite Rdiv_def. rewrite C4.
      apply Rinv_0_lt_compat in D.
      rewrite <- (Rmult_0_l 0).
      apply Rmult_le_compat; lra. }
    assert (F2:= sqrt_positivity _ F4).
    assert (F3:= L5 _ _ (pos_leq _ _ P)).
    apply (L4 _ _ _ F2) in F3.
    assert (E:= sqvec_plus_leq _ _  _  (bin_is_vec_leq _ a Ba) F3 E2).
    rewrite vec_plus_comm in E.
    rewrite sqvec_dist in E.
    rewrite (sq_sqrt_vec _ _ (pos_leq _ _ P)) in E.
    rewrite (sqrt_def _ F4) in E.
    rewrite dot_mult_dist_r in E.
    rewrite Pa in E.
    assert (G: (2 * dot a 1%Vec / dot s 1%Vec * (dot s 1%Vec / 2) = dot a 1%Vec)%R).
    { rewrite 2Rdiv_def.
      rewrite Rmult_assoc.
      rewrite <- (Rmult_assoc _ _ (/ 2)).
      rewrite Rmult_inv_l by lra.
      lra. }
    rewrite G in E.
    apply E.
  -- apply conj.
  ++ rewrite Rmult_1_l.
     rewrite vec_sub_neg.
     assert (E2:= L3 _ 0 s P (or_intror (eq_refl 0%R))).
     rewrite Rplus_0_l in E2.
     assert (F4: 0 <= (2 * dot a 1 / dot s 1)).
    { rewrite Rdiv_def. rewrite C4.
      apply Rinv_0_lt_compat in D.
      rewrite <- (Rmult_0_l 0).
      apply Rmult_le_compat; lra. }
    assert (F2:= sqrt_positivity _ F4).
    assert (F3:= L5 _ _ (pos_leq _ _ P)).
    apply (L4 _ _ _ F2) in F3.
    assert (E:= sqvec_plus_leq _ _  _  (bin_is_vec_leq _ a Ba) E2 F3).
    rewrite sqvec_dist in E.
    rewrite sqvec_1 in E.
    rewrite (sqrt_def _ (Rlt_le _ _ D)) in E.
    rewrite dot_mult_dist_r in E.
    rewrite dot_mult_dist_r.
    rewrite Pa.
    assert (G: (2 * dot a 1%Vec * (dot s 1%Vec / 2) = dot a 1%Vec * dot s 1%Vec)%R).
    { lra. }
    rewrite G.
    rewrite vec_plus_comm.
    lra.
  ++ apply I.
  * apply conj.
  -- apply I.
  -- apply I.
Qed.

Lemma is_bin_sum_bound: forall (n: nat) (a: vec n),
  (is_binary_to_nat_sum a <= n)%nat
.
Proof.
  induction a.
  - constructor.
  - simpl.
    destruct (Req_dec_T); lia.
Qed.

Lemma is_positive_1: forall (n: nat),
  @is_positive n 1
.
Proof.
  induction n.
  - constructor.
  - simpl. constructor.
    -- lra.
    -- apply IHn.
Qed.

Lemma dot_1_1: forall (n: nat),
  @dot n 1 1 = INR n
.
Proof.
  induction n.
  - simpl. apply eq_refl.
  - rewrite dot_step, S_INR. simpl. lra.
Qed.

Theorem c_separation_NP_complete:
  forall (n: nat) (s: vec (S n)),
    is_positive s ->
    (exists a, is_partition a s) <->
    (exists a m, (O < m <= (S n))%nat /\
    c_separated_valid (1%R) m a (partition_to_gaussians m s))
.
Proof.
  intros. constructor.
  - intros P.
    destruct (cm_separated_NP_completness_right _ _ H P) as [a [m [L D]]].
    exists a, m.
    constructor; auto.
    constructor; auto.
    destruct D as [B [E F]].
    assert (J:= is_bin_is_pos_dot_leq _ _ _ B (is_positive_1 _)).
    rewrite dot_1_1 in J.
    rewrite E in J.
    apply (INR_le _ _ J).
  - intros [a [m [L G]]].
    apply cm_separated_NP_completness_left; auto.
    exists a, m.
    constructor; auto.
    lia.
Qed.

(** assume c = 1 from now on **)
Definition separation {n: nat} (a: vec n)
  (g1 g2: gaussian) : R :=
  let (mu1, sigm1) := g1 in
  let (mu2, sigm2) := g2 in
    dot a ((sqvec (mu1 - mu2))) /
    Rmax (dot a sigm1) (dot a sigm2)
.

Definition missing_separation {n: nat} (a: vec n)
  (g1 g2: gaussian) : R :=
  Rmax 0 (1 - separation a g1 g2)
.

Lemma Rmax_le_l: forall a b c,
  Rmax a b <= c -> a <= c
.
Proof.
  intros a b c A.
  unfold Rmax in A.
  destruct (Rle_dec a b); lra.
Qed.

Lemma Rmax_le_r: forall a b c,
  Rmax a b <= c -> b <= c
.
Proof.
  intros a b c A.
  unfold Rmax in A.
  destruct (Rle_dec a b); lra.
Qed.

Theorem beta_to_separated :
  forall (n: nat) (a: vec n) (g1 g2: gaussian) (b: R),
  let (_, sig1) := g1 in
  let (_, sig2) := g2 in
  0 < dot a sig1 \/ 0 < dot a sig2 -> 
  (missing_separation a g1 g2 <= b <-> c_separates (1 - b) a [g1 ; g2])
.
Proof.
  intros n a [mu1 sig1] [mu2 sig2] b N.
  split; intros A.
  - unfold missing_separation in A.
    unfold separation in A.
    assert (Al:= Rmax_le_l _ _ _ A).
    assert (Ar:= Rmax_le_r _ _ _ A).
    assert (0 < Rmax (dot a sig1) (dot a sig2)).
    { destruct N;
      unfold Rmax; destruct Rle_dec; lra. }
    assert (Br: (1 - b) * Rmax (dot a sig1) (dot a sig2) <= dot a (sqvec (mu1 - mu2))).
    { apply (Rmult_le_reg_r _ _ _ (Rinv_0_lt_compat _ H)).
      field_simplify; lra. }
    rewrite Rmax_dist_mult_l in Br.
    
    Search (c_separates).
    split; split.
    Search (_ * Rmax _ _)%R.
    Search (_ * Rmax _ _)%R.
  

Close Scope vec_scope.
Close Scope R_scope.