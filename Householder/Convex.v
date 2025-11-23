Load Rsets.

Open Scope R.
Open Scope vec_scope.

Structure ConvexSet {n} := make_convexset {
  convexset_mem :> set (vec n) ;
  has_mid: forall (x y: vec n) (lam: R),
    0 <= lam <= 1 ->
    is_mem convexset_mem x ->
    is_mem convexset_mem y -> is_mem convexset_mem (lam * x + (1-lam) * y);
}.

Definition ConvexFunc {n} (D: @ConvexSet n) (f: vec n -> R) :=
  forall (x y: vec n),
    is_mem D x -> is_mem D y ->
  forall (lam: R),
    (0 <= lam <= 1)%R ->
    f (lam * x + (1-lam) * y) <= lam * f x + (1-lam) * f y
.

Definition subgradient {n} (gx: vec n) (x: vec n) (D: ConvexSet) (f: vec n -> R):=
  forall (y: vec n),
    is_mem D y ->
    dot gx (y - x) + f x <= f y
.

Theorem subgrad_conv {n} (D: @ConvexSet n) (f: vec n -> R):
  (exists (g: vec n -> vec n),
    forall (x: vec n),
      is_mem D x -> 
      subgradient (g x) x D f) ->
    ConvexFunc D f
.
Proof.
  intros [g A] x y Dx Dy lam ZO.
  specialize (A (lam * x + (1-lam)*y) (has_mid D _ _ lam ZO Dx Dy)).
  assert (E:= A x Dx).
  assert (F:= A y Dy).
  assert (Z: 0 <= lam) by lra.
  assert (O: 0 <= 1 - lam) by lra.
  apply (Rmult_le_compat_l _ _ _ Z) in E.
  apply (Rmult_le_compat_l _ _ _ O) in F.
  assert (B:= Rplus_le_compat _ _ _ _ E F).
  rewrite <- ? vec_plus_sub in B.
  rewrite ? dot_dist in B.
  rewrite ? dot_dist_l in B.
  assert (C: (lam * dot (g (lam * x + (1 - lam) * y))%Vec x +
             (1 - lam) * dot (g (lam * x + (1 - lam) * y))%Vec y +
             dot (g (lam * x + (1 - lam) * y))%Vec (- (lam * x + (1 - lam) * y))%Vec +
             f (lam * x + (1 - lam) * y)%Vec <= lam * f x + (1 - lam) * f y)%R) by lra.
  rewrite <- vec_mult_neg1 in C.
  rewrite (vec_mult_dist_r (-1)) in C.
  rewrite (dot_dist _ (-1 * _)) in C.
  replace (dot (g (lam * x + (1 - lam) * y))
       (-1 * (lam * x))) with (-1*lam* (dot (g (lam * x + (1 - lam) * y))
       x)%Vec)%R in C.
  2:{ rewrite (dot_comm _ (-1*_)).
      rewrite <-2 dot_mult_commute.
      rewrite (dot_comm x _).
      lra. }
  replace (dot (g (lam * x + (1 - lam) * y))
       (-1 * ((1-lam) * y))) with (-1*(1-lam)* (dot (g (lam * x + (1 - lam) * y))
       y)%Vec)%R in C.
  2:{ rewrite (dot_comm _ (-1*_)).
      rewrite <-2 dot_mult_commute.
      rewrite (dot_comm y _).
      lra. }
  lra.
Qed.

Theorem Cauchy_Schwarz:
  forall (n: nat) (u v: vec n),
    (dot u v)^2 <= dot u u * dot v v
.
Proof.
  intros.
  destruct (Req_dec (dot v v) 0).
    - assert (A:= dot_eq0 _ H).
      rewrite A. rewrite (dot_comm u 0).
      rewrite 2 dot_0. lra.
    - assert (A:= dot_geq0 (u + (- dot u v * / dot v v) * v)).
      rewrite dot_dist_l in A.
      rewrite 2 dot_dist in A.
      rewrite <- 2 (dot_mult_commute _ v) in A.
      rewrite 2 (dot_comm _ (_ * v)) in A.
      rewrite <- 2 (dot_mult_commute _ v) in A.
      rewrite (Rmult_assoc _ _ (dot v v)) in A.
      rewrite (Rinv_l _ H) in A.
      rewrite Rmult_1_r in A.
      apply (Rmult_le_compat_l _ _ _ (dot_geq0 v)) in A.
      rewrite Rmult_0_r in A.
      rewrite 3 Rmult_plus_distr_l in A.
      rewrite <- 4 Rmult_assoc in A.
      rewrite ! (Rinv_r_simpl_m _ _ H) in A.
      rewrite ! (dot_comm v u) in A.
      lra.
Qed.

Corollary max_dot_eq:
  forall (n: nat) (u v: vec n),
    dot v v <= dot u u -> dot u v <= dot u u
.
Proof.
  intros.
  assert (A:= Cauchy_Schwarz n u v).
  assert (B: dot u v ^2 <= dot u u * dot u u).
  { assert (C:= dot_geq0 u).
    assert (D:= dot_geq0 v).
    assert (E: dot u u * dot v v <= dot u u * dot u u).
    { apply (Rmult_le_compat_l _ _ _ C H). }
    lra.
  }
  apply Rsqr_incr_0_var.
    - rewrite 2 Rsqr_pow2.
      lra.
    - apply dot_geq0.
Qed.

Corollary min_dot_eq:
  forall (n: nat) (u v: vec n),
    dot v v <= dot u u -> -dot u u <= dot u v
.
Proof.
  intros.
  assert (F: dot v v <= dot (-1 * u) (-1 * u)).
  { rewrite <- dot_mult_commute.
    rewrite (dot_comm u).
    rewrite <- dot_mult_commute.
    lra.
  }
  assert (A:= max_dot_eq n (-1 * u) v F).
  rewrite <- 2 dot_mult_commute in A.
  rewrite (dot_comm u (-1 * u)) in A.
  rewrite <- dot_mult_commute in A.
  lra.
Qed.

Close Scope vec_scope.