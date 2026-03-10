Require Import Reals.
Require Import Lra Lia.
Require Import Ring.
Require Import Vector.
Require Import Coq.Logic.Eqdep_dec.
Require Import Field.

Import VectorNotations.
Open Scope R_scope.

(* -------- Convexity -------- *)

Definition convex (f : R -> R) : Prop :=
  forall x y t,
    0 <= t <= 1 ->
    f (t * x + (1 - t) * y) <= t * f x + (1 - t) * f y.

Definition secant_slope (f : R -> R) (x y : R) : R :=
  (f y - f x) / (y - x).

(* -------- Pure Vector.t utilities -------- *)

Fixpoint sumV {n : nat} (v : Vector.t R n) : R :=
  match v with
  | [] => 0
  | x :: xs => x + sumV xs
  end.

(* Sum of all entries of a vector *)
Fixpoint vsum {n : nat} (v : Vector.t R n) : R :=
  match v with
  | [] => 0
  | x :: xs => x + vsum xs
  end.

(* Sum of the first [k] entries of a vector.
   If [k] is bigger than the length, this just returns the full sum. *)
Fixpoint prefix_sum {n : nat} (k : nat) (v : Vector.t R n) : R :=
  match k, v with
  | 0, _ => 0
  | S _, [] => 0
  | S k', x :: xs => x + prefix_sum k' xs
  end.

(* Descending sortedness on vectors *)
Inductive sorted_desc : forall n, Vector.t R n -> Prop :=
| sorted_desc_nil :
    sorted_desc 0 []
| sorted_desc_single :
    forall x,
      sorted_desc 1 [x]
| sorted_desc_cons :
    forall n x y (v : Vector.t R n),
      x >= y ->
      sorted_desc (S n) (y :: v) ->
      sorted_desc (S (S n)) (x :: y :: v).

(* Weak prefix-majorization: no equal-total-sum requirement *)
Definition weak_majorized_raw {n : nat} (v w : Vector.t R n) : Prop :=
  forall k, prefix_sum k v >= prefix_sum k w.

(* Weak majorization with both vectors sorted descending *)
Definition weak_majorized {n : nat} (v w : Vector.t R n) : Prop :=
  sorted_desc n v /\
  sorted_desc n w /\
  weak_majorized_raw v w.

(* Prefix-majorization + equal total sum *)
Definition majorized_raw {n : nat} (v w : Vector.t R n) : Prop :=
  weak_majorized_raw v w /\
  vsum v = vsum w.

(* Standard majorization usually assumes both vectors are sorted descending *)
Definition majorized {n : nat} (v w : Vector.t R n) : Prop :=
  sorted_desc n v /\
  sorted_desc n w /\
  majorized_raw v w.

Lemma majorized_raw_tails :
  forall (n : nat) (h : R) (v w : Vector.t R n),
    majorized_raw (h :: v) (h :: w) ->
    majorized_raw v w.
Proof.
  intros n h v w [Hpref Hsum].
  split.
  - intros k.
    specialize (Hpref (S k)).
    simpl in Hpref.
    lra.
  - simpl in Hsum.
    lra.
Qed.

Lemma weak_majorized_raw_tails :
  forall (n : nat) (h : R) (v w : Vector.t R n),
    weak_majorized_raw (h :: v) (h :: w) ->
    weak_majorized_raw v w.
Proof.
  intros n h v w Hpref.
  intros k.
  specialize (Hpref (S k)).
  simpl in Hpref.
  lra.
Qed.

Ltac inv H := inversion H; subst.
Ltac app_inj_nat H := apply (inj_pair2_eq_dec _ Nat.eq_dec) in H; subst.


Lemma sorted_desc_tail :
  forall (n : nat) (h : R) (v : Vector.t R n),
    sorted_desc (S n) (h :: v) ->
    sorted_desc n v.
Proof.
  intros n h v H.
  destruct v as [| x n' v'].
  - inversion H. constructor.
  - inv H. app_inj_nat H4.
    exact H5.
Qed.

Lemma majorized_tails :
  forall (n : nat) (h : R) (v w : Vector.t R n),
    majorized (h :: v) (h :: w) ->
    majorized v w.
Proof.
  intros n h v w [Hs1 [Hs2 Hmaj]].
  repeat split.
  - apply sorted_desc_tail with (h := h). exact Hs1.
  - apply sorted_desc_tail with (h := h). exact Hs2.
  - apply majorized_raw_tails with (h := h). exact Hmaj.
  - inv Hmaj. simpl in H0. lra.
Qed.

Lemma weak_majorized_tails :
  forall (n : nat) (h : R) (v w : Vector.t R n),
    weak_majorized (h :: v) (h :: w) ->
    weak_majorized v w.
Proof.
  intros n h v w [Hv [Hw Hmaj]].
  repeat split.
  - apply (sorted_desc_tail _ _ _ Hv).
  - apply (sorted_desc_tail _ _ _ Hw).
  - apply (weak_majorized_raw_tails _ h _ _ Hmaj).
Qed.

Inductive sorted_asc : forall n, Vector.t R n -> Prop :=
| sorted_asc_nil :
    sorted_asc 0 []
| sorted_asc_single :
    forall x,
      sorted_asc 1 [x]
| sorted_asc_cons :
    forall n x y (v : Vector.t R n),
      x <= y ->
      sorted_asc (S n) (y :: v) ->
      sorted_asc (S (S n)) (x :: y :: v).

Fixpoint inv_weak_majorized_raw {n : nat} (u v: Vector.t R n) : Prop.
destruct n.
  - apply True.
  - apply (vsum u >= vsum v /\ inv_weak_majorized_raw n (tl u) (tl v)).
Defined.

Lemma vsum_pref_sum: forall n k (u: Vector.t R n),
  prefix_sum (k + n) u = vsum u
.
Proof.
  induction n; intros k u.
    - rewrite (nil_spec u). destruct k; trivial.
    - rewrite (eta u). rewrite Nat.add_succ_r. simpl. f_equal. apply IHn.
Qed.

Lemma prefix_sum_shiftin_leq: forall n k (x: R) (u: Vector.t R n),
  (k <= n)%nat -> prefix_sum k (shiftin x u) = prefix_sum k u
.
Proof.
  induction n, k.
  - trivial.
  - intros. lia.
  - trivial.
  - intros.
    rewrite (eta u). simpl.
    rewrite IHn by lia.
    lra.
Qed.

Lemma vsum_shift : forall n x (u: Vector.t R n),
  vsum (shiftin x u) = vsum u + x
.
Proof.
  induction n; intros x u.
  - rewrite (nil_spec u). simpl. lra.
  - rewrite (eta u).
    simpl. rewrite IHn. lra.
Qed.

Lemma weak_majorized_raw_shiftin : forall n (x y: R) (u v: Vector.t R n),
  weak_majorized_raw (shiftin x u) (shiftin y v)
  -> weak_majorized_raw u v
.
Proof.
  intros n x y u v Hf k.
  destruct (le_dec k n).
  - specialize (Hf k).
    rewrite 2 (prefix_sum_shiftin_leq _ _ _ _ l) in Hf.
    apply Hf.
  - assert (N: forall a b, (a < b -> exists c, b = c + S a)%nat).
    { induction a, b; intros L.
      + exists O. lia.
      + exists (b). lia.
      + lia.
      + assert (E: (a < b)%nat) by lia.
        destruct (IHa _ E). exists x0. lia.
    }
    assert (E: (n < k)%nat) by lia.
    destruct (N _ _ E).
    assert (F2:= Hf n).
    rewrite 2 prefix_sum_shiftin_leq in F2 by lia.
    subst k.
    rewrite <- (Nat.add_succ_comm).
    rewrite 2 (vsum_pref_sum n (S x0)).
    assert (M:= vsum_pref_sum n O).
    simpl in M.
    rewrite 2 M in F2.
    lra.
Qed.

Lemma weak_majorized_raw_rev : forall n (u v: Vector.t R (S n)),
  weak_majorized_raw (rev u) (rev v) ->
  weak_majorized_raw (rev (tl u)) (rev (tl v))
.
Proof.
  intros n u v H k.
  rewrite (eta u), (eta v) in H.
  rewrite 2 rev_cons in H.
  simpl in H.
  apply weak_majorized_raw_shiftin in H.
  apply H.
Qed.

Lemma vsum_rev: forall n (u: Vector.t R n),
  vsum (rev u) = vsum u
.
Proof.
  induction n; intros u.
  - rewrite (nil_spec (rev u)), (nil_spec u). trivial.
  - rewrite (eta u).
    rewrite rev_cons.
    simpl. rewrite vsum_shift. rewrite IHn. lra.
Qed.

Lemma majorized_raw_if_inv_majorized_raw :
  forall n (u v: Vector.t R n),
  weak_majorized_raw (rev u) (rev v) -> inv_weak_majorized_raw u v
.
Proof.
  induction n; intros u v Hw.
  - exact I.
  - simpl. split.
    + specialize (Hw (S n)).
      assert (Hww:= vsum_pref_sum (S n) O).
      simpl plus in Hww.
      rewrite 2 (Hww) in Hw.
      rewrite 2 vsum_rev in Hw. apply Hw.
    + apply IHn.
      apply weak_majorized_raw_rev.
      apply Hw.
Qed.

Lemma inv_majorized_raw_if_majorized_raw :
  forall n (u v: Vector.t R n),
  inv_weak_majorized_raw u v -> weak_majorized_raw (rev u) (rev v).
Proof.


Lemma vsum_singleout : forall n x (u : Vector.t R n),
  vsum (x :: u) - vsum u = x.
Proof. intros. simpl. lra. Qed.

Fixpoint Ksum {n : nat} (f : R -> R) (u v: Vector.t R n) : R .
destruct n.
  - apply 0.
  - apply (f (hd u) - f (hd v) + Ksum n f (tl u) (tl v)).
Defined.

Fixpoint Ksum_delta {n : nat} (f : R -> R) (u v: Vector.t R n) : R .
destruct n.
  - apply 0.
  - apply (secant_slope f (hd u) (hd v) * (hd u - hd v) + Ksum_delta n f (tl u) (tl v)).
Defined.

Fixpoint elem_neq {n : nat} (u v: Vector.t R n) : Prop.
destruct n.
  - apply True.
  - apply (hd u <> hd v /\ elem_neq n (tl u) (tl v)).
Defined.

Lemma Ksum_to_Ksum_delta : forall n f (u v: Vector.t R n),
  Ksum f u v = Ksum_delta f u v.
Proof.
  induction n.
  - trivial.
  - intros f u v.
    simpl. unfold secant_slope.
    destruct (Req_dec (hd u) (hd v)); rewrite IHn.
    + rewrite H. lra.
    + field. lra.
Qed.

Fixpoint KPsum {n : nat} (f : R -> R) (u v: Vector.t R n): R.
destruct n.
  - apply 0.
  - apply (secant_slope f (hd u) (hd v) * (vsum u - vsum v) + KPsum n f (tl u) (tl v)).
Defined.

Fixpoint KPSsum {n : nat} (f : R -> R) (u v: Vector.t R n): R.
destruct n.
  - apply 0.
  - apply (secant_slope f (hd u) (hd v) * (vsum (tl u) - vsum (tl v)) + KPSsum n f (tl u) (tl v)).
Defined.

Lemma Ksum_delta_to_KPsumS : forall n f (u v: Vector.t R n),
  Ksum_delta f u v = KPsum f u v - KPSsum f u v
.
Proof.
  induction n.
  - simpl. intros. lra.
  - intros f u v.
    simpl. rewrite IHn.
    replace (vsum u - vsum v) with (hd u - hd v + vsum (tl u) - vsum (tl v)).
    2:{ rewrite (eta u), (eta v). simpl. lra. }
    lra.
Qed.


Fixpoint KPSsum_deltaS {n : nat} (f: R -> R) (u v: Vector.t R (S n)) {struct n}: R.
destruct n.
  + apply 0.
  + apply ((secant_slope f (hd (tl u)) (hd (tl v)) - secant_slope f (hd u) (hd v)) * (vsum (tl u) - vsum (tl v)) + KPSsum_deltaS (n) f (tl u) (tl v)).
Defined.

Lemma KPSsumS_to_KPSsum_deltaS : forall n f (u v: Vector.t R (S n)),
  KPsum f u v - KPSsum f u v = (secant_slope f (hd u) (hd v)) * (vsum u - vsum v) + KPSsum_deltaS f u v.
Proof.
  induction n; intros f u v.
  - rewrite (eta u), (eta v). rewrite (nil_spec (VectorDef.tl u)), (nil_spec (VectorDef.tl v)). simpl. lra.
  - simpl. field_simplify.
    replace (
      secant_slope f (hd u) (hd v) * vsum u -
      secant_slope f (hd u) (hd v) * vsum v -
      secant_slope f (hd u) (hd v) * vsum (tl u) +
      secant_slope f (hd u) (hd v) * vsum (tl v) +
      secant_slope f (hd (tl u)) (hd (tl v)) * vsum (tl u) -
      secant_slope f (hd (tl u)) (hd (tl v)) * vsum (tl v) +
      KPSsum_deltaS f (tl u) (tl v)
    ) with
    (
      secant_slope f (hd u) (hd v) * vsum u -
      secant_slope f (hd u) (hd v) * vsum v -
      secant_slope f (hd u) (hd v) * vsum (tl u) +
      secant_slope f (hd u) (hd v) * vsum (tl v) +
      (secant_slope f (hd (tl u)) (hd (tl v)) * (vsum (tl u) -
      vsum (tl v)) +
      KPSsum_deltaS f (tl u) (tl v))
    ) by lra.
    rewrite <- IHn. simpl.
    lra.
Qed.

Theorem KPSsum_deltaS_mono : forall n f (u v: Vector.t R (S n)),
  convex f ->
  weak_majorized u v ->
  0 <= KPSsum_deltaS f u v
.
Proof.
  induction n; intros f u v Hconv [Hu [Hv Hmajo]].
  - right. trivial.
  - simpl.
    Search (weak_majorized_raw).
Theorem Karamata_inequality :
  forall n f (u v : Vector.t R n),
  convex f ->
  weak_majorized u v ->
  0 <= Ksum f u v
.
Proof.
  induction n; intros f u v Hconv [Hu [Hv Hmajo]].
  - simpl. lra.
  - rewrite Ksum_to_Ksum_delta.
    rewrite Ksum_delta_to_KPsumS.
    rewrite KPSsumS_to_KPSsum_deltaS.
    

Definition secant (f : R -> R) (x y : R) : R :=
  (f y - f x) / (y - x).

Lemma frac_between_0_1 :
  forall x y z : R,
    x < y < z ->
    0 <= (z - y) / (z - x) <= 1.
Proof.
  intros x y z H.
  destruct H as [Hxy Hyz].
  assert (Hzx : 0 < z - x) by lra.
  split.
  - left. apply Rdiv_lt_0_compat; lra.
  - apply (Rmult_le_reg_l (z - x)); try lra.
    rewrite Rmult_1_r.
    rewrite Rmult_comm.
    rewrite <- Rmult_div_swap.
    rewrite Rmult_div_l; lra.
Qed.

Lemma convex_secant_mono_l_l :
  forall f : R -> R,
    convex f ->
    forall x y z,
      x < y < z ->
      secant f x y <= secant f x z.
Proof.
  intros f Hconv x y z Hxyz.
  destruct Hxyz as [Hxy Hyz].

  set (t := (z - y) / (z - x)).

  assert (Ht : 0 <= t <= 1).
  { apply frac_between_0_1; lra. }

  assert (Hy :
    y = t * x + (1 - t) * z).
  {
    unfold t.
    field.
    lra.
  }

  assert (Hc : f y <= t * f x + (1 - t) * f z).
  {
    rewrite Hy.
    apply Hconv.
    exact Ht.
  }

  assert (Ht' : 1 - t = (y - x) / (z - x)).
  {
    unfold t.
    field.
    lra.
  }

  assert (Hstep :
    f y - f x <= ((y - x) / (z - x)) * (f z - f x)).
  {
    replace (t * f x) with ((1 - (1 - t)) * f x) in Hc by lra.
    rewrite (Rmult_minus_distr_r (f x)) in Hc.
    rewrite Rmult_1_l in Hc.
    rewrite Ht' in Hc.
    unfold t in Hc.
    lra.
  }

  unfold secant.
  apply (Rmult_le_reg_r (y - x)).
  { lra. }

  replace (((f y - f x) / (y - x)) * (y - x)) with (f y - f x).
  2:{
    field.
    lra.
  }

  replace (((f z - f x) / (z - x)) * (y - x))
    with (((y - x) / (z - x)) * (f z - f x)).
  2:{
    field.
    lra.
  }

  exact Hstep.
Qed.

Lemma sub_div_sym_explicit :
  forall a b c d : R,
    (a - b) / (c - d) = (b - a) / (d - c).
Proof.
  intros a b c d.
  unfold Rdiv.
  replace (b - a) with (-(a - b)) by lra.
  replace (d - c) with (-(c - d)) by lra.
  rewrite Rinv_opp.
  ring.
Qed.

Lemma convex_secant_mono_l_m :
  forall f : R -> R,
    convex f ->
    forall x y z,
      y < x < z ->
      secant f x y <= secant f x z.
Proof.
  intros f Hconv x y z [Hyx Hxz].
  unfold secant.

  assert (Hyz : y < z) by lra.

  assert
    (Haux :
      (z - y) * f x <= (z - x) * f y + (x - y) * f z).
  {
    specialize (Hconv y z ((z - x) / (z - y))).
    assert (Ht : 0 <= (z - x) / (z - y) <= 1).
    { apply frac_between_0_1; lra. }
    specialize (Hconv Ht).

    replace
      (((z - x) / (z - y)) * y +
       (1 - (z - x) / (z - y)) * z)
    with x in Hconv.
    2:{ field; lra. }

    replace
      ((z - x) / (z - y) * f y +
       (1 - (z - x) / (z - y)) * f z)
    with
      (((z - x) * f y + (x - y) * f z) / (z - y)) in Hconv.
    2:{ field; lra. }

    apply (Rmult_le_compat_l (z - y)) in Hconv; [|lra].
    field_simplify in Hconv; lra.
  }

  apply (Rmult_le_reg_l ((x - y) * (z - x))).
  { nra. }
  rewrite (sub_div_sym_explicit _ _ y x).
  field_simplify; nra.
Qed.

Lemma convex_secant_mono_l_r :
  forall f : R -> R,
    convex f ->
    forall x y z,
      y < z < x ->
      secant f x y <= secant f x z.
Proof.
  intros f Hconv x y z [Hyz Hzx].
  unfold secant.

  assert (Hyx : y < x) by lra.

  assert
    (Haux :
      (x - y) * f z <= (x - z) * f y + (z - y) * f x).
  {
    specialize (Hconv y x ((x - z) / (x - y))).
    assert (Ht : 0 <= (x - z) / (x - y) <= 1).
    { apply frac_between_0_1; lra. }
    specialize (Hconv Ht).

    replace
      (((x - z) / (x - y)) * y +
       (1 - (x - z) / (x - y)) * x)
    with z in Hconv.
    2:{ field; lra. }

    replace
      ((x - z) / (x - y) * f y +
       (1 - (x - z) / (x - y)) * f x)
    with
      (((x - z) * f y + (z - y) * f x) / (x - y)) in Hconv.
    2:{ field; lra. }

    apply (Rmult_le_compat_l (x - y)) in Hconv; [|lra].
    field_simplify in Hconv; lra.
  }

  apply (Rmult_le_reg_l ((x - y) * (x - z))); [nra|].
  rewrite 2 (sub_div_sym_explicit _ _ _ x).
  field_simplify; nra.
Qed.

Lemma secant_sym :
  forall (f : R -> R) x y,
    secant f x y = secant f y x.
Proof.
  intros f x y.
  unfold secant.
  apply sub_div_sym_explicit.
Qed.

Lemma convex_secant_mono_r_l :
  forall f : R -> R,
    convex f ->
    forall x y z,
      x < y < z ->
      secant f y x <= secant f z x.
Proof.
  intros f Hconv x y z Hxyz.
  rewrite (secant_sym f y x) by lra.
  rewrite (secant_sym f z x) by lra.
  apply convex_secant_mono_l_l; assumption.
Qed.

Lemma convex_secant_mono_r_m :
  forall f : R -> R,
    convex f ->
    forall x y z,
      y < x < z ->
      secant f y x <= secant f z x.
Proof.
  intros f Hconv x y z Hxyz.
  rewrite (secant_sym f y x) by lra.
  rewrite (secant_sym f z x) by lra.
  apply convex_secant_mono_l_m; assumption.
Qed.

Lemma convex_secant_mono_r_r :
  forall f : R -> R,
    convex f ->
    forall x y z,
      y < z < x ->
      secant f y x <= secant f z x.
Proof.
  intros f Hconv x y z Hxyz.
  rewrite (secant_sym f y x) by lra.
  rewrite (secant_sym f z x) by lra.
  apply convex_secant_mono_l_r; assumption.
Qed.

Lemma convex_secant_mono_l :
  forall f : R -> R,
    convex f ->
    forall x y z,
      x <> y ->
      x <> z ->
      y < z ->
      secant f x y <= secant f x z.
Proof.
  intros f Hconv x y z Hxy Hxz Hyz.
  destruct (Rtotal_order x y) as [H1|[H1|H1]];
  destruct (Rtotal_order x z) as [H2|[H2|H2]];
  try lra;
  [
    apply convex_secant_mono_l_l |
    apply convex_secant_mono_l_m |
    apply convex_secant_mono_l_r
  ]; auto; lra.
Qed.

Lemma convex_secant_mono_r :
  forall f : R -> R,
    convex f ->
    forall x y z,
      x <> y ->
      x <> z ->
      y < z ->
      secant f y x <= secant f z x.
Proof.
  intros f Hconv x y z Hxy Hxz Hyz.
  destruct (Rtotal_order x y) as [H1|[H1|H1]];
  destruct (Rtotal_order x z) as [H2|[H2|H2]];
  try lra;
  [
    apply convex_secant_mono_r_l |
    apply convex_secant_mono_r_m |
    apply convex_secant_mono_r_r
  ]; auto; lra.
Qed.

