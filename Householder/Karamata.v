Require Import Reals.
Require Import Lra.
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

Lemma vsum_pref_sum: forall n (u: Vector.t R n),
  prefix_sum n u = vsum u
.
Proof.
  induction n; intros u.
    - rewrite (nil_spec u). trivial.
    - rewrite (eta u). simpl. f_equal. apply IHn.
Qed.

Lemma weak_majorized_raw_rev : forall n (u v: Vector.t R (S n)),
  weak_majorized_raw (rev u) (rev v) ->
  weak_majorized_raw (rev (tl u)) (rev (tl v))
.
Proof.
  intros n u v H k.
  rewrite (eta u), (eta v) in H.
  unfold rev in H.

Lemma majorized_raw_if_inv_majorized_raw :
  forall n (u v: Vector.t R n),
  weak_majorized_raw u v -> inv_weak_majorized_raw (rev u) (rev v)
.
Proof.
  induction n; intros u v Hw.
  - exact I.
  - simpl. split.
    + specialize (Hw (S n)).
      rewrite 2 vsum_pref_sum in Hw.
      apply Hw.
    + apply IHn. 

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
    