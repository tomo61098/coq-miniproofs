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

Definition v0 (v : Vector.t R 2) : R :=
  Vector.hd v.

Definition v1 (v : Vector.t R 2) : R :=
  Vector.hd (Vector.tl v).

(* -------- Majorization in dimension 2 -------- *)
(* x = [a; d], y = [b; c], with equal sums and the outer pair wider:
     a <= b <= c <= d,  a + d = b + c
   This is the usual 2-point majorization situation. *)

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

(* Prefix-majorization + equal total sum *)
Definition majorized_raw {n : nat} (v w : Vector.t R n) : Prop :=
  (forall k, prefix_sum k v >= prefix_sum k w) /\
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

(* ---------- A basic 2-point convexity lemma ---------- *)

Lemma convex_two_point_spread :
  forall (f : R -> R) (a b c d : R),
    convex f ->
    a <= b /\ b <= c <= d ->
    a + d = b + c ->
    f a + f d >= f b + f c.
Proof.
  intros f a b c d Hconv Hord Heq.
  destruct Hord as [Hab [Hbc Hcd]].

  destruct (Req_EM_T d a) as [Hdaeq | Hdaeq].
  - assert (a = b /\ b = c /\ c = d) by lra.
    destruct H as [-> [-> ->]].
    lra.
  - assert (Hda : d - a > 0) by lra.
    set (t := (c - a) / (d - a)).

    assert (Ht : 0 <= t <= 1).
    {
      unfold t.
      split.
      - apply Rmult_le_reg_r with (r := d - a).
        + lra.
        + field_simplify.
          lra.
          lra.
      - apply Rmult_le_reg_r with (r := d - a).
        + lra.
        + field_simplify.
          lra.
          lra.
    }

    assert (Htb : 0 <= 1 - t <= 1) by lra.

    assert (Hc : c = t * d + (1 - t) * a).
    {
      unfold t.
      field.
      lra.
    }

    assert (Hb : b = (1 - t) * d + t * a).
    {
      unfold t. rewrite Rmult_minus_distr_r.
      rewrite Rmult_1_l.
      rewrite <- Rplus_minus_swap.
      rewrite <- Rplus_minus_assoc.
      rewrite <- Rmult_minus_distr_l.
      rewrite <- (Ropp_minus_distr'_depr a d).
      rewrite Ropp_mult_distr_r_reverse.
      rewrite <- Rmult_div_swap.
      rewrite Rmult_div_l; lra.
    }

    pose proof (Hconv d a t Ht) as Hcineq.
    pose proof (Hconv d a (1 - t) Htb) as Hbineq.

    rewrite <- Hc in Hcineq.
    replace (1 - (1 - t)) with (t) in Hbineq by lra.
    rewrite <- Hb in Hbineq.

    simpl in Hcineq, Hbineq.
    lra.
Qed.