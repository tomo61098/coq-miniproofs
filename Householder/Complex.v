Require Import Reals.
Open Scope R_scope.

(* Declare Scope C_scope. *) (* Temporarily removed for 8.9 compatibility *)
Delimit Scope C_scope with C.
Bind Scope C_scope with C.
Open Scope C_scope.
Definition C : Set := R * R.
Definition RtoC (r : R) : C := (r,0).
Coercion RtoC : R >-> C.

Notation i := (0,1).
Notation "0" := (RtoC 0) : C_scope.
Notation "1" := (RtoC 1) : C_scope.

Definition Cplus (c1 c2 : C) : C := (fst c1 + fst c2, snd c1 + snd c2).

Definition Copp (c : C) : C := (- fst c, - snd c).
Definition Cminus (c1 c2 : C) : C := Cplus c1 (Copp c2).

Definition Cmult (c1 c2 : C) : C :=
    (fst c1 * fst c2 - snd c1 * snd c2, fst c1 * snd c2 + snd c1 * fst c2).
Definition Cinv (c : C) : C :=
  (fst c / (fst c ^ 2 + snd c ^ 2), - snd c / (fst c ^ 2 + snd c ^ 2)).
Definition Cdiv (c1 c2 : C) : C := Cmult c1 (Cinv c2).

Definition Cnorm2 (c : C) : R := fst c ^ 2 + snd c ^ 2.
Definition Cnorm (c : C) : R := sqrt (Cnorm2 c).
Arguments Cnorm2 c /.
Arguments Cnorm c /.
Infix "+" := Cplus : C_scope.
Notation "- x" := (Copp x) : C_scope.
Infix "-" := Cminus : C_scope.
Infix "*" := Cmult : C_scope.
Notation "/ x" := (Cinv x) : C_scope.
Infix "/" := Cdiv : C_scope.

Lemma c_proj_eq : forall (c1 c2 : C),
  fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.
Proof. intros. destruct c1, c2. simpl in *. subst. reflexivity. Qed.

Require Import Lra.

Ltac lca := eapply c_proj_eq; simpl; lra.

Lemma C1_neq_C0 : 1 <> 0. Proof. intros F. inversion F. lra. Qed.
Lemma Cplus_comm : forall c1 c2 : C, c1 + c2 = c2 + c1. Proof. intros. lca. Qed.
Lemma Cplus_assoc : forall c1 c2 c3 : C, c1 + c2 + c3 = c1 + (c2 + c3).
Proof. intros. lca. Qed.
Lemma Cplus_opp_r : forall c : C, c + - c = 0. Proof. intros. lca. Qed.
Lemma Cplus_0_l : forall c : C, 0 + c = c. Proof. intros. lca. Qed.
Lemma Cmult_comm : forall c1 c2:C, c1 * c2 = c2 * c1. Proof. intros. lca. Qed.
Lemma Cmult_assoc : forall c1 c2 c3:C, c1 * c2 * c3 = c1 * (c2 * c3).
Proof. intros. lca. Qed.
Lemma Cmult_1_l : forall c:C, 1 * c = c. Proof. intros. lca. Qed.
Lemma Cmult_plus_distr_r : forall c1 c2 c3:C, (c1 + c2) * c3 = c1 * c3 + c2 * c3.
Proof. intros. lca. Qed.
Lemma Cinv_l : forall c:C, c <> 0 -> / c * c = 1.
Proof.
  intros.
  eapply c_proj_eq; simpl; unfold Rminus, Rdiv.
  - repeat rewrite <- Ropp_mult_distr_l.
    rewrite Ropp_involutive.
    repeat rewrite Rmult_1_r.
    rewrite (Rmult_comm (fst c)). rewrite Rmult_assoc.
    rewrite (Rmult_comm (snd c) (/ _)). rewrite Rmult_assoc.
    rewrite <- Rmult_plus_distr_l.
    rewrite Rinv_l; try lra.
    contradict H. apply Rplus_sqr_eq_0 in H. lca.
  - repeat rewrite Rmult_1_r.
    rewrite (Rmult_comm (fst c)). rewrite Rmult_assoc.
    rewrite (Rmult_comm (- snd c)). rewrite Rmult_assoc.
    rewrite <- Rmult_plus_distr_l.
    lra.
Qed.
Lemma C_Field_Theory : @field_theory C 0 1 Cplus Cmult Cminus Copp Cdiv Cinv eq.
Proof.
  constructor. constructor.
  (* addition *)
  (* left identity *) apply Cplus_0_l.
  (* commutativity *) apply Cplus_comm.
  (* associativity *) intros; rewrite Cplus_assoc; easy.
  (* multiplication *)
  (* left identity *) apply Cmult_1_l.
  (* commutativity *) apply Cmult_comm.
  (* associativity *) intros; rewrite Cmult_assoc; easy.
  (* distributivity *) apply Cmult_plus_distr_r.
  (* sub = opp *) reflexivity.
  (* additive inverse *) apply Cplus_opp_r.
  (* 0 <> 1 *) apply C1_neq_C0.
  (* div = inv *) reflexivity.
  (* multiplicative inverse *) apply Cinv_l.
Defined.
Add Field CField : C_Field_Theory.

Lemma Cplus_opp_l : forall c : C, - c + c = 0. Proof. intros. lca. Qed.
Lemma Cplus_0_r : forall c : C, c + 0 = c. Proof. intros. lca. Qed.
Lemma Cmult_0_l : forall c:C, 0 * c = 0. Proof. intros. lca. Qed.
Lemma Cmult_0_r : forall c:C, c * 0 = 0. Proof. intros. lca. Qed.
Lemma Cmult_1_r : forall c:C, c * 1 = c. Proof. intros. lca. Qed.
Lemma Cmult_plus_distr_l : forall c1 c2 c3:C, c1 * (c2 + c3) = c1 * c2 + c1 * c3.
Proof. intros. lca. Qed.
Lemma Cinv_r : forall c:C, c <> 0 -> c * /c = 1.
Proof. intros. rewrite Cmult_comm. apply Cinv_l. easy. Qed.
Lemma Copp_mult_distr_r : forall c1 c2 : C, - (c1 * c2) = c1 * - c2.
Proof. intros; lca. Qed.
Lemma Copp_mult_distr_l : forall c1 c2 : C, - (c1 * c2) = - c1 * c2.
Proof. intros; lca. Qed.
Lemma Copp_involutive: forall c : C, - - c = c. Proof. intros; lca. Qed.
Lemma RtoC_neq : forall (r1 r2 : R), r1 <> r2 -> RtoC r1 <> RtoC r2.
Proof. intros r1 r2 H F. inversion F. easy. Qed.

Definition Cconj (x : C) : C := (fst x, (- snd x)%R).
Notation "a ^*" := (Cconj a) (at level 10) : C_scope.
Lemma Cconj_R : forall r : R, r^* = r. Proof. intros; lca. Qed.
Lemma Cconj_0 : 0^* = 0. Proof. lca. Qed.
Lemma Cconj_opp : forall C, (- C)^* = - (C^*). Proof. reflexivity. Qed.
Lemma Cconj_rad2 : (/ sqrt 2)^* = / sqrt 2. Proof. lca. Qed.
Lemma Cconj_involutive : forall c, (c^*)^* = c. Proof. intros; lca. Qed.
Lemma Cconj_plus_distr : forall (x y : C), (x + y)^* = x^* + y^*. Proof. intros; lca. Qed.
Lemma Cconj_mult_distr : forall (x y : C), (x * y)^* = x^* * y^*. Proof. intros; lca. Qed.

Lemma Conj_mult_norm2 : forall c, c^* * c = Cnorm2 c.
Proof. intros. lca. Qed.

Fixpoint Csum (f: nat -> C) (n: nat): C :=
  match n with
    | O => 0
    | S m => Csum f m + f m
  end.

Require Import Lia.

Lemma Csum_0 : forall (f : nat -> C) (n : nat),
    (forall x, (x < n)%nat -> f x = 0) ->
    Csum f n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite H by lia.
    rewrite IHn. lca.
    intros. apply H; lia.
Qed.

Lemma Csum_eq : forall (f g : nat -> C) (n : nat),
  (forall x, (x < n)%nat -> f x = g x) ->
  Csum f n = Csum g n.
Proof.
  (* WORKED IN CLASS *)
  intros f g n H.
  induction n.
  + simpl. reflexivity.
  + simpl.
    rewrite H by lia.
    rewrite IHn by (intros; apply H; lia).
    reflexivity.
Qed.

Lemma Csum_plus : forall (f g : nat -> C) (n : nat),
    Csum (fun x => f x + g x) n = Csum f n + Csum g n.
Proof.
  intros f g n.
  induction n.
  - simpl. lca.
  - simpl. rewrite IHn. lca.
Qed.

Lemma Csum_mult_l : forall (c : C) (f : nat -> C) (n : nat),
    c * Csum f n = Csum (fun x => c * f x) n.
Proof.
  intros c f n.
  induction n.
  - simpl; lca.
  - simpl.
    rewrite Cmult_plus_distr_l.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Csum_mult_r : forall (c : C) (f : nat -> C) (n : nat),
    Csum f n * c = Csum (fun x => f x * c) n.
Proof.
  intros c f n.
  induction n.
  - simpl; lca.
  - simpl.
    rewrite Cmult_plus_distr_r.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Csum_conj_distr : forall (f : nat -> C) (n : nat),
    (Csum f n) ^* = Csum (fun x => (f x)^*) n.
Proof. intros. induction n.
  - lca.
  - simpl. rewrite <- IHn. lca.
Qed.

(*
Lemma Csum_unique : forall (f : nat -> C) (k : C) (n x : nat),
  (x < n)%nat ->
  f x = k ->
  (forall x', x <> x' -> f x' = 0) ->
  Csum f n = k.
Proof. *)

Lemma pow2_sqrt : forall x:R, 0 <= x -> (sqrt x) ^ 2 = x.
Proof. intros; simpl; rewrite Rmult_1_r, sqrt_def; auto. Qed.
Lemma pow2_sqrt2 : (sqrt 2) ^ 2 = 2.
Proof. apply pow2_sqrt; lra. Qed.
Lemma pown_sqrt : forall (x : R) (n : nat),
  0 <= x -> sqrt x ^ (S (S n)) = (x * sqrt x ^ n)%R.
Proof.
  intros. simpl. rewrite <- Rmult_assoc. rewrite sqrt_sqrt; auto.
Qed.
Lemma sqrt_neq_0_compat : forall r : R, 0 < r -> (sqrt r)%R <> R0.
Proof. intros. specialize (sqrt_lt_R0 r). lra. Qed.
Lemma sqrt_inv : forall (r : R), 0 < r -> sqrt (/ r) = (/ sqrt r)%R.
Proof.
  intros.
  replace (/r)%R with (1/r)%R by lra.
  rewrite sqrt_div_alt, sqrt_1 by lra.
  lra.
Qed.
Lemma sqrt2_inv : sqrt (/ 2) = (/ sqrt 2)%R.
Proof.
  apply sqrt_inv; lra.
Qed.

Lemma Csqrt_inv : forall (r : R), 0 < r -> RtoC (sqrt (/ r)) = (/ sqrt r).
Proof.
  intros r H.
  apply c_proj_eq; simpl.
  field_simplify_eq [(pow2_sqrt r (or_introl H)) (sqrt_inv r H)].
  rewrite Rinv_r. reflexivity.
  apply sqrt_neq_0_compat; lra.
  apply sqrt_neq_0_compat; lra.
  field. apply sqrt_neq_0_compat; lra.
Qed.

Lemma Csqrt2_inv : RtoC (sqrt (/ 2)) = (/ sqrt 2).
Proof. apply Csqrt_inv; lra. Qed.
Lemma Csqrt2_square : sqrt 2 *  sqrt 2 = 2.
Proof.
  eapply c_proj_eq; simpl; try lra.
  rewrite Rmult_0_r, Rminus_0_r.
  apply sqrt_def.
  lra.
Qed.

Ltac nonzero :=
  repeat match goal with
  | |- _ /\ _ => split
  end;
  try match goal with
  | |- (?x <> 0)%C => apply RtoC_neq
  end;
  repeat match goal with
  | |- (sqrt ?x <> 0)%R => apply sqrt_neq_0_compat
  | |- (/?x <> 0)%R => apply Rinv_neq_0_compat
  end;
  match goal with
  | |- (_ <> _)%R => lra
  | |- (_ < _)%R => lra
  end.

Ltac R_field_simplify := repeat field_simplify_eq [pow2_sqrt2 sqrt2_inv];
                         try nonzero.
Ltac R_field := R_field_simplify; reflexivity.
Ltac C_field_simplify := repeat field_simplify_eq [Csqrt2_square Csqrt2_inv];
                         try nonzero.
Ltac C_field := C_field_simplify; reflexivity.

Lemma Csum_extend_r : forall n f, Csum f n + f n = Csum f (S n).
Proof. reflexivity. Qed.
Lemma Csum_extend_l : forall n f, f O + Csum (fun x => f (S x)) n = Csum f (S n).
Proof.
  intros n f.
  induction n.
  + simpl; lca.
  + simpl.
    rewrite <- Cplus_assoc.
    rewrite IHn.
    simpl.
    reflexivity.
Qed.

Lemma Cmult_plus_dist_l (x y z : C) : x * (y + z) = x * y + x * z.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.
Lemma Cmult_plus_dist_r (x y z : C) : (x + y) * z = x * z + y * z.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.

Lemma Csum_sum : forall m n f, Csum f (m + n) =
                          Csum f m + Csum (fun x => f (m + x)%nat) n.
Proof.
  intros m n f.
  induction m.
  + simpl. rewrite Cplus_0_l. reflexivity.
  + simpl.
    rewrite IHm.
    remember (fun y => f (m + y)%nat) as g.
    replace (f m) with (g O) by (subst; rewrite plus_0_r; reflexivity).
    replace (f (m + n)%nat) with (g n) by (subst; reflexivity).
    replace (Csum (fun x : nat => f (S (m + x))) n) with
            (Csum (fun x : nat => g (S x)) n).
    2:{ apply Csum_eq. subst. intros. intros; rewrite <- plus_n_Sm. reflexivity. }
    repeat rewrite Cplus_assoc.
    rewrite Csum_extend_l.
    rewrite Csum_extend_r.
    reflexivity.
Qed.
Lemma Csum_eq_bounded : forall f g n, (forall x, (x < n)%nat -> f x = g x) -> Csum f n = Csum g n.
Proof.
  intros f g n H.
  induction n.
  + simpl. reflexivity.
  + simpl.
    rewrite H by lia.
    rewrite IHn by (intros; apply H; lia).
    reflexivity.
Qed.
Lemma Csum_product : forall m n f g, n <> O ->
                              Csum f m * Csum g n =
                              Csum (fun x => f (x / n)%nat * g (x mod n)%nat) (m * n).
Proof.
  intros.
  induction m.
  + simpl; lca.
  + simpl.
    rewrite Cmult_plus_dist_r.
    rewrite IHm. clear IHm.
    rewrite Csum_mult_l.
    remember ((fun x : nat => f (x / n)%nat * g (x mod n)%nat)) as h.
    replace (Csum (fun x : nat => f m * g x) n) with
            (Csum (fun x : nat => h ((m * n) + x)%nat) n).
    2:{
      subst.
      apply Csum_eq_bounded.
      intros x Hx.
      rewrite Nat.div_add_l by assumption.
      rewrite Nat.div_small; trivial.
      rewrite plus_0_r.
      rewrite Nat.add_mod by assumption.
      rewrite Nat.mod_mul by assumption.
      rewrite plus_0_l.
      repeat rewrite Nat.mod_small; trivial. }
    rewrite <- Csum_sum.
    rewrite plus_comm.
    reflexivity.
Qed.

Theorem Ceq_dec: forall (x y: C), {x = y} + {x <> y}.
Proof. intros.
  destruct (Req_EM_T (fst x) (fst y)), (Req_EM_T (snd x) (snd y)), x, y.
    left. simpl in e, e0. rewrite e, e0. trivial.
    all: right. all: intros A.
    1: apply (f_equal snd) in A.
    2,3: apply (f_equal fst) in A.
    all: auto.
Qed.

Close Scope R.
Close Scope C.
Opaque C.