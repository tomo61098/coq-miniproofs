Add LoadPath "C:\Progis\Coq\Prog\matrix" as Matrix.
Load Complex.

Section StrongInduction.

  Variable P:nat -> Prop.

  (** The stronger inductive hypothesis given in strong induction. The standard
  [nat ] induction principle provides only n = pred m, with [P 0] required
  separately. *)
  Hypothesis IH : forall m, (forall n, n < m -> P n) -> P m.

  Lemma P0 : P 0.
  Proof.
    apply IH; intros.
    exfalso; inversion H.
  Qed.

  Hint Resolve P0.

  Lemma pred_increasing : forall n m,
      n <= m ->
      Nat.pred n <= Nat.pred m.
  Proof.
    induction n; cbn; intros.
    apply le_0_n.
    induction H; subst; cbn; eauto.
    destruct m; eauto.
  Qed.

  Hint Resolve le_S_n.

  (** * Strengthen the induction hypothesis. *)

  Local Lemma strong_induction_all : forall n,
      (forall m, m <= n -> P m).
  Proof.
    induction n; intros;
      match goal with
      | [ H: _ <= _ |- _ ] =>
        inversion H
      end; eauto.
  Qed.

  Theorem strong_induction : forall n, P n.
  Proof.
    eauto using strong_induction_all.
  Qed.

End StrongInduction.

Tactic Notation "strong" "induction" ident(n) := induction n using strong_induction.

Open Scope R_scope.
Open Scope C_scope.

Declare Scope vec_scope.
Delimit Scope vec_scope with Vec.
Open Scope vec_scope.

Require Import Vector.
Import VectorNotations VectorDef.

Theorem eta0 {A}: forall x: t A O, x = [].
Proof. apply case0. auto. Qed.


Lemma hd_app: forall {T n k}
  (A: t T (S n))
  (B: t T k),
  hd (A ++ B) = hd A.
Proof. intros. rewrite (eta A). trivial. Qed.

Lemma tl_app: forall {T n k}
  (A: t T (S n))
  (B: t T k),
  tl (A ++ B) = tl A ++ B.
Proof. intros. rewrite (eta A). simpl. trivial. Qed.

Global Hint Resolve hd_app : vec_scope.
Global Hint Resolve tl_app : vec_scope.

Require Import Lia.

Notation vec := (t C).

(* SPECIAL VEC definitions *)

Fixpoint zerosV {n: nat}: vec n.
destruct n.
  + exact [].
  + apply cons.
    - apply 0%C.
    - apply zerosV.
Defined.

Fixpoint onesV {n: nat}: vec n.
destruct n.
  + exact [].
  + apply cons.
    - apply 1%C.
    - apply onesV.
Defined.

Fixpoint canon_e {n: nat} (m: nat) : vec n :=
  match n with
    | O => []
    | S ns => match m with
                | O => 1 :: @zerosV ns
                | S ms => 0 :: canon_e ms
  end end.

Notation "0" := (zerosV) : vec_scope.
Notation "1" := (onesV) : vec_scope.

(* SPECIAL VEC proofs *)

Lemma canon_e_geq: forall (n x: nat),
  (n <= x)%nat -> @canon_e n x = 0.
Proof.
  induction n; auto.
  intros. simpl.
  destruct x. * inversion H.
  * f_equal. apply IHn. intuition.
Qed.

Lemma canon_e_split: forall {n m k},
  @canon_e (n + m) (n + k) = 0 ++ @canon_e m k.
Proof.
  induction n.
    - intros. trivial.
    - intros.
      simpl. f_equal. apply IHn.
Qed.

Theorem vec_eq_dec: forall {n} (x y: vec n),
  {x = y} + {x <> y}.
Proof.
  induction n.
    - intros. rewrite (eta0 x), (eta0 y). auto.
    - intros.
      destruct (IHn (tl x) (tl y)).
      + destruct (Ceq_dec (hd x) (hd y)).
        * left. rewrite (eta x), (eta y), e, e0. trivial.
        * right. congruence.
      + right. congruence.
Qed.

(* VEC PROP definitions *)

Fixpoint mapvec {n: nat} (f: C -> C) (a: vec n): vec n.
destruct a.
  - apply [].
  - apply cons.
    + apply (f h).
    + apply (mapvec n f a).
Defined.

Definition negvec {n} := @mapvec n (fun x: C => (-x)%C).
Definition multvec {n} (c: C) := @mapvec n (fun x => (c*x)%C).
Definition conjvec {n} := @mapvec n (fun x => Cconj x).

Notation "- x" := (negvec x) : vec_scope.
Infix "*" := (multvec) : vec_scope.
Notation "x ^*" := (conjvec x) : vec_scope.

Fixpoint zipvecs {n: nat} (f: C -> C -> C) (a b: vec n): vec n.
destruct a.
  - apply [].
  - inversion b; subst.
     apply cons.
      + apply f. * apply h. * apply h0.
      + apply zipvecs. * apply f. * apply a. * apply H0.
Defined.

Definition plusvecs {n} := @zipvecs n (fun x y => (x + y)%C).
Definition subvecs {n} := @zipvecs n (fun x y => (x - y)%C).

Infix "+" := (plusvecs) : vec_scope.
Infix "-" := (subvecs) : vec_scope.


(* VEC PROP proof *)

Lemma vec_mult_0: forall {n} (x: vec n),
  0%C * x = 0.
Proof.
  induction x; auto.
  cbn. f_equal. { lca. }
  apply IHx.
Qed.

Lemma vec_mult_neg1: forall {n} (x: vec n),
  (-(1))%C * x = -x.
Proof.
  induction x; auto.
  cbn. f_equal. { lca. } apply IHx.
Qed.

Global Hint Resolve vec_mult_0 : vec_scope.
Global Hint Resolve vec_mult_neg1 : vec_scope.

Lemma vec_plus_step: forall {n} (x y: vec (S n)),
  x + y = (hd x + hd y)%C :: tl x + tl y.
Proof. intros. rewrite (eta x), (eta y). trivial. Qed.

Lemma vec_plus_app_dist: forall {n} (a b: C) (x y: vec n),
  (a + b)%C :: x + y = (a :: x) + (b :: y).
Proof.
  induction n.
    - intros. rewrite (eta0 x), (eta0 y). rewrite (eta0 _). trivial.
    - intros. rewrite 2 vec_plus_step.
      f_equal. rewrite IHn. simpl tl.
      rewrite <-2 eta. trivial.
Qed.

Lemma vec_plus_sub: forall {n} (x y: vec n),
  x + (-y) = x - y.
Proof.
  induction x; auto.
  intros. rewrite (eta y).
  cbn. f_equal. apply IHx.
Qed.

Lemma vec_neg_0: forall {n: nat}, -0 = (0: vec n).
Proof.
  induction n; auto.
  cbn. f_equal. { lca. } apply IHn.
Qed.

Lemma vec_plus_assoc:
  forall {n: nat}, forall (u v w: vec n),
  u + v + w = u + (v + w).
Proof.
  induction u; auto.
  intros. rewrite (eta v), (eta w).
  cbn. f_equal. { lca. } apply IHu.
Qed.

Lemma vec_plus_comm:
  forall {n: nat}, forall (u v: vec n),
  u + v = v + u.
Proof.
  induction u; intros. { auto using (@eta0 C). }
  rewrite (eta v).
  cbn. f_equal. { lca. } apply IHu.
Qed.

Lemma vec_plus_0: forall {n} (x: vec n),
  x + 0 = x.
Proof.
  induction x; auto.
  cbn. f_equal. { lca. } apply IHx.
Qed.

Lemma vec_sub_sub: forall {n} (x: vec n),
  x - x = 0.
Proof.
  induction n; intros; cbn.
    - auto using eta0.
    - rewrite (eta x).
      cbn. f_equal. { lca. } apply IHn.
Qed.

Global Hint Resolve vec_plus_assoc : vec_scope.
Global Hint Resolve vec_plus_comm : vec_scope.
Global Hint Resolve vec_plus_0 : vec_scope.
Global Hint Resolve vec_sub_sub : vec_scope.

Lemma vec_mult_dist: forall {n} (l r: C) (x: vec n),
  (l + r)%C * x = l * x + r * x.
Proof.
  induction x; auto.
  cbn. f_equal. { lca. }
  apply IHx.
Qed.


(* VEC ELEM prop *)

Lemma vec_hd_plus_dist: forall {n}
  (x y: vec (S n)),
  hd (x + y) = (hd x + hd y)%C.
Proof.
  intros. rewrite (eta x), (eta y).
  trivial.
Qed.

Lemma vec_tl_plus_dist: forall {n}
  (x y: vec (S n)),
  tl (x + y) = tl x + tl y.
Proof.
  intros. rewrite (eta x), (eta y).
  trivial.
Qed.

Lemma vec_hd_conj: forall {n} (x: vec (S n)),
  (hd x ^*)%C = hd (x^*).
Proof. intros. rewrite (eta x). trivial. Qed.

Lemma vec_tl_conj: forall {n} (x: vec (S n)),
  (tl x ^*) = tl (x^*).
Proof. intros. rewrite (eta x). trivial. Qed.

Lemma vec_mult_step: forall {n} (a: C) (x: vec (S n)),
  a * x = (a * hd x)%C :: a * tl x.
Proof. intros. rewrite (eta x). trivial. Qed.

Ltac etaeta := rewrite eta0; apply eta0.

Lemma vec_mult_dist_r: forall {n} (a: C) (x y: vec n),
  a * (x + y) = a * x + a * y.
Proof.
  induction n.
    - intros. etaeta.
    - intros.
      rewrite 3 (vec_mult_step).
      rewrite vec_tl_plus_dist.
      rewrite vec_hd_plus_dist. 
      rewrite (IHn).
      rewrite Cmult_plus_distr_l.
      rewrite vec_plus_app_dist. trivial.
Qed.

Lemma vec_conj_0: forall {n},
  (0: vec n) ^* = 0.
Proof.
  induction n; auto.
  cbn. f_equal; auto. lca.
Qed.

Lemma vec_conj_conj: forall {n} (x: vec n),
  x ^* ^* = x.
Proof.
  induction x.
    - trivial.
    - cbn.
      f_equal. + lca.
      + apply IHx.
Qed.

Hint Resolve vec_conj_conj : vec_scope.

Lemma vec_plus_conj_dist: forall {n} (u v: vec n),
  (u + v)^* = u^* + v^*.
Proof.
  induction n; auto.
    - intros. etaeta.
    - intros. rewrite (eta u), (eta v).
      cbn. f_equal. { lca. }
      cbv in IHn. auto.
Qed.

Lemma vec_mult_conj_dist: forall {n} (c: C) (u: vec n),
  (c * u) ^* = (c ^*)%C * (u ^*).
Proof.
  induction u; auto.
  cbn.
  f_equal. { lca. }
  apply IHu.
Qed.

Lemma vec_split_conj: forall {n m} (u: vec n) (v: vec m),
  (u ++ v)^* = u^* ++ v^*.
Proof.
  induction n.
    - intros. rewrite (eta0 u). trivial.
    - intros.
      rewrite (eta u).
      cbn.
      f_equal. apply IHn.
Qed.

Hint Resolve vec_mult_dist : vec_scope.
Hint Resolve vec_conj_0 : vec_scope.

(* DOT definition *)
Fixpoint dot {n} (a b: vec n): C.
destruct a.
  - apply 0%C.
  - inversion b as [|e l c]; subst.
    apply (fun x y => (x + y)%C).
    + apply (h * Cconj e)%C.
    + apply (dot n).
      * apply a.
      * apply c.
Defined.

(* DOT proofs *)

Lemma dot_step: forall {n} (a b: vec (S n)),
  dot a b = (hd a * Cconj (hd b) + dot (tl a) (tl b))%C.
Proof. intros. rewrite (eta a), (eta b) at 1. trivial. Qed.

Lemma dot_comm: forall {n} (u v: vec n),
  dot u v = Cconj (dot v u).
Proof.
  induction v; auto.
    - rewrite (eta0 _). simpl. lca.
    - rewrite (eta u). cbn.
      rewrite IHv.
      lca.
Qed.

Lemma dot_0: forall {n} (u: vec n),
  dot 0 u = 0%C.
Proof.
  induction u; auto.
  cbn. rewrite IHu. lca.
Qed.

Lemma dot_dist: forall {n} (u v z: vec n),
  dot u (v + z) = (dot u v + dot u z)%C.
Proof.
  induction u.
    - intros. simpl. lca.
    - intros.
  rewrite (eta v), (eta z).
  cbn. unfold plusvecs in IHu. rewrite IHu. lca.
Qed.

Lemma dot_dist_l: forall {n} (u v z: vec n),
  dot (u + v) z = (dot u z + dot v z)%C.
Proof.
  intros.
  rewrite dot_comm.
  rewrite dot_dist. rewrite 2 (dot_comm z). lca.
Qed.

Lemma dot_split: forall {n m} (u v: vec n) (x y: vec m),
  dot (u ++ x) (v ++ y) = (dot u v + dot x y)%C.
Proof.
  induction n.
    - intros. rewrite (eta0 u), (eta0 v). lca.
    - intros. rewrite (eta u), (eta v).
      cbn. rewrite IHn. lca.
Qed.

Lemma dot_conj_dist: forall {n} (u v: vec n),
  dot (u^*) (v^*) = (dot u v ^*)%C.
Proof.
  induction n.
    - intros. rewrite (eta0 u). simpl. lca.
    - intros. rewrite (eta v), (eta u).
      cbn. rewrite Cconj_plus_distr. rewrite <- IHn.
  f_equal. lca.
Qed.

Hint Resolve dot_0 : vec_scope.
Hint Resolve dot_comm : vec_scope.
Hint Resolve dot_dist : vec_scope.
Hint Resolve dot_split : vec_scope.

Lemma dot_R: forall {n} (u: vec n),
  snd (dot u u) = 0%R.
Proof.
  induction n.
    - intros. rewrite (eta0 _). trivial.
    - intros. rewrite (eta _). simpl.
      rewrite (IHn (tl u)).
      lra.
Qed.

Lemma dot_geq0: forall {n} (u: vec n),
  0 <= fst (dot u u).
Proof.
  induction u; auto.
    - simpl. lra.
    - cbn. assert (A:= pow2_ge_0 (fst h)).
      assert (B:= pow2_ge_0 (snd h)).
      replace (fst h * fst h - snd h * - snd h)%R
      with (fst h ^ 2 + snd h ^ 2)%R by lra.
      lra.
Qed.

Lemma dot_eq0: forall {n} (u: vec n),
  dot u u = 0%C -> u = 0.
Proof.
  induction u; auto.
  intros.
  rewrite dot_step in H.
  simpl in H.
  assert (A := f_equal fst H).
  simpl in A.
  replace (fst h * fst h - snd h * - snd h)%R
  with (fst h ^ 2 + snd h ^ 2)%R in A by lra.
  assert (B:= pow2_ge_0 (snd h)).
  assert (C:= pow2_ge_0 (fst h)).
  assert (D:= dot_geq0 u).
  assert (fst (dot u u) = 0)%R by lra.
  simpl. rewrite H0 in A.
  rewrite Rplus_0_r in A.
  f_equal.
  + assert (fst h = 0)%R.
    { apply (Rplus_sqr_eq_0_l (fst h) (snd h)).
      cbv. cbv in A. lra. }
    assert (snd h = 0)%R.
    { apply (Rplus_sqr_eq_0_l (snd h) (fst h)).
      cbv. cbv in A. lra. }
    lca.
  + apply IHu. assert (G:=dot_R u). lca.
Qed.

(* MATRIX *)
Declare Scope mat_scope.
Delimit Scope mat_scope with Mat.
Open Scope mat_scope.

(* SPECIAL MAT defs *)

Notation matrix n m := (t (vec m) n).

Fixpoint zerosM {n m: nat}: matrix n m.
destruct n.
  + exact [].
  + apply cons.
    - apply (zerosV).
    - apply zerosM.
Defined.

Fixpoint onesM {n m: nat}: matrix n m.
destruct n.
  + exact [].
  + apply cons.
    - apply 1%Vec.
    - apply onesM.
Defined.

Fixpoint eyeM (x: nat) {n m: nat} := 
  match n with
    | O => []
    | S ns => @canon_e m x :: @eyeM (S x) ns m end.


Fixpoint col {n} (x: vec n) :=
  match x with
    | [] => []
    | u::us => [u] :: col us end.

Fixpoint emptyM {n} : matrix n O :=
  match n with
    | O => []
    | S m => [] :: @emptyM m end.

Notation "0" := (zerosM) : mat_scope.
Notation "1" := (onesM) : mat_scope.
Local Notation I := (eyeM 0).

(* SPECIAL MAT proofs *)

Lemma eye_0: forall {n m x: nat}, (m <= x)%nat -> @eyeM x n m = 0.
Proof.
  induction n; auto.
   intros. simpl.
   f_equal. { apply (canon_e_geq _ _ H). }
   apply IHn. lia.
Qed.

Require Import Logic.Eqdep_dec.

Theorem mat_eq_dec: forall {n m} (A B: matrix n m),
  {A = B} + {A <> B}.
Proof.
  induction n.
    - intros. left. etaeta.
    - intros. rewrite (eta A), (eta B).
      destruct (vec_eq_dec (hd A) (hd B)).
      + destruct (IHn m (tl A) (tl B)).
        * left. rewrite e, e0. auto.
        * right. intros D. inversion D; subst.
          apply inj_pair2_eq_dec in H1; auto using eq_nat_dec.
      + right. congruence.
Qed.

(* MAT PROPS definition *)

Fixpoint mapmat {n m: nat} (f: vec m -> vec m) (M: matrix n m): matrix n m.
destruct M.
  - apply [].
  - apply cons.
    + apply (f h).
    + apply (mapmat n m f M).
Defined.

Definition negmat {n m} := @mapmat n m (fun x: vec m => (-x)%Vec).
Definition multmat {n m} (c: C) := @mapmat n m (fun x: vec m => (c*x)%Vec).
Definition conjmat {n m} := @mapmat n m (fun x: vec m => conjvec x).

Fixpoint multmatvec {n m} (M: matrix n m) (v: vec m) :=
  match M with
    | [] => []
    | u::Ms => dot u (conjvec v) :: multmatvec Ms v end.

Notation "- x" := (negmat x) : mat_scope.
Infix "*" := (multmat) : mat_scope.
Infix "@" := (multmatvec) (at level 40, left associativity) : mat_scope.

Fixpoint zipmat {n m: nat} (f: vec m -> vec m -> vec m) (a b: matrix n m): matrix n m.
destruct a.
  - apply [].
  - inversion b; subst.
     apply cons.
      + apply f. * apply h. * apply h0.
      + apply zipmat. * apply f. * apply a. * apply H0.
Defined.

Definition plusmat {n m} := @zipmat n m (fun x y => (x + y)%Vec).
Definition submat {n m} := @zipmat n m (fun x y => (x - y)%Vec).

Infix "+" := (plusmat) : mat_scope.
Infix "-" := (submat) : mat_scope.

(* MAT PROPS proofs *)

Lemma mat_conj_0: forall {n m},
  conjmat (0: matrix n m) = 0.
Proof.
  induction n; auto.
  cbn. intros. f_equal.
  + apply vec_conj_0.
  + apply IHn.
Qed.

Lemma mat_mult_0: forall {n m} (x: matrix n m),
  0%C * x = 0.
Proof.
  induction x; auto.
  cbn. f_equal. { intuition. }
  apply IHx.
Qed.

Lemma mat_mult_neg1: forall {n m} (x: matrix n m),
  (-(1))%C * x = -x.
Proof. 
  induction x; auto.
  cbn. f_equal. { intuition. } apply IHx.
Qed.

Lemma mat_mult_zeros: forall {n m} (M: matrix n m),
  M @ 0%Vec = 0%Vec.
Proof.
  induction M; auto.
  simpl. rewrite IHM. rewrite vec_conj_0, dot_comm, dot_0.
  f_equal. lca.
Qed.

Lemma mat_vec_dist: forall {n m} (M: matrix n m) (u v: vec m),
  M @ (u + v)%Vec = (M @ u + M @ v)%Vec.
Proof.
  induction M; auto.
  intros. destruct m; auto.
    - cbn. rewrite (eta0 h), (eta0 u), (eta0 v).
      f_equal. { simpl. lca. }
      cbn. specialize (IHM [] []).
           intuition.
    - cbn. f_equal. { rewrite vec_plus_conj_dist. apply dot_dist. }
      rewrite IHM. trivial.
Qed.

Hint Resolve mat_mult_zeros : mat_scope.

Lemma eye_mult_vec: forall {k x m n} (u: vec m) (v: vec n),
  (m <= x)%nat -> @eyeM x k _ @ (u ++ v) = eyeM (x - m) @ v.
Proof.
  induction k; auto.
  intros.
  simpl. f_equal. { revert x m n u v H.
  induction x. * intros. assert (m = O) by lia. destruct u; auto. lia.
  * intros. destruct u; auto.
    cbn. rewrite Cmult_0_l. rewrite Cplus_0_l.
    apply IHx. lia. }
  replace (S (x - m)) with ((S x) - m)%nat by lia.
  apply IHk. lia.
Qed.

Lemma vec_mult_I: forall {n} (x: vec n),
  I @ x = x.
Proof.
  induction x; auto.
  cbn. rewrite dot_0. f_equal. { lca. }
  replace (h :: x) with ([h] ++ x) by auto.
  rewrite (eye_mult_vec [h]) by lia.
  auto.
Qed.

Lemma vec_mult_M0: forall {n m} (x: vec n),
  0 @ x = (0: vec m)%Vec.
Proof.
  intros n m. revert n.
  induction m; auto.
  intros. simpl. f_equal. { intuition. }
  auto.
Qed.

Global Hint Resolve mat_mult_0 : mat_scope.
Global Hint Resolve mat_mult_neg1 : mat_scope.
Global Hint Resolve vec_mult_M0 : mat_scope.
Global Hint Resolve vec_mult_I : mat_scope.

Lemma mat_plus_sub: forall {n m} (x y: matrix n m),
  x + (-y) = x - y.
Proof.
  induction x; auto.
  intros. rewrite (eta y).
  cbn. f_equal. { auto using vec_plus_sub. } apply IHx.
Qed.

Lemma mat_neg_0: forall {n m: nat}, -0 = (0: matrix n m).
Proof.
  induction n; auto.
  cbn. intros. f_equal. { auto using vec_neg_0. } apply IHn.
Qed.

Lemma mat_plus_assoc:
  forall {n m: nat}, forall (u v w: matrix n m),
  u + v + w = u + (v + w).
Proof.
  induction u; auto.
  intros. rewrite (eta v), (eta w).
  cbn. f_equal. { auto using vec_plus_assoc. } apply IHu.
Qed.

Lemma mat_plus_comm:
  forall {n m: nat}, forall (u v: matrix n m),
  u + v = v + u.
Proof.
  induction u; intros. {
  rewrite eta0. auto. }
  rewrite (eta v).
  cbn. f_equal. { auto using vec_plus_comm. } apply IHu.
Qed.

Lemma mat_plus_0: forall {n m} (x: matrix n m),
  x + 0 = x.
Proof.
  induction x; auto.
  cbn. f_equal. { auto using vec_plus_0. } apply IHx.
Qed.

Lemma mat_sub_sub: forall {n m} (x: matrix n m),
  x - x = 0.
Proof.
  induction n; intros; cbn.
    - rewrite (eta0 x). cbn. trivial.
    - rewrite (eta x).
      cbn. f_equal. { auto using vec_sub_sub. } apply IHn.
Qed.

Lemma mat_mat_dist: forall {n m} (N M: matrix n m) (u: vec m),
  (N + M) @ u = (N @ u + M @ u)%Vec.
Proof.
  induction N; auto.
  intros. rewrite (eta M).
  simpl. unfold plusmat in IHN. rewrite IHN.
  rewrite dot_dist_l.
  auto.
Qed.

Global Hint Resolve mat_plus_assoc : mat_scope.
Global Hint Resolve mat_plus_comm : mat_scope.
Global Hint Resolve mat_plus_0 : mat_scope.
Global Hint Resolve mat_sub_sub : mat_scope.


(* MAT COL append *)

Fixpoint hc {n m} (M: matrix n (S m)): vec n.
destruct M.
  - apply [].
  - apply cons. 
    + apply (hd h).
    + eapply hc.
      apply M.
Defined.

Fixpoint tc {n m} (M: matrix n (S m)): matrix n m.
destruct M.
  - apply [].
  - apply cons. 
    + apply (tl h).
    + eapply tc.
      apply M.
Defined.

Fixpoint cc {n m k} (M: matrix n m) (N: matrix n k) : matrix n (m + k).
  destruct n.
    - apply [].
    - apply cons.
      + apply append.
        * apply (hd M).
        * apply (hd N).
      + apply cc.
        * apply (tl M).
        * apply (tl N).
Defined.

Infix "++'" := cc (at level 60, right associativity): mat_scope.

Fact eta0_col: forall {n} (M: matrix n O),
  M = emptyM.
Proof.
  induction M; auto.
  simpl. f_equal; auto using eta0.
Qed.

Fact eta_col: forall {n m} (M: matrix n (S m)),
  M = col (hc M) ++' tc M.
Proof.
  induction M; auto.
  simpl. f_equal; auto.
  apply (eta h).
Qed.

Lemma cc_empty: forall {n m} (M: matrix n m),
  @emptyM n ++' M = M.
Proof.
  induction M; auto.
  simpl. f_equal; auto.
Qed.

Global Hint Resolve cc_empty : mat_scope.

Lemma cc_dist: forall {k n m} (N: matrix k n) (M: matrix k m) (u: vec n) (v: vec m),
  (N ++' M) @ (u ++ v) = ((N @ u) + (M @ v))%Vec.
Proof.
  induction k.
    - intros. etaeta.
    - intros. rewrite (eta N), (eta M).
      simpl. rewrite IHk. cbn. f_equal.
      rewrite vec_split_conj.
      rewrite dot_split. lca.
Qed.

Lemma eye_cc_split: forall {k n m z},
  @eyeM (n + z) k (n + m) = 0 ++' @eyeM z k m.
Proof.
  induction k.
    - intros. trivial.
    - intros. simpl. f_equal.
      + apply canon_e_split.
      + replace (S (n + z)) with (n + S z)%nat by lia.
        apply IHk.
Qed.

(* MATMAT def *)

Fixpoint matmultmat {n k m} (N: matrix n k) (M: matrix k m): matrix n m.
destruct m.
  - apply emptyM.
  - apply (cc (col (N@ hc M))).
    eapply matmultmat.
      + apply N.
      + apply (tc M).
Defined.

Infix "@@" := matmultmat (at level 40, left associativity): mat_scope.

Fixpoint tM {n m} (M: matrix n m) : matrix m n.
destruct m.
  - apply [].
  - apply cons.
    + apply (hc M).
    + apply tM.
      apply (tc M).
Defined.

Notation "x ^*" := (conjmat (tM x)) : mat_scope.

Definition is_Linv_of {n r}
  (A: matrix n r) (B: matrix r n) :=
  A @@ B = I.

Definition is_Rinv_of {n r}
  (A: matrix r n) (B: matrix n r) :=
   B @@ A = I.

Definition sqmatrix (n: nat) := matrix n n.

Definition is_inv_of {n}
  (A: sqmatrix n) (B: sqmatrix n) :=
  is_Linv_of A B /\ is_Rinv_of A B.

Structure inv {n} (A: sqmatrix n):= make_invM {
  invA :> sqmatrix n ;
  inv_AB: is_inv_of invA A ;
}.

Fixpoint trace {n} (A: sqmatrix n): C.
  destruct n.
    - apply 0%C.
    - apply Cplus.
      + apply (hd (hd A)).
      + apply (trace n (tl (tc A))).
Defined.

Inductive is_diag: forall {n}, sqmatrix n -> Prop :=
  | diag_empty: is_diag []
  | S_diag: forall {n} (d: C) (D: sqmatrix n), is_diag D -> is_diag ((d::0%Vec)::(col 0%Vec ++' D)).

Fixpoint diag {n} (d: vec n): sqmatrix n.
  destruct n.
    - apply [].
    - apply cons.
      + apply (hd d :: 0%Vec).
      + apply (@cc n (S 0) n).
        * apply (col 0%Vec).
        * apply diag.
          apply (tl d).
Defined.

Inductive is_upTri: forall {n m}, matrix n m -> Prop :=
  | upTri: forall {n m}, is_upTri (0: matrix n m)
  | S_upTri: forall {n m} (x: vec (S m)) (T: matrix n m), is_upTri T -> is_upTri (x :: (col 0%Vec ++' T)).

Definition is_lowTri {n m} X := @is_upTri n m (tM X).

Definition Runitary {n m} (A: matrix n m) :=
  A @@ A^* = I.

Definition Lunitary {n m} (A: matrix n m) :=
  A^* @@ A = I.

Definition unitary {n} (A: sqmatrix n) :=
  Runitary A /\ Lunitary A.

Definition hermit {n} (A: sqmatrix n) :=
  A^* = A.

Definition antihermit {n} (A: sqmatrix n) :=
  A^* = -A.

(* MATMAT proofs *)

Lemma mat_mult_emptyl: forall {n m} (A: matrix n m),
  [] @@ A = [].
Proof.
  induction A.
    - destruct m; auto.
    - destruct m; auto.
Qed.

Lemma mat_mult_vec_empty: forall {n} (A: matrix n O),
  A @ [] = 0%Vec.
Proof.
  induction n.
    - intros. rewrite (eta0_col A). trivial.
    - intros. rewrite (eta0_col A). simpl. rewrite IHn. trivial.
Qed.

Global Hint Resolve mat_mult_vec_empty : mat_scope.

Lemma mat_mult_I: forall {n m} (M: matrix n m),
  I @@ M = M.
Proof.
  induction m; auto.
    - intros. simpl. induction M; auto. simpl. f_equal; auto. symmetry. apply eta0.
    - intros.
      cbn. rewrite IHm. rewrite vec_mult_I.
      symmetry. apply eta_col.
Qed.

Global Hint Resolve mat_mult_I : mat_scope.

Lemma mat_tail_col_commute: forall {m n}
  (A: matrix (S n) m) (x: vec m),
  tl (col (A @ x)) = col (tl A @ x).
Proof.
  induction m.
    - intros. rewrite (eta0_col _). trivial.
    - intros. rewrite (eta x), (eta_col A).
      simpl. f_equal.
Qed.

Lemma mat_tail_mult_commute: forall {m n r}
  (B: matrix (S n) r) (A: matrix r m),
    tl (B @@ A) = tl B @@ A.
Proof.
  induction m; auto.
  intros. simpl. rewrite IHm.
  rewrite mat_tail_col_commute.
  trivial.
Qed.

Lemma mat_head_mult_commute: forall {m n r}
  (B: matrix (S n) r) (A: matrix r m),
  hd (B @@ A) = tM A @ hd B.
Proof.
  induction m; auto.
  intros. simpl. rewrite IHm.
  rewrite (eta B) at 1. simpl. rewrite dot_comm, <- dot_conj_dist.
  rewrite vec_conj_conj. trivial.
Qed.

Lemma mat_tl_tc_commute: forall {n m}
  (M: matrix (S n) (S m)),
    tl (tc M) = tc (tl M).
Proof.
  intros.
  rewrite (eta_col _). trivial.
Qed.

Global Hint Resolve mat_tl_tc_commute : mat_scope.

Lemma mat_tm_tc_commute: forall {m n}
  (M: matrix (S n) m),
    tc (tM M) = tM (tl M).
Proof.
  induction m; auto.
  intros. simpl. rewrite IHm.
  rewrite (eta_col M). trivial.
Qed.

Lemma mat_tm_tl_commute: forall {n m}
  (M: matrix n (S m)),
    tl (tM M) = tM (tc M).
Proof. intros. trivial. Qed.

Lemma mat_hd_hc_hd_eq: forall {n m}
  (M: matrix (S n) (S m)),
  hd (hc M) = hd (hd M).
Proof. intros. rewrite (eta M) at 1. trivial. Qed.

Lemma mat_hc_hd_commute: forall {m n}
  (M: matrix (S n) m),
    hc (tM M) = hd M.
Proof.
  induction m.
    - intros. rewrite (eta0_col M). trivial.
    - intros. simpl. rewrite IHm.
      rewrite (eta M) at 2. simpl.
      rewrite (mat_hd_hc_hd_eq).
      rewrite eta. trivial.
Qed.

Lemma mat_hd_col_hd: forall {n m}
  (M: matrix (S n) (S m)),
  hd (col (hd M)) = [hd (hd M)].
Proof.
  intros.
  rewrite (eta (hd M)). simpl. trivial.
Qed.

Lemma mat_hd_conj: forall {n m} (M: matrix (S n) m),
  hd (conjmat M) = ((hd M)^*)%Vec.
Proof. intros. rewrite (eta M). trivial. Qed.

Lemma mat_tl_conj: forall {n m} (M: matrix (S n) m),
  conjmat (tl M) = tl (conjmat M).
Proof. intros. rewrite (eta M). trivial. Qed.

Lemma tm_dist: forall {m n}
  (M: matrix (S n) m),
  tM M = col (hd M) ++' tM (tl M).
Proof.
  induction m; auto.
  intros. simpl.
  rewrite (IHm). f_equal; auto.
    - rewrite (eta (hd M)). simpl.
      rewrite (eta M) at 1.
      trivial.
    - rewrite mat_tl_tc_commute.
      f_equal. rewrite (eta (hd M)). simpl.
      f_equal. rewrite (eta M). trivial.
Qed.

Lemma mat_tm_tm: forall {n m} (M: matrix n m), tM (tM M) = M.
Proof.
  induction n; auto.
    - intros. rewrite eta0. trivial.
    - destruct m.
      -- intros. rewrite (eta0_col M). simpl.
      f_equal. trivial. rewrite (eta0_col _). trivial.
      -- intros.
      rewrite (eta M) at 2. simpl.
      f_equal.
      + rewrite mat_hc_hd_commute.
        rewrite (eta M). simpl.
        rewrite <- (eta _). trivial.
      + rewrite tm_dist. simpl.
  rewrite mat_tm_tc_commute.
  rewrite IHn.
  rewrite (eta M). simpl.
  rewrite eta_col. trivial.
Qed.

Theorem tm_bijection: forall {n m}
  (N M: matrix n m),
  tM N = tM M -> N = M.
Proof. intros. apply (f_equal tM) in H.
  rewrite 2 mat_tm_tm in H. apply H.
Qed.

Global Hint Resolve mat_tm_tm : mat_scope.

Lemma mat_tm_mult_vec: forall {n m}
  (A: matrix n (S m)) (x: vec n),
  tM A @ x = dot (hc A) (x^*)%Vec :: tM (tc A) @ x.
Proof. auto. Qed.

Lemma mat_mult_col: forall {n m}
  (A: matrix n (S m)) (x: vec (S m)),
  A @ x = (hd x * hc A + tc A @ tl x)%Vec.
Proof.
  induction n.
    - intros. rewrite (eta0), (eta0 _). trivial.
    - intros. rewrite (eta A) at 1.
      simpl (_ @ _) at 1. rewrite IHn.
      rewrite (eta A) at 4 5.
      simpl hc. simpl tc.
      simpl (_ @ _) at 2.
      rewrite (dot_step (hd A) (x^*)%Vec).
      rewrite (vec_plus_app_dist).
      f_equal. + cbn. f_equal.
      rewrite vec_hd_conj.
      rewrite vec_conj_conj.
      lca.
      + rewrite vec_tl_conj. trivial.
Qed.

Lemma mat_hd_dot_commute: forall {m n}
  (A: matrix (S n) m) (x: vec m),
  hd (A @ x) = dot (hd A) (x^*)%Vec.
Proof. intros. rewrite (eta A). trivial. Qed.

Lemma dot_mult_commute: forall {n} (a: C)
  (x y: vec n),
  (a * dot x y)%C = dot (a * x)%Vec y.
Proof.
  induction n.
    - intros. rewrite (eta0 _). simpl. lca.
    - intros. rewrite 2 dot_step.
      rewrite vec_mult_step. simpl hd.
      simpl tl.
      rewrite <- IHn. lca.
Qed.

Lemma hc_col: forall {n m}
  (x: vec n) (A: matrix n m),
  hc (col x ++' A) = x.
Proof.
  induction n.
    - intros. simpl. symmetry. apply eta0.
    - intros. simpl. rewrite (eta x) at 3.
      f_equal.
      + rewrite (eta x). trivial.
      + rewrite (eta x). simpl.
        apply IHn.
Qed.

Lemma mat_conj_hc: forall {n m} (A: matrix n (S m)),
  conjvec (hc A) = hc (conjmat A).
Proof. induction n.
  - intros. rewrite eta0. apply eta0.
  - intros. rewrite (eta A). simpl.
    cbn. f_equal.
      + apply (vec_hd_conj).
      + apply IHn.
Qed.

Lemma mat_conj_tc: forall {n m} (A: matrix n (S m)),
  conjmat (tc A) = tc (conjmat A).
Proof. induction n.
  - intros. rewrite eta0. apply eta0.
  - intros. rewrite (eta A). simpl.
    cbn. f_equal.
      + apply (vec_tl_conj).
      + apply IHn.
Qed.

Lemma mat_hc_herm: forall {n m} (A: matrix (S n) (m)),
  hc (A^*) = (hd A)^*%Vec.
Proof.
  intros. rewrite <- mat_conj_hc.
  rewrite mat_hc_hd_commute. trivial.
Qed.

Lemma mat_tc_herm: forall {n m} (A: matrix (S n) (m)),
  tc (A^*) = (tl A)^*.
Proof.
  intros. rewrite <- mat_conj_tc.
  rewrite mat_tm_tc_commute.
  trivial.
Qed.

Lemma mat_dot_comm: forall {n m}
  (A: matrix n m) (x: vec n) (y: vec m),
  dot x (A @ y) = dot (A^* @ x) y.
Proof.
  induction n.
    - intros. rewrite (eta0 _). rewrite (eta0_col _).
      rewrite mat_mult_vec_empty. rewrite dot_0. trivial.
    - destruct m; intros.
      { rewrite (eta0_col _).
        rewrite (eta0 _). rewrite mat_mult_vec_empty.
        rewrite (dot_comm). rewrite dot_0. lca.
      }
  rewrite (mat_mult_col (A ^*) _).
  
  rewrite mat_tc_herm.
  rewrite dot_dist_l.
  rewrite <- IHn.
  rewrite <- dot_mult_commute.
  rewrite dot_step at 1. f_equal.
    + f_equal. rewrite mat_hc_herm.
      rewrite mat_hd_dot_commute.
      rewrite <- dot_conj_dist.
      rewrite vec_conj_conj. trivial.
    + rewrite (eta A). trivial.
Qed.

Lemma mat_mult_mat_step: forall {n r m}
  (B: matrix n r) (A: matrix r (S m)),
    B @@ A = col (B @ hc A) ++' B @@ tc A.
Proof. intros. trivial. Qed.

Lemma mat_mult_mat_row_step: forall {m r n}
  (B: matrix (S n) r) (A: matrix r m),
  B @@ A = tM A @ hd B :: tl B @@ A.
Proof.
  induction m.
    - intros. simpl. trivial.
    - intros. simpl. rewrite IHm.
      simpl. f_equal.
      + rewrite dot_comm.
        rewrite <- dot_conj_dist.
        rewrite vec_conj_conj.
        rewrite <- mat_hd_dot_commute.
        rewrite (eta (B @ hc A)). simpl. trivial.
      + rewrite mat_tail_col_commute. trivial.
Qed.

Lemma mat_mult_vec_O:
  forall {n} (A: matrix n O) (x: vec O),
  A @ x = 0%Vec.
Proof.
  intros. rewrite (eta0_col _).
  rewrite (eta0 _). apply mat_mult_vec_empty.
Qed.

Global Hint Resolve mat_mult_vec_O : mat_scope.

Theorem mat_mult_mat_MAGIC:
  forall {n m} (B: matrix n O) (A: matrix O m),
  B @@ A = 0.
Proof.
  induction n.
    - intros. rewrite (eta0 _). trivial.
    - intros.
      rewrite (mat_mult_mat_row_step B A).
      rewrite (IHn).
      rewrite mat_mult_vec_O.
      trivial.
Qed.

Global Hint Resolve mat_mult_mat_MAGIC : mat_scope.

Lemma mat_mult_vec_conj: forall {n m} (A: matrix n m) (x: vec m),
  ((A @ x) ^* = (conjmat A) @ x^*)%Vec.
Proof.
  induction m.
    - intros. rewrite 2 mat_mult_vec_O. apply vec_conj_0.
    - intros. rewrite mat_mult_col.
      rewrite vec_plus_conj_dist.
      rewrite IHm.
      rewrite (eta x) at 3.
      cbn. rewrite mat_mult_col.
      f_equal. + cbn. rewrite vec_mult_conj_dist.
      f_equal. apply mat_conj_hc.
      + rewrite mat_conj_tc. trivial.
Qed.

Lemma cc_0: forall {n m} (A: matrix n O)
  (M: matrix n m),
  A ++' M = M.
Proof. intros. rewrite (eta0_col A). apply cc_empty. Qed.

Lemma mat_conj_split_col: forall {n m k}
  (A: matrix n m) (B: matrix n k),
  conjmat (A ++' B) = conjmat A ++' conjmat B.
Proof.
  induction n.
    - intros. rewrite eta0. apply eta0.
    - intros. simpl.
      cbn. f_equal.
      + rewrite vec_split_conj. rewrite 2 mat_hd_conj.
        trivial.
      + rewrite <- 2 mat_tl_conj. rewrite <- IHn. trivial.
Qed.

Lemma col_conj: forall {n} (x: vec n),
  col (x ^*)%Vec = conjmat (col x).
Proof.
  induction n.
    - intros. rewrite eta0. apply eta0.
    - intros. rewrite (eta x).
      simpl. cbn. f_equal.
      apply IHn.
Qed.

Lemma mat_tm_conj: forall {n m} (A: matrix n m),
  tM (conjmat A) = conjmat (tM A).
Proof.
  induction n.
    - intros. rewrite (eta0_col). apply eta0_col.
    - intros. rewrite (eta A).
      rewrite 2 tm_dist. simpl.
      rewrite (mat_conj_split_col (col _)).
      f_equal.
      + apply col_conj.
      + apply IHn.
Qed.

Lemma mat_conj_conj: forall {n m} (A: matrix n m),
  conjmat (conjmat A) = A.
Proof.
  induction n.
    - intros. rewrite eta0. apply eta0.
    - intros. rewrite (eta A). cbn.
      f_equal. + apply vec_conj_conj.
      + apply IHn.
Qed.

Lemma mat_mult_mat_vec_assoc:
  forall {n r m} (B: matrix n r) (A: matrix r m)
  (x: vec m),
    (B @@ A) @ x = B @ (A @ x).
Proof.
  induction n.
    - intros. rewrite (eta0), (eta0 _). trivial.
    - intros.
      destruct m.
        -- rewrite (eta0_col _).
           rewrite (eta0 _).
           rewrite (eta0_col A).
           rewrite 2 mat_mult_vec_empty.
           rewrite mat_mult_zeros. trivial.
        --
    rewrite (eta B) at 2.
    simpl (_ @ _) at 2.
    rewrite <- IHn.
    rewrite mat_mult_mat_row_step.
    replace ((tM A @ hd B :: tl B @@ A) @ x) with
    ( dot (tM A @ hd B) (x^*)%Vec :: (tl B @@ A) @ x).
    { f_equal. rewrite mat_mult_vec_conj.
      rewrite mat_dot_comm.
      rewrite <- mat_tm_conj.
      rewrite mat_conj_conj.
      auto.
    } trivial.
Qed.

Lemma mat_scalar_comm: forall {n m}
  (a: C) (x: vec m) (A: matrix n m),
  A @ (a * x)%Vec = (a * A) @ x.
Proof.
  induction n.
    - intros. rewrite (eta0 A). trivial.
    - intros. rewrite (eta A).
      simpl.  rewrite vec_mult_conj_dist.
      rewrite (dot_comm (hd A) (_))%Vec.
      rewrite <- 2 (dot_mult_commute).
      rewrite (dot_comm). f_equal.
      + rewrite Cconj_mult_distr.
        rewrite 2 Cconj_involutive. trivial.
      +
      rewrite (IHn).
      auto.
Qed.

Lemma vec_tl_col_commute: forall {n}
  (x: vec (S n)),
  tl (col x) = col (tl x).
Proof. intros. rewrite (eta x). simpl. trivial. Qed.

Global Hint Resolve hc_col : mat_scope.

Lemma tc_col: forall {n m}
  (x: vec n) (A: matrix n m),
  tc (col x ++' A) = A.
Proof.
  induction n.
    - intros. rewrite (eta0). trivial.
    - intros. rewrite (eta A).
      simpl tc. f_equal.
      + rewrite (eta x). trivial.
      + rewrite (eta x). simpl.
        apply IHn.
Qed.

Global Hint Resolve tc_col : mat_scope.

Ltac inj H := repeat (
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in H).

Fact diag_step: forall {n} (A: sqmatrix (S n)),
  is_diag A -> A = ((hd(hd A))::0%Vec) :: (col 0%Vec ++' (tl (tc A))).
Proof.
  intros.
  inversion H; subst.
  inj H1.
  rewrite (eta A) at 1.
  rewrite (eta_col _) at 1.
  simpl.
  rewrite (eta A) in H1.
  rewrite (eta_col (hd A :: _)) in H1.
  simpl in H1.
  inversion H1; subst.
  inj H4. inj H5.
  apply (f_equal hc) in H5.
  rewrite 2 hc_col in H5.
  rewrite <- H4, H5. rewrite mat_tl_tc_commute. trivial.
Qed.

Fact diag_step_diag: forall {n} (A: sqmatrix (S n)),
  is_diag A -> is_diag (tl (tc A)).
Proof.
  intros.
  inversion H; subst.
    inj H1.
    rewrite (eta A) in H1.
    rewrite (eta_col (hd A :: _)) in H1.
    inversion H1; subst.
    inj H4. inj H5.
    apply (f_equal tc) in H5.
    rewrite 2 tc_col in H5.
    simpl.
    rewrite (mat_tl_tc_commute).
    rewrite <- H5. apply H2.
Qed.

Lemma mat_mult_mat_mat_assoc:
  forall {k n r m}
  (A: matrix n r) (B: matrix r m)
 (C: matrix m k),
    A @@ B @@ C = A @@ (B @@ C).
Proof.
  induction k.
    - intros. rewrite (eta0_col _). trivial.
    - intros.
      rewrite 2 (mat_mult_mat_step _ C0).
      rewrite IHk.
      destruct n; auto.
      rewrite (mat_mult_mat_step A (col (B @ hc C0) ++' B @@ tc C0)).
      f_equal.
      + rewrite hc_col.
        rewrite (mat_mult_mat_vec_assoc).
        trivial.
      + rewrite tc_col. trivial.
Qed.

Theorem mat_mult_tm_dist: forall {n r m}
  (A: matrix n r) (B: matrix r m),
    tM (A @@ B) = tM B @@ tM A.
Proof.
  induction n.
    - intros. rewrite (eta0 A).
      rewrite (eta0 ([] @@ B)).
      induction m; auto.
      simpl. f_equal. apply (IHm (tc B)).
    - intros.
      rewrite tm_dist.
      rewrite mat_tail_mult_commute.
      rewrite IHn.
      simpl. rewrite mat_tm_tc_commute. f_equal.
      f_equal.
      rewrite mat_hc_hd_commute.
      apply mat_head_mult_commute.
Qed.

Lemma mat_tm_I: forall {n},
  @tM n n I = I.
Proof.
  intros.
  assert(A := @mat_mult_tm_dist n n n I (tM I)).
  rewrite (mat_mult_I) in A.
  rewrite mat_tm_tm in A.
  rewrite (mat_mult_I) in A.
  auto.
Qed.

Global Hint Resolve mat_tm_I : mat_scope.

Lemma mat_mult_I_r: forall {n m} (A: matrix n m),
  A @@ I = A.
Proof.
  intros.
  assert (D := @mat_mult_tm_dist m m n I (tM A)).
  rewrite (mat_tm_I) in D.
  rewrite mat_mult_I in D.
  rewrite (mat_tm_tm) in D.
  auto.
Qed.

Global Hint Resolve mat_mult_I_r : mat_scope.

Lemma mat_inv_eq: forall {n} (A L R: sqmatrix n),
  L @@ A = I -> A @@ R = I -> L = R.
Proof.
  intros.
  rewrite <- (mat_mult_I_r L).
  rewrite <- H0.
  rewrite <- mat_mult_mat_mat_assoc.
  rewrite H.
  apply mat_mult_I.
Qed.

Lemma mat_diag_vec: forall {n} (x: vec n),
  is_diag (diag x).
Proof.
  induction n.
    - intros. constructor.
    - intros. simpl. apply S_diag. apply IHn.
Qed.

Lemma mat_diag_exist: forall {n} (D: sqmatrix n),
  is_diag D <-> exists x, D = diag x.
Proof.
  induction n.
    - intros. split.
      + intros. exists []. rewrite (eta0 _). trivial.
      + intros [x A]. rewrite (eta0 _). constructor.
    - intros. split.
      + intros.
        assert (B := diag_step_diag D H).
        destruct (IHn (tl (tc D))) as [X _].
        specialize (X B).
        destruct X.
        exists (hd (hd D) :: x).
        simpl. rewrite <- H0.
        apply diag_step. trivial.
      + intros [x H].
        simpl in H.
    rewrite H.
    apply S_diag.
    apply IHn.
    exists (tl x).
    trivial.
Qed.

Lemma mat_hc_app_dist: forall {m n k}
  (A: matrix n (S m)) (B: matrix k (S m)),
  hc (A ++ B) = hc A ++ hc B.
Proof.
  induction n.
    - intros. rewrite (eta0 _). trivial.
    - intros. rewrite (eta A). simpl.
      f_equal. apply IHn.
Qed.

Lemma mat_tc_app_dist: forall {m n k}
  (A: matrix n (S m)) (B: matrix k (S m)),
  tc (A ++ B) = tc A ++ tc B.
Proof.
  induction n.
    - intros. rewrite (eta0 _). trivial.
    - intros. rewrite (eta A). simpl.
      f_equal. apply IHn.
Qed.

Lemma mat_tm_app_dist: forall {m n k}
  (A: matrix n m) (B: matrix k m),
  tM (A ++ B) = tM A ++' tM B.
Proof.
  induction m.
    - intros. trivial.
    - intros.
      simpl. rewrite mat_hc_app_dist. f_equal.
      rewrite mat_tc_app_dist.
      apply IHm.
Qed.

Theorem mat_mult_app_dist: forall {n m r k}
  (A: matrix n m) (C: matrix m k)
  (B: matrix n r) (D: matrix r k),
  (A ++' B) @@ (C ++ D) = A @@ C + B @@ D.
Proof.
  induction n.
    - intros. rewrite (eta0), (eta0 _). trivial.
    - intros.
      rewrite 3 mat_mult_mat_row_step.
      rewrite mat_tm_app_dist.
      simpl. cbn. rewrite cc_dist. f_equal.
      rewrite IHn.
      trivial.
Qed.

Lemma mat_app_cc_dist: forall {n m k r}
  (A: matrix n m) (B: matrix r m)
  (C: matrix n k) (D: matrix r k),
  (A ++ B) ++' (C ++ D) = (A ++' C) ++ (B ++' D).
Proof.
  induction n.
    - intros. rewrite (eta0 A), (eta0 C0). trivial.
    - intros.
      simpl. rewrite 2 hd_app.
      f_equal.
      rewrite 2 tl_app.
      apply IHn.
Qed.

Lemma mat_tm_app_col_dist: forall {n m k}
  (A: matrix m n) (B: matrix k n),
  tM (A ++ B) = tM A ++' tM B.
Proof.
  intros. rewrite <- mat_tm_tm.
  rewrite mat_tm_app_dist.
  intuition.
Qed.

Lemma mat_app_0: forall {m n k},
  (0: matrix n m) ++ (0: matrix k m) = 0.
Proof.
  induction n.
    - intros. trivial.
    - intros. simpl. f_equal. apply IHn.
Qed.

Global Hint Resolve mat_app_0 : mat_scope.

Lemma mat_hc_cc: forall {n m k}
  (A: matrix n (S m)) (B: matrix n k),
  hc (A ++' B) = hc A.
Proof.
  induction n.
    - intros. rewrite eta0. trivial.
    - intros. simpl.
  rewrite (eta A) at 3.
  simpl. f_equal; auto.
  apply hd_app.
Qed.

Lemma mat_hd_tc_commute: forall {n m}
  (A: matrix (S n) (S m)),
  hd (tc A) = tl (hd A).
Proof. intros.
  rewrite (eta_col _). trivial.
Qed.

Lemma mat_tc_cc: forall {n m k}
  (A: matrix n (S m)) (B: matrix n k),
  tc (A ++' B) = tc A ++' B.
Proof.
  induction n.
    - intros. rewrite eta0. trivial.
    - intros. simpl.
  rewrite tl_app.
  rewrite mat_hd_tc_commute.
  f_equal.
  rewrite IHn.
  rewrite mat_tl_tc_commute.
  trivial.
Qed.

Lemma mat_hc_0: forall {n m},
  hc (0: matrix n (S m)) = 0%Vec.
Proof.
  induction n.
    - auto.
    - intros. simpl. f_equal. auto.
Qed.

Global Hint Resolve mat_hc_0 : mat_scope.

Lemma mat_tc_0: forall {n m},
  tc (0: matrix n (S m)) = 0.
Proof.
  induction n.
    - auto.
    - intros. simpl. f_equal. auto.
Qed.

Global Hint Resolve mat_tc_0 : mat_scope.

Lemma mat_cc_0: forall {m n k},
  (0: matrix n m) ++' (0: matrix n k) = (0: matrix n (m + k)).
Proof.
  induction m.
    - intros. rewrite (eta0_col _). apply cc_empty.
    - intros. rewrite (eta_col _).
      rewrite (eta_col).
      rewrite mat_tc_cc.
      rewrite mat_hc_cc.
      rewrite mat_hc_0.
      rewrite mat_tc_0.
      f_equal.
        + f_equal.
          destruct n; auto.
          simpl.
          rewrite mat_hc_0. trivial.
        + destruct n; auto.
          simpl.
          rewrite mat_tc_0. apply IHm.
Qed.

Lemma mat_tm_cc_dist: forall {n m k}
  (A: matrix m n) (B: matrix m k),
  tM (A ++' B) = tM A ++ tM B.
Proof.
  induction n.
    - intros. rewrite (eta0_col _).
      rewrite cc_empty.
      trivial.
    - intros.
      simpl.
      f_equal.
      { apply mat_hc_cc. }
      rewrite mat_tc_cc.
      apply IHn.
Qed.

Lemma mat_vec_app_dist: forall {n m k}
  (A: matrix n m) (B: matrix k m) (x: vec m),
  (A ++ B) @ x = A @ x ++ B @ x.
Proof.
  induction n.
    - intros. rewrite (eta0 _). trivial.
    - intros.
      rewrite (eta A).
      simpl.
      rewrite IHn. trivial.
Qed.

Theorem mat_mult_app_col_dist: forall {n r m k L}
  (A: matrix n m) (C: matrix m k)
  (B: matrix r m) (D: matrix m L),
  (A ++ B) @@ (C ++' D) =
  (A @@ C ++' A @@ D) ++ (B @@ C ++' B @@ D).
Proof.
  induction n.
    - induction r.
      + intros. simpl. apply (eta0 _).
      + intros.
        simpl.
        rewrite 2 mat_tail_mult_commute.
        rewrite 2 mat_head_mult_commute.
        rewrite (eta0 _).
        simpl. rewrite mat_mult_mat_row_step.
        f_equal.
      * rewrite mat_tm_cc_dist.
        apply mat_vec_app_dist.
      * specialize (IHr m k L [] C0 (tl B) D).
        simpl in IHr.
        apply IHr.
    - intros.
      simpl.
      rewrite ! mat_head_mult_commute.
      rewrite ! mat_tail_mult_commute.
      simpl. rewrite <- IHn.
      rewrite mat_mult_mat_row_step.
      simpl. f_equal.
       +
      rewrite mat_tm_cc_dist.
      rewrite hd_app.
      apply mat_vec_app_dist.
       +
      rewrite tl_app. trivial.
Qed.

Lemma mat_hc_I: forall {n},
  hc (I: matrix (S n) (S n)) = 1%C::0%Vec.
Proof.
  intros.
  rewrite <- mat_tm_I.
  rewrite mat_hc_hd_commute.
  trivial.
Qed.

Lemma vec_hc_col: forall {n} (x: vec n),
  hc (col x) = x.
Proof.
  induction n.
    - intros. rewrite (eta0 _), (eta0). trivial.
    - intros. rewrite (eta x). simpl. f_equal. apply IHn.
Qed.

Lemma vec_0_mult: forall {n}
  (x: C),
  (x * 0: vec n)%Vec = 0%Vec.
Proof.
  induction n; auto.
  intros. rewrite vec_mult_step.
  simpl. f_equal. { lca. }
  apply IHn.
Qed.

Lemma mat_mult_vec_col0: forall {n}
  (x: vec 1),
  col 0%Vec @ x = (0: vec n)%Vec.
Proof.
  induction n; auto.
  intros.
  rewrite mat_mult_col.
  rewrite vec_mult_step.
  simpl. rewrite vec_plus_step.
  simpl. f_equal. { lca. }
  rewrite (eta0 _).
  rewrite (mat_mult_vec_empty _).
  rewrite vec_hc_col.
  rewrite vec_plus_0.
  apply vec_0_mult.
Qed.

Lemma mat_mult_col0: forall {n m}
  (A: matrix 1 n),
  col (0%Vec : vec m) @@ A = 0.
Proof.
  induction m.
    - intros. rewrite (eta0). apply eta0.
    - intros. rewrite mat_mult_mat_row_step.
      rewrite (eta 0).
      simpl.
      f_equal; auto.
      rewrite mat_mult_col.
      simpl. rewrite mat_mult_vec_empty.
      rewrite vec_plus_0.
      rewrite vec_mult_0. trivial.
Qed.

Lemma mat_plus_zero_GIBBERISH: forall {n m}
  (A B: matrix n m),
  A = 0 -> A + B = B.
Proof.
  intros. rewrite H.
  rewrite mat_plus_comm.
  apply mat_plus_0.
Qed.

Lemma vec_mult_1: forall {n}
  (x: vec n),
  (1%C * x)%Vec = x.
Proof.
  induction n.
   - intros. rewrite (eta0). apply eta0.
   - intros. rewrite vec_mult_step.
     rewrite eta.
     f_equal; auto.
    lca.
Qed.

Lemma mat_II_gibberish: forall {m n} (A: matrix (S n) m),
  ((1%C :: 0%Vec) :: col 0%Vec ++' I) @@ A = A.
Proof.
  intros.
  rewrite mat_mult_mat_row_step.
  simpl.
  replace A with ([hd A] ++ tl A) at 2.
  { rewrite (mat_mult_app_dist _ [hd A] _ _).
    rewrite mat_mult_I.
    rewrite (eta A) at 4.
    f_equal.
    - rewrite mat_mult_col.
      simpl. rewrite mat_mult_zeros.
      rewrite vec_plus_0.
      rewrite (mat_hc_hd_commute).
      apply vec_mult_1.
    - apply mat_plus_zero_GIBBERISH.
      apply mat_mult_col0.
  }
  simpl. symmetry. apply eta.
Qed.

Lemma mat_mult_I_eq: forall {n} (B: sqmatrix n),
  (forall {m} (A: matrix n m), B @@ A = A)
  -> B = I.
Proof.
  intros.
  specialize (H n I).
  rewrite mat_mult_I_r in H.
  apply H.
Qed.

Fact mat_I_step: forall {n},
  (I: sqmatrix (S n)) = ((1%C :: 0%Vec) :: col 0%Vec ++' I).
Proof.
  intros.
  symmetry. apply mat_mult_I_eq.
  intros. apply mat_II_gibberish.
Qed. 

Lemma mat_tc_tl_I: forall {n},
  tl (tc (I: sqmatrix (S n))) = I.
Proof.
  intros. rewrite mat_I_step.
  simpl. apply tc_col.
Qed.

Lemma mat_I_is_diag: forall {n},
  @is_diag n I.
Proof.
  induction n.
    - constructor.
    - rewrite mat_I_step. apply S_diag.
      apply IHn.
Qed.

Fact upTri_step: forall {n m} (A: matrix (S n) (S m)),
  is_upTri A -> A = (hd A :: col 0%Vec ++' (tl (tc A))).
Proof.
  intros.
  inversion H; subst.
  inj H3.
    + rewrite <- H3. simpl. f_equal. rewrite (eta_col 0) at 1.
      rewrite mat_hc_0. trivial.
    + repeat (apply (inj_pair2_eq_dec _ Nat.eq_dec) in H2).
      rewrite <- H2.
      f_equal.
      f_equal.
      simpl.
      rewrite tc_col. trivial.
Qed.

Lemma upTri_step_upTri: forall {n m} (A: matrix (S n) (S m)),
  is_upTri A -> is_upTri (tl (tc A)).
Proof.
  intros.
  inversion H; subst.
    inj H3.
    + rewrite (eta A) in H3.
      apply (f_equal tl) in H3.
      simpl in H3.
      rewrite eta_col in H3.
      apply (f_equal tc) in H3.
      rewrite tc_col in H3.
      rewrite mat_tc_0 in H3.
      rewrite mat_tl_tc_commute. rewrite <- H3.
      constructor.
    + inj H2.
    rewrite (eta A) in H2.
    apply (f_equal tl) in H2.
    simpl in H2.
    rewrite (eta_col A) in H2.
    apply (f_equal tc) in H2.
    rewrite <- mat_tl_tc_commute in H2.
    rewrite 2 tc_col in H2.
    rewrite <- H2.
    apply H3.
Qed.

Lemma mat_hc_tm: forall {n m} (A: matrix n (S m)),
  hd (tM A) = hc A.
Proof. auto. Qed.

Theorem diag_iff_low_up: forall {n} (A: sqmatrix n),
  is_diag A <-> is_upTri A /\ is_lowTri A.
Proof.
  induction n.
    - intros. rewrite (eta0 A).
      split; constructor; constructor.
    - intros.
      split.
      -- intros.
         unfold is_lowTri.
         assert (B:=diag_step A H).
        split; rewrite B.
        2: simpl tM.
        2: rewrite hc_col, tc_col.
        2: rewrite tm_dist.
        2: simpl.
        all: apply S_upTri.
        all: apply IHn.
        all: inversion H; subst.
        all: inj H1; rewrite <- H1.
        all: simpl.
        all: rewrite tc_col; apply H2.
    -- unfold is_lowTri. intros [L R].
      assert (B:= upTri_step A L).
      assert (D:= upTri_step (tM A) R).
      simpl in D. apply (f_equal tl) in D.
      simpl in D. apply (f_equal tM) in D.
      simpl in D. rewrite tc_col in D.
      rewrite <- (mat_tm_tl_commute (tM _)) in D.
      rewrite mat_tm_tm in D.
      rewrite hc_col in D. apply (f_equal hd) in D.
      simpl in D.
      rewrite mat_hc_hd_commute in D.
      replace (hd A) with (hd (hd A) :: (0: vec n))%Vec in B.
      { rewrite B. apply S_diag. apply IHn.
        split.
          + apply (upTri_step_upTri _ L).
          + unfold is_lowTri. rewrite <- mat_tm_tc_commute. rewrite <- mat_tm_tl_commute.
            rewrite <- mat_tl_tc_commute.
            apply (upTri_step_upTri _ R).
      }
      rewrite (eta_col A) at 2.
      simpl. rewrite D. rewrite <- mat_hc_tm.
      rewrite mat_hd_col_hd. simpl. rewrite mat_hd_hc_hd_eq. trivial.
Qed.

Theorem linear_functions: forall {n m},
  forall (f: vec n -> vec m),
    (forall x y: vec n, f (x + y) = f x + f y)%Vec
    ->
    (forall x: vec n, forall c: C, f (c * x)
  = c * f x)%Vec -> exists M: matrix m n,
    forall x: vec n, M @ x = f x.
Proof.
  induction n; intros.
    - exists emptyM. intros.
      specialize (H0 x 0%C).
      rewrite (eta0 _) in H0.
      rewrite vec_mult_0 in H0.
      rewrite (eta0 _). rewrite H0. rewrite mat_mult_vec_empty. trivial.
    - pose (s:= (fun x => f (0%C::x)%Vec)).
      specialize (IHn m s).
      assert (A: forall  x y, (s (x + y)%Vec = (s x + s y)%Vec)).
      { intros. unfold s. rewrite <- H. cbn. rewrite Cplus_0_r.
      trivial. }
      assert (B: forall x c, (s (c * x)%Vec = (c * s x)%Vec)).
      { intros. unfold s. replace (0%C :: (c * x))%Vec with (c * (0%C :: x))%Vec.
        { apply H0. }
       cbn. rewrite Cmult_0_r. trivial. }
      destruct (IHn A B) as [N C].
      exists (col (f (canon_e O)) ++' N).
      intros. simpl. rewrite (eta x).
      rewrite mat_mult_col. simpl.
      rewrite hc_col. rewrite tc_col.
      rewrite <- (vec_mult_I (hd _ :: _)).
      rewrite (mat_mult_col I).
      rewrite H. simpl hd. simpl tl.
      rewrite H0. f_equal.
      + rewrite mat_hc_I. trivial.
      + simpl. rewrite (@eye_cc_split _ 1 _ 0).
        rewrite dot_0. replace (0 ++' I) with (col 0%Vec ++' (I: sqmatrix n)).
        { rewrite tc_col. rewrite vec_mult_I. apply C. }
        f_equal.
        assert (forall z: nat, col (0%Vec: vec z) = (0: matrix z 1)).
        { induction z; auto. simpl. f_equal. apply IHz. }
        apply H1.
Qed.

Lemma mat_mult_mat_conj: forall {n m k}
  (A: matrix n m) (B: matrix m k),
  conjmat (A @@ B) = conjmat A @@ conjmat B.
Proof. induction n.
  - intros. rewrite (eta0). apply eta0.
  - intros. rewrite (mat_mult_mat_row_step).
    rewrite (eta A) at 3.
    cbn. rewrite (mat_mult_mat_row_step _ (conjmat B)).
    simpl. f_equal. 2: apply IHn.
    rewrite mat_mult_vec_conj.
    rewrite mat_tm_conj. trivial.
Qed.

Corollary herm_dist: forall {n m k} (A: matrix n m)
  (B: matrix m k),
  (A @@ B) ^* = B ^* @@ A^*.
Proof. intros.
        rewrite mat_mult_tm_dist.
        apply mat_mult_mat_conj.
Qed.

Lemma Runi_mult: forall {n m k} (Q: matrix n m)
  (P: matrix m k),
  Runitary Q -> Runitary P -> Runitary (Q @@ P).
Proof.
  unfold Runitary.
  intros. rewrite herm_dist.
  rewrite mat_mult_mat_mat_assoc.
  rewrite <- (mat_mult_mat_mat_assoc P).
  rewrite H0. rewrite mat_mult_I. apply H.
Qed.

Lemma Luni_mult: forall {n m k} (Q: matrix n m)
  (P: matrix m k),
  Lunitary Q -> Lunitary P -> Lunitary (Q @@ P).
Proof.
  unfold Lunitary.
  intros. rewrite herm_dist.
  rewrite mat_mult_mat_mat_assoc.
  rewrite <- (mat_mult_mat_mat_assoc _ Q).
  rewrite H. rewrite mat_mult_I. apply H0.
Qed.

Corollary uni_mult: forall {n} (Q P: sqmatrix n),
  unitary Q -> unitary P -> unitary (Q @@ P).
Proof. intros.
  split.
    2: apply Luni_mult.
    1: apply Runi_mult.
    1,3: apply H.
    all: apply H0.
Qed.

Lemma tm_0: forall {n m},
  tM (0: matrix m n) = 0.
Proof. induction n.
  - intros. etaeta.
  - intros. simpl. rewrite mat_hc_0. rewrite mat_tc_0.
    rewrite IHn. trivial.
Qed.

Lemma mat_hd_col_hc: forall {n m}
  (A: matrix (S n) (S m)),
  hd (col (hc A)) = [hd (hc A)].
Proof.
  intros. rewrite (eta A). simpl. trivial.
Qed.

Lemma mat_tl_hc_commute: forall {n m}
  (A: matrix (S n) (S m)),
  tl (hc A) = hc (tl A).
Proof.
  intros. rewrite (eta A). simpl. trivial.
Qed.

Theorem mat_mult_mat_more_mat: forall {n m k}
  (A: matrix n (S m)) (B: matrix (S m) k),
  A @@ B = col (hc A) @@ [hd B] + tc A @@ tl B.
Proof. induction n.
  - intros. etaeta.
  - intros. rewrite 3 mat_mult_mat_row_step.
    cbn. f_equal.
    + rewrite ! mat_mult_col.
      rewrite mat_hd_col_hc.
      simpl. rewrite ! mat_tm_tc_commute.
      rewrite ! mat_hc_hd_commute.
      simpl. rewrite mat_mult_vec_empty.
      rewrite vec_plus_0.
      rewrite mat_hd_hc_hd_eq.
      rewrite mat_hd_tc_commute. trivial.
    + rewrite IHn.
      rewrite vec_tl_col_commute.
      rewrite mat_tl_tc_commute.
      rewrite mat_tl_hc_commute.
      trivial.
Qed.

Lemma swap_last: forall {n m} (A: matrix n m)
  (x: vec m),
  (((0: matrix n (S 0)) ++' I) ++ [canon_e O]) @@ (x::A) = A ++ [x].
Proof.
 induction n.
    + intros. rewrite (eta0 A).
      simpl. assert (D:=mat_mult_I [x]).
      simpl in D. apply D.
    + intros. rewrite (eta A). simpl.
      specialize (IHn _ (tl A) x).
      simpl in IHn.
      rewrite mat_mult_mat_row_step.
      simpl. f_equal.
      * rewrite mat_mult_col. simpl.
        rewrite mat_tm_tc_commute.
        rewrite mat_hc_hd_commute.
        simpl.
        rewrite vec_mult_0.
        rewrite vec_plus_comm.
        rewrite vec_plus_0.
        rewrite mat_mult_col. simpl.
        rewrite mat_tm_tc_commute.
        rewrite mat_hc_hd_commute.
        simpl. rewrite vec_mult_1.
        rewrite mat_mult_zeros.
        apply vec_plus_0.
      * simpl. rewrite <- IHn.
        rewrite (eta_col _).
        rewrite mat_tc_app_dist.
        rewrite mat_hc_app_dist. simpl.
        rewrite (mat_hc_cc (0: matrix _ 1) (eyeM 1)).
        rewrite (mat_tc_cc (0: matrix _ 1) _).
        rewrite (eta0_col _). rewrite cc_empty.
        rewrite mat_hc_0.
        rewrite (@eye_cc_split _ 1).
        rewrite (eta_col (_ ++ _)).
        rewrite mat_tc_app_dist.
        rewrite mat_hc_app_dist. simpl.
        rewrite (mat_hc_cc (0: matrix _ 1) _).
        rewrite (mat_tc_cc (0: matrix _ 1) _).
        rewrite (eta0_col _). rewrite cc_empty.
        rewrite mat_hc_0.
        rewrite mat_mult_mat_more_mat.
        simpl. rewrite mat_mult_mat_more_mat.
        simpl. rewrite mat_mult_mat_MAGIC.
        rewrite ! hc_col.
        rewrite tc_col.
        rewrite vec_hc_col.
        rewrite mat_plus_0.
        rewrite (mat_mult_mat_more_mat _ (x::tl A)).
        simpl. rewrite mat_hc_app_dist.
        simpl. rewrite (mat_hc_cc (0: matrix _ 1)).
        rewrite mat_hc_0. f_equal.
        rewrite mat_mult_mat_more_mat.
        simpl. rewrite tc_col.
        rewrite mat_tc_app_dist.
        rewrite (mat_tc_cc (0: matrix _ 1)).
        simpl. rewrite (mat_hc_cc (col _) (I ++ _)).
        rewrite vec_hc_col.
        assert (forall {n m}, (0: vec n) ++ (0: vec m) = 0)%Vec.
        { induction n0. + intros. trivial. + intros. simpl. f_equal. apply IHn0. }
        rewrite H. rewrite mat_mult_col0.
        rewrite mat_plus_comm.
        rewrite mat_plus_0.
        rewrite (eta0_col _).
        rewrite cc_empty. trivial.
Qed.

Lemma conj_canon_e: forall {n k},
  (@canon_e n k) ^*%Vec = canon_e k.
Proof. induction n.
  - intros. etaeta.
  - intros.
    destruct k. + cbn. f_equal. lca.
    apply vec_conj_0.
    + cbn. f_equal. lca.
      apply IHn.
Qed.

Lemma conj_I: forall {n m k},
  conjmat (@eyeM k n m) = eyeM k.
Proof.
  induction n.
    - intros. etaeta.
    - intros. cbn.
      f_equal. + apply conj_canon_e.
      + apply IHn.
Qed.

Corollary hermit_I: forall {n},
  (I: sqmatrix n) ^* = I.
Proof. intros. rewrite mat_tm_I. apply conj_I. Qed.

Lemma mat_mult_mat_0_r: forall {n m k}
  (A: matrix n m),
  A @@ 0 = (0: matrix n k).
Proof.
  induction n.
    - intros. etaeta.
    - intros. rewrite mat_mult_mat_row_step.
      simpl. f_equal. { 
        rewrite tm_0. apply vec_mult_M0.
      } apply IHn.
Qed.

Lemma mat_mult_mat_0: forall {n m k}
  (A: matrix m k),
  0 @@ A = (0: matrix n k).
Proof.
  induction n.
    - intros. etaeta.
    - intros. rewrite mat_mult_mat_row_step.
      simpl.
      rewrite mat_mult_zeros. f_equal. apply IHn.
Qed.

Fixpoint Vcnorm2 {n} (x: vec n): R :=
  match x with
    | [] => R0
    | h::xs => Cnorm2 h + Vcnorm2 xs
  end.

Definition Vnorm {n} (x: vec n): R := sqrt (Vcnorm2 x).

Lemma mat_mult_mat_plus_dist: forall {n m k}
  (A B: matrix n m) (D: matrix m k),
  (A + B) @@ D = A @@ D + B @@ D.
Proof. induction n; intros. - etaeta.
  - rewrite (mat_mult_mat_row_step A D).
    rewrite (mat_mult_mat_row_step B D).
    rewrite (eta A), (eta B) at 1.
    cbn. rewrite mat_mult_mat_row_step. simpl.
    f_equal. apply mat_vec_dist.
    apply IHn.
Qed.

Lemma mat_scalar_app_dist: forall {n m k}
  (a: C) (A: matrix n m) (B: matrix k m),
  a * (A ++ B) = a * A ++ a * B.
Proof.
  induction n.
    - intros. rewrite (eta0 A). trivial.
    - intros. rewrite (eta A). cbn. f_equal.
      apply IHn.
Qed.

Lemma vec_scalar_app_dist: forall {n m}
  (a: C) (u: vec n) (v: vec m),
  (a * (u ++ v) = a * u ++ a * v)%Vec.
Proof.
  induction u.
    - intros. trivial.
    - intros. cbn. f_equal. apply IHu.
Qed.

Lemma mat_scalar_cc_dist: forall {n m k}
  (a: C) (A: matrix n m) (B: matrix n k),
  a * (A ++' B) = a * A ++' a * B.
Proof.
  induction n.
    - intros. etaeta.
    - intros. cbn. f_equal.
      -- rewrite vec_scalar_app_dist.
         rewrite (eta A), (eta B). cbn. trivial.
      -- rewrite (eta A), (eta B). cbn. apply IHn.
Qed.

Lemma mat_scalar_tm: forall {n m}
  (a: C) (A: matrix n m),
  tM (a * A) = a * tM A.
Proof.
    induction n.
    - intros. rewrite eta0_col. apply eta0_col.
    - intros. rewrite (eta A). cbn.
      change (mapmat (fun x : vec m => (a * x)%Vec)
        (tl A)) with (a * tl A).
      change ((a * hd A)%Vec :: a * tl A) with
      ([(a * hd A)%Vec] ++ (a * tl A)).
      change (hd A :: tl A) with ([hd A] ++ tl A).
      rewrite ! (mat_tm_app_dist ([ _ ])).
      simpl. rewrite (mat_scalar_cc_dist a (tM [_])). rewrite <- IHn.
      f_equal.
      rewrite ! tm_dist.
      simpl.
      rewrite (mat_scalar_cc_dist a (col _)).
      rewrite (eta0_col _). rewrite (eta0_col (a * _)).
      assert (forall {r} (b: C) (x: vec r), col (b * x)%Vec = b * col x).
      { induction r. - intros. etaeta. - intros. rewrite (eta x).
        cbn. f_equal. apply IHr. }
      rewrite H. trivial.
Qed.

Lemma mat_vec_scalar_dist: forall {n m}
  (a: C) (A: matrix n m) (x: vec m),
  a * A @ x = (a * (A @ x))%Vec.
Proof.
  induction n.
    - intros. etaeta.
    - intros. rewrite (eta A). cbn.
      f_equal.
      + symmetry. apply dot_mult_commute.
      + apply IHn.
Qed.

Lemma mat_mult_scalar_dist_l: forall {n m k}
  (a: C) (A: matrix n m) (B: matrix m k),
  (a * A) @@ B = a * (A @@ B).
Proof.
  induction n.
    - intros. etaeta.
    - intros. rewrite (mat_mult_mat_row_step A B).
      rewrite (eta A). simpl. cbn.
      rewrite <- mat_vec_scalar_dist.
      change (mapmat (fun x : vec k => (a * x)%Vec)
     (tl A @@ B)) with (a * (tl A @@ B)).
      change (mapmat (fun x : vec m => (a * x)%Vec)
      (tl A)) with (a * tl A).
      rewrite mat_mult_mat_row_step.
      simpl.
      rewrite mat_scalar_comm. f_equal.
      apply IHn.
Qed.

Lemma mat_mult_scalar_dist_r: forall {n m k}
  (a: C) (A: matrix n m) (B: matrix m k),
  A @@ (a * B) = a * (A @@ B).
Proof.
  induction n.
    - intros. etaeta.
    - intros. rewrite mat_mult_mat_row_step.
      rewrite IHn.
      rewrite mat_scalar_tm.
      rewrite mat_mult_mat_row_step.
      cbn. f_equal. apply mat_vec_scalar_dist.
Qed.

Lemma vcnorm_pos: forall {n} (u: vec n),
  0%R <= Vcnorm2 u.
Proof.
  induction u.
    - simpl. lra.
    - simpl. assert (A:= pow2_ge_0 (fst h)).
      assert (B:= pow2_ge_0 (snd h)).
      lra.
Qed.

Corollary vnorm_pos: forall {n} (u: vec n),
  0%R <= Vnorm u.
Proof. intros. unfold Vnorm. apply sqrt_positivity.
  apply vcnorm_pos.
Qed.

Theorem vnorm_dot: forall {n} (u: vec n),
  (Vnorm u * Vnorm u)%R = fst (dot u u)%Vec.
Proof.
  induction n.
    - intros. rewrite (eta0 u). unfold Vnorm. cbn.
      apply sqrt_def. lra.
    - intros.
      rewrite (eta u).
      unfold Vnorm. rewrite sqrt_def.
      * simpl. f_equal.
        ++ lra.
        ++ rewrite <- IHn.
           unfold Vnorm. symmetry.
           apply sqrt_def.
           apply vcnorm_pos.
      * apply vcnorm_pos.
Qed.

Lemma vcnorm_scalarR: forall {n} (a: R) (u: vec n),
  Vcnorm2 (a * u)%Vec = (a² * Vcnorm2 u)%R.
Proof. induction n.
    - intros. rewrite (eta0 u). simpl. lra.
    - intros. rewrite (eta u). simpl.
      rewrite ! Rmult_0_l.
      rewrite Rplus_0_r.
      rewrite Rminus_0_r.
      rewrite ! Rmult_1_r.
      rewrite Rmult_plus_distr_l.
      f_equal. cbv. lra. 
      apply IHn.
Qed.

Corollary vnorm_scalarR: forall {n} (a: R) (u: vec n),
  Vnorm (a * u)%Vec = (Rabs a * Vnorm u)%R.
Proof. intros. unfold Vnorm.
    rewrite vcnorm_scalarR.
    rewrite sqrt_mult_alt.
    rewrite sqrt_Rsqr_abs. lra. apply Rle_0_sqr.
Qed.

Lemma vcnorm_iff_0: forall {n} (u: vec n),
  u = 0%Vec <-> Vcnorm2 u = 0%R.
Proof.
  induction n; intros.
    - rewrite (eta0 u). split; auto.
    - rewrite (eta u). split.
      + intros. inversion H. inj H2. rewrite H1, H2.
        simpl. rewrite Rmult_0_l. rewrite ! Rplus_0_l.
        apply IHn. trivial.
      + intros. simpl in H.
      rewrite ! Rmult_1_r in H.
      replace (fst (hd u) * fst (hd u) + snd (hd u) * snd (hd u))%R
      with ((fst (hd u))² + (snd (hd u))²)%R in H.
      2: cbv; lra.
      rewrite Rplus_assoc in H.
      assert (C:=vcnorm_pos (tl u)).
      assert ((fst (hd u))² = 0%R).
      { assert (0 <= (snd (hd u))² + Vcnorm2 (tl u)).
        { assert (G:= Rle_0_sqr (snd (hd u))). lra. }
      apply (Rplus_eq_0_l _ _ (Rle_0_sqr _) H0 H).
      }
      rewrite H0 in H. rewrite Rplus_0_l in H.
      assert ((snd (hd u))² = 0%R).
      { apply (Rplus_eq_0_l _ _ (Rle_0_sqr _) C H). }
      rewrite H1 in H. rewrite Rplus_0_l in H.
      assert (fst (hd u) = 0%R).
      { destruct (Rmult_integral _ _ H0); lra. }
      assert (snd (hd u) = 0%R).
      { destruct (Rmult_integral _ _ H1); lra. }
      assert (hd u = 0%C) by lca. simpl.
      rewrite H4. f_equal. apply IHn. apply H.
Qed.

Corollary notvcnorm_iff_0: forall {n} (u: vec n),
  u <> 0%Vec <-> Vcnorm2 u <> 0%R.
Proof.
  induction n.
  - intros. rewrite (eta0 u).
    split; auto.
  - intros. rewrite (eta u).
    split.
    -- intros. intros F.
      apply H.
      apply vcnorm_iff_0. apply F.
  -- intros.
     intros F. rewrite F in H. apply H.
     apply vcnorm_iff_0. trivial.
Qed.

Corollary vnorm_iff_0: forall {n} (u: vec n),
  u = 0%Vec <-> Vnorm u = 0%R.
Proof.
  intros. split; intros.
    - destruct (vcnorm_iff_0 u) as [U _]. unfold Vnorm.
      specialize (U H). apply (f_equal sqrt) in U.
      rewrite U. apply sqrt_0.
    - apply vcnorm_iff_0.
      unfold Vnorm in H. apply (f_equal (fun x => x * x)%R) in H.
      rewrite (sqrt_def _ (vcnorm_pos _)) in H.
      lra.
Qed.

Lemma notvnorm_iff_0: forall {n} (u: vec n),
  u <> 0%Vec <-> Vnorm u <> 0%R.
Proof. intros. destruct (vnorm_iff_0 u). 
    split; auto.
Qed.

Lemma mat_plus_col_step: forall {n m}
  (A B: matrix n (S m)),
  A + B = col (hc A + hc B)%Vec ++' (tc A + tc B).
Proof.
  induction n.
    - intros. etaeta.
    - intros. rewrite (eta A), (eta B). simpl.
      cbn. f_equal.
      rewrite <- vec_hd_plus_dist.
      rewrite <- vec_tl_plus_dist.
      apply eta. apply IHn.
Qed.

Lemma mat_plus_tm_dist: forall {n m} (A B: matrix n m),
tM (A + B) = tM A + tM B.
Proof.
  induction n.
    - intros. rewrite eta0_col. apply eta0_col.
    - intros. rewrite (eta A), (eta B).
      cbn.
      change (zipmat (fun x y : vec m => (x + y)%Vec)
        (tl A) (tl B)) with (tl A + tl B).
      change ((hd A + hd B)%Vec :: tl A + tl B)
      with ([(hd A + hd B)%Vec] ++ (tl A + tl B)).
      rewrite (mat_tm_app_dist [_]).
      rewrite IHn.
      rewrite tm_dist.
      simpl.
      rewrite mat_plus_col_step.
      rewrite ! mat_hc_hd_commute.
      rewrite ! mat_tm_tc_commute. simpl.
      f_equal.
      assert (forall {i} (x: vec i),
        col x ++' emptyM = col x).
      { induction i. intros. etaeta.
        intros. simpl. rewrite vec_tl_col_commute. rewrite IHi.
        rewrite (eta x). simpl. trivial. }
      rewrite (eta0_col _). apply H.
Qed.

Lemma mat_plus_conj_dist: forall {n m} (A B: matrix n m),
conjmat (A + B) = conjmat A + conjmat B.
Proof.
  induction n; intros. - etaeta.
  - rewrite (eta A), (eta B). cbn.
    f_equal. apply vec_plus_conj_dist.
    apply IHn.
Qed.

Corollary mat_plus_herm_dist: forall {n m}
  (A B: matrix n m),
    (A + B)^* = A^* + B^*.
Proof. intros. rewrite mat_plus_tm_dist. apply mat_plus_conj_dist. Qed.

Corollary mat_mult_mat_plus_dist_r: forall {n m k}
  (A: matrix n m) (B D: matrix m k),
  A @@ (B + D) = A @@ B + A @@ D.
Proof. intros.
  apply tm_bijection.
  rewrite mat_mult_tm_dist.
  rewrite ! mat_plus_tm_dist.
  rewrite ! mat_mult_tm_dist.
  apply mat_mult_mat_plus_dist.
Qed.

Lemma mat_hc_scalar: forall {n m} (a: C)
  (A: matrix n (S m)), hc (a * A) = (a * hc A)%Vec.
Proof. induction n; intros. - etaeta.
  - rewrite (eta A). cbn. f_equal.
    rewrite (eta (hd A)). trivial.
    apply IHn.
Qed.

Lemma mat_tc_scalar: forall {n m} (a: C)
  (A: matrix n (S m)), tc (a * A) = a * tc A.
Proof. induction n; intros. - etaeta.
  - rewrite (eta A). cbn.
    f_equal. + rewrite (eta (hd A)). trivial.
    + apply IHn.
Qed.

Lemma mat_hd_scalar: forall {n m} (a: C)
  (A: matrix (S n) m),
  hd (a * A) = (a * hd A)%Vec.
Proof. intros. rewrite (eta A). trivial. Qed.

Lemma mat_tl_scalar: forall {n m} (a: C)
  (A: matrix (S n) m),
  tl (a * A) = a * tl A.
Proof. intros. rewrite (eta A). trivial. Qed.

Lemma vec_hd_scalar: forall {n} (a: C) (x: vec (S n)),
  hd (a * x)%Vec = (a * hd x)%C.
Proof. intros. rewrite (eta x). trivial. Qed.

Lemma vec_tl_scalar: forall {n} (a: C) (x: vec (S n)),
  tl (a * x)%Vec = (a * tl x)%Vec.
Proof. intros. rewrite (eta x). trivial. Qed.

Lemma mat_scalar_herm: forall {m n} (a: C)
  (A: matrix n m),
  (a * A)^* = (a^*)%C * (A^*).
Proof. induction m; intros. - etaeta.
  - destruct n; auto. rewrite eta0_col. apply eta0_col. cbn. 
    f_equal. rewrite mat_hc_scalar.
    apply vec_mult_conj_dist.
    change (mapmat (fun x : vec (S n) => (x ^*)%Vec)
  (tM (tc (a * A)))) with ((tc (a * A))^*).
    change (mapmat
  (fun x : vec (S n) => ((a ^*)%C * x)%Vec)
  (mapmat (fun y : vec (S n) => (y ^*)%Vec)
     (tM (tc A)))) with ((a^*)%C * (tc A)^*).
    rewrite mat_tc_scalar.
    apply IHm.
Qed.

Lemma row_tm_col: forall {n} (u: vec n),
  tM [u] = col u.
Proof. induction n; intros. etaeta.
  rewrite (eta u).
  simpl. f_equal. apply IHn.
Qed.

Corollary col_tm_row: forall {n} (u: vec n),
  tM (col u) = [u].
Proof. intros. rewrite <- row_tm_col.
  apply mat_tm_tm. Qed.

Fact col_0_0: forall {n},
  (col 0%Vec) = (0: matrix n 1).
Proof. induction n; auto. rewrite (eta 0).
  rewrite (eta 0%Vec). simpl. f_equal. apply IHn.
Qed.

Corollary herm_app_dist: forall {n m k}
  (A: matrix n m) (B: matrix k m),
  (A ++ B) ^* = A^* ++' B^*.
Proof.
  intros. rewrite mat_tm_app_dist.
  apply mat_conj_split_col. Qed.

Lemma mat_conj_split_row: forall {n m k}
  (A: matrix n m) (B: matrix k m),
  conjmat (A ++ B) = conjmat A ++ conjmat B.
Proof. induction n. - intros. rewrite (eta0 A). trivial.
  - intros. rewrite (eta A). cbn. f_equal.
    apply IHn. Qed.

Corollary herm_cc_dist: forall {n m k}
  (A: matrix n m) (B: matrix n k),
  (A ++' B)^* = A^* ++ B^*.
Proof. intros.
  rewrite mat_tm_cc_dist.
  apply mat_conj_split_row. Qed.

Corollary vcnorm2_dotC: forall {n} (u: vec n),
  dot u u = Vcnorm2 u.
Proof. intros.
  assert ((Vcnorm2 u = Vnorm u * Vnorm u)%R).
  { unfold Vnorm. symmetry. apply sqrt_def. apply vcnorm_pos. }
  rewrite H. assert (A := vnorm_dot u).
             assert (B := dot_R u). lca.
Qed.

Lemma vec_scalar_scalar: forall {n} (a b: C)
  (z: vec n),
  (a * (b * z) = (a * b)%C * z)%Vec.
Proof.
  induction n; intros.
    - etaeta.
    - rewrite (eta z). cbn.
      f_equal. lca. apply IHn.
Qed.

Lemma mat_scalar_scalar: forall {n m}
  (a b: C) (A: matrix n m),
  a * (b * A) = (a * b)%C * A.
Proof.
  induction n; intros.
    - etaeta.
    - rewrite (eta A). cbn.
      f_equal. apply vec_scalar_scalar.
      apply IHn.
Qed.

Lemma mat_mult_0_scalar: forall {n m} (a: C),
  a * (0: matrix n m) = 0.
Proof. induction n; intros. etaeta.
  cbn. f_equal. apply vec_0_mult.
  apply IHn. Qed.

Lemma mat_herm_unit: forall {n} (A: sqmatrix n),
  hermit A -> Lunitary A -> unitary A.
Proof.
  induction n; intros; split; auto.
  unfold Lunitary in H0.
  unfold Runitary. rewrite H. rewrite H in H0.
  apply H0.
Qed.

Lemma matstep_herm: forall {n m} (A: matrix n m),
  (canon_e O :: col 0%Vec ++' A)^* =
  canon_e O :: col 0%Vec ++' (A^*).
Proof.  intros.
      cbn.
      f_equal. f_equal. lca.
      f_equal. rewrite hc_col.
      apply vec_conj_0.
      rewrite tc_col.
      change (mapmat (fun x : vec (S n) => (x ^*)%Vec) (tM (0%Vec :: A))) with (conjmat (tM ([0%Vec] ++ A))).
      rewrite (mat_tm_app_dist [_]).
      rewrite row_tm_col.
      rewrite mat_conj_split_col.
      f_equal. rewrite <- col_conj. f_equal.
      apply vec_conj_0.
Qed.

Lemma mat_hc_plus_dist: forall {n m}
  (A B: matrix n (S m)),
  hc (A + B) = (hc A + hc B)%Vec.
Proof. intros. rewrite (eta_col A).
       rewrite (eta_col B).
      rewrite mat_plus_col_step. rewrite hc_col.
      rewrite hc_col. trivial.
Qed.

Lemma mat_tc_plus_dist: forall {n m}
  (A B: matrix n (S m)),
  tc (A + B) = tc A + tc B.
Proof. intros.
      rewrite mat_plus_col_step. rewrite tc_col. trivial.
Qed.

Lemma vcnorm_0_step: forall {n} (x: vec n),
  Vcnorm2 (0%C::x) = Vcnorm2 x.
Proof. intros. simpl. lra. Qed.

Corollary vnorm_0_step: forall {n} (x: vec n),
  Vnorm (0%C::x) = Vnorm x.
Proof. intros. unfold Vnorm. rewrite vcnorm_0_step.
trivial. Qed.

Lemma mat_tl_cc_dist: forall {n m k} (A: matrix (S n) m)
  (B: matrix (S n) k),
  tl (A ++' B) = tl A ++' tl B.
Proof. intros. rewrite (eta A), (eta B). trivial. Qed.

Lemma vcnorm_plus_dist: forall {n} (x y: vec n),
  Vcnorm2 (x + y)%Vec = (Vcnorm2 x + Vcnorm2 y + 2 * fst (dot x y))%R.
Proof. induction n.
    - intros. rewrite (eta0 x), (eta0 y). simpl. lra.
    - intros. rewrite (eta x), (eta y). cbn.
      fold (@plusvecs n). rewrite IHn.
      rewrite ! Rmult_1_r.
      rewrite ! Rmult_plus_distr_r.
      rewrite ! Rmult_plus_distr_l.
      replace (fst (hd x) * fst (hd y) -
   snd (hd x) * - snd (hd y))%R with
      (fst (hd x) * fst (hd y) + snd (hd x) * snd (hd y))%R by lra.
      pose (a:= (fst (hd x) * fst (hd x))%R). fold a.
      pose (b:= (fst (hd y) * fst (hd x))%R). fold b.
      pose (c:= (fst (hd x) * fst (hd y))%R). fold c.
      pose (d:= (fst (hd y) * fst (hd y))%R). fold d.
      pose (e:= (snd (hd x) * snd (hd x))%R). fold e.
      pose (f:= (snd (hd x) * snd (hd y))%R). fold f.
      pose (g:= (snd (hd y) * snd (hd x))%R). fold g.
      pose (h:= (snd (hd y) * snd (hd y))%R). fold h.
      replace (a + e + Vcnorm2 (tl x) +
 (d + h + Vcnorm2 (tl y)))%R with
      ((a + e + d + h) + (Vcnorm2 (tl x) + Vcnorm2 (tl y)))%R by lra.
      replace (a + e + d + h +
 (Vcnorm2 (tl x) + Vcnorm2 (tl y)) +
 (2 * (c + f) + 2 * fst (dot (tl x) (tl y))))%R with
      ((a + e + d + h + 2 * (c + f)) + (Vcnorm2 (tl x) + Vcnorm2 (tl y) + 2 * fst (dot (tl x) (tl y))))%R by lra.
      f_equal. subst a b c d e f g h. lra. Qed.

Lemma mat_herm_herm: forall {n m} (A: matrix n m),
  A ^* ^* = A.
Proof. intros.
  rewrite mat_tm_conj. rewrite mat_conj_conj.
  apply mat_tm_tm. Qed.

Section Householder.

  Let H {n: nat} {z: vec n} := (I + (- 2) *  (col ((/ Vnorm z)%R * z))%Vec @@ [((/ Vnorm z)%R * z)^*]%Vec).

  Lemma z2: forall {u} (z: vec u), (
        -2 * z = -z + -z)%Vec.
  Proof. induction u. intros. etaeta.
          intros. rewrite (eta z). cbn.
          f_equal. lca. apply IHu.
  Qed.

  Lemma Y2: forall {i j} (Y: matrix i j),
      (-2) * Y = -Y + -Y.
  Proof. induction i. intros. etaeta.
        intros. rewrite (eta Y). cbn.
        f_equal. - apply z2.
  - apply IHi. Qed.

  Lemma HH_I: forall (n: nat) (z: vec n), z <> 0%Vec -> (@H n z) @@ (@H n z) = I.
  Proof. intros. unfold H. pose (v:= ((/ Vnorm z)%R * z)%Vec). fold v. rewrite mat_mult_mat_plus_dist.
    rewrite mat_mult_I.
    rewrite mat_mult_mat_plus_dist_r.
    rewrite mat_mult_I_r.
    rewrite mat_mult_mat_mat_assoc.
    rewrite <- (mat_mult_mat_mat_assoc [v^*]%Vec).
    rewrite mat_mult_scalar_dist_r.
    rewrite mat_mult_scalar_dist_l.
    rewrite (mat_mult_scalar_dist_l (-2) (_ @@ _)).
    rewrite mat_mult_scalar_dist_r.
    simpl ([v ^*]%Vec @@ _).
    rewrite dot_conj_dist.
    rewrite vec_hc_col.
    replace (dot v v) with (1%C).
    2:{ rewrite vcnorm2_dotC.
    unfold v. rewrite vcnorm_scalarR.
    rewrite Rsqr_inv. 2: { assert (L:= notvnorm_iff_0 z). apply L. apply H0. }
   unfold Vnorm.
   rewrite Rsqr_sqrt. 2: { apply vcnorm_pos. }
   rewrite Rinv_l. 2: { apply notvcnorm_iff_0. apply H0. } lca.
    }
      replace (1 ^*)%C with 1%C by lca.
      replace ([[1%C]]) with (I: sqmatrix 1) by auto.
      rewrite mat_mult_I.
      pose (X := -2 * (col v @@ [(v ^*)%Vec])).
      fold X. rewrite mat_mult_scalar_dist_l. fold X.
      rewrite Y2.
      rewrite mat_plus_assoc.
      rewrite <- (mat_plus_assoc X (-X)).
      rewrite (mat_plus_sub X X).
      rewrite mat_sub_sub.
      rewrite (mat_plus_comm 0).
      rewrite mat_plus_0.
      rewrite (mat_plus_sub X X).
      rewrite mat_sub_sub.
      apply mat_plus_0.
  Qed.

  Theorem Hh_H: forall (n: nat) (z: vec n), (@H n z)^* = (@H n z).
  Proof. intros.
      unfold H.
      destruct (vec_eq_dec z 0%Vec).
      { rewrite e. rewrite vec_0_mult. rewrite col_0_0.
      rewrite mat_mult_0_scalar.
      rewrite mat_mult_mat_0.
      rewrite mat_plus_0.
      apply hermit_I. } pose (v := ((/ Vnorm z)%R * z)%Vec). fold v.
      rewrite mat_plus_herm_dist.
      f_equal. apply hermit_I.
      rewrite herm_dist.
      replace ([(v^*)%Vec]^*) with (col v).
      replace ((-2 * col v)^*) with (-2 * [v^*]%Vec).
      rewrite mat_mult_scalar_dist_l.
      apply mat_mult_scalar_dist_r.
      rewrite mat_scalar_herm.
      f_equal. lca.
      cbn.
      rewrite vec_hc_col. trivial.
      rewrite row_tm_col.
      rewrite col_conj. rewrite mat_conj_conj. trivial.
  Qed.

  Corollary HRunit: forall {n} (u: vec n),
    u <> 0%Vec -> ((@H n u) @@ (@H n u)^*) = I.
  Proof. intros. rewrite Hh_H. apply (HH_I). apply H0. Qed.

  Lemma Hex: forall (n: nat) (z y: vec n),
  dot z y = 0%C -> (@H n z) @ y = y.
  Proof. induction n; intros.
    - etaeta.
    - unfold H.
      rewrite mat_mat_dist.
      rewrite mat_mult_mat_vec_assoc.
      rewrite vec_mult_I.
      rewrite <- vec_plus_0.
      f_equal.
      rewrite mat_mult_col.
      simpl hd. simpl tl.
      rewrite mat_mult_vec_empty.
      rewrite vec_plus_0.
      rewrite mat_hc_scalar.
      rewrite vec_hc_col.
      rewrite dot_conj_dist.
      rewrite <- dot_mult_commute.
      rewrite H0. rewrite Cmult_0_r.
      rewrite Cconj_0. apply vec_mult_0.
  Qed.

  Lemma Hz: forall (n: nat) (z: vec n),
    (@H n z) @ z = (-z)%Vec.
  Proof. intros. unfold H.
    destruct (vec_eq_dec z 0%Vec).
    { rewrite e. rewrite mat_mult_zeros.
      symmetry. apply vec_neg_0. }
    induction n; intros.
      - etaeta.
      - unfold H. pose (N := (/ Vnorm z)%R). fold N.
       rewrite mat_mat_dist.
      rewrite mat_mult_mat_vec_assoc.
      rewrite vec_mult_I.
      rewrite mat_mult_col.
      simpl hd. simpl tl.
      rewrite mat_mult_vec_empty.
      rewrite vec_plus_0.
      rewrite mat_hc_scalar.
      rewrite vec_hc_col.
      rewrite dot_conj_dist.
      rewrite <- dot_mult_commute.
      rewrite vcnorm2_dotC.
      rewrite Cconj_mult_distr.
      replace (N ^*)%C with (RtoC N) by lca.
      rewrite ! vec_scalar_scalar.
      replace (N * (Vcnorm2 z) ^* * -2 * N)%C with
      (-2 * (Vcnorm2 z)^* * (N * N))%C by lca.
      replace (N * N)%C with
      (/ Vcnorm2 z)%C.
      2: { subst N.
      replace (Vcnorm2 z) with (Vnorm z * Vnorm z)%R.
      2: { unfold Vnorm.
      apply sqrt_def. apply vcnorm_pos. }
      replace (((/ Vnorm z)%R * (/ Vnorm z)%R)%C)
      with ((RtoC (/ Vnorm z * / Vnorm z)%R)) by lca.
      rewrite <- (Rinv_mult_distr (Vnorm z)).
      2,3: apply notvnorm_iff_0; auto.
      assert (forall (r: R), r<>0%R-> / (RtoC r) = RtoC (/ r)).
      { intros. cbv. change R1 with 1%R. change R0 with 0%R.
      rewrite Ropp_0.
      rewrite ! Rmult_0_l.
      rewrite Rmult_1_r. rewrite Rplus_0_r.
      rewrite Rinv_mult_distr. 2,3: apply H0.
      rewrite <- Rmult_assoc.
      rewrite Rinv_r_simpl_r; auto.
      } apply H0. replace (Vnorm z * Vnorm z)%R
      with (Vcnorm2 z)%R.
      apply notvcnorm_iff_0. apply n0. 
      unfold Vnorm. rewrite sqrt_def; auto.
      apply vcnorm_pos.
      }
    replace ((Vcnorm2 z)^*)%C with (RtoC (Vcnorm2 z)) by lca.
    rewrite Cmult_assoc.
    rewrite Cinv_r. 2:{ destruct (notvcnorm_iff_0 z) as [F _].
    specialize (F n0). intros G. apply F. inversion G. trivial. }
    rewrite Cmult_1_r.
    rewrite z2. rewrite <- vec_plus_assoc.
    rewrite (vec_plus_sub z).
    rewrite vec_sub_sub. rewrite vec_plus_comm.
    apply vec_plus_0.
Qed.

  Definition HstepH {n} (u: vec (S n)) (Q: sqmatrix n) :=
  (canon_e O :: col 0%Vec ++' Q) @@ (@H _ u).

  Lemma unistep_uni: forall {n} (Q: sqmatrix n),
  unitary Q -> unitary (canon_e O :: col 0%Vec ++' Q).
  Proof. unfold unitary. unfold Lunitary, Runitary.
    intros n Q [L R]. rewrite matstep_herm.
    rewrite 2 mat_mult_mat_row_step. simpl hd.
    simpl tl. simpl I. split; f_equal.
    1,3: cbn.
    1,2: rewrite hc_col, tc_col.
    1,2: rewrite dot_0. 1,2: f_equal. lca. 2:lca.
      change (0%Vec :: Q ^*) with ([0%Vec] ++ Q^*).
      2:change (0%Vec :: Q) with ([0%Vec] ++ Q).
      1,2:rewrite (mat_tm_app_dist [_]).
      1,2:rewrite mat_mult_col.
      1,2:rewrite row_tm_col.
      1,2:rewrite hc_col, tc_col. 1,2: simpl.
      1,2:rewrite mat_mult_zeros.
      1,2:rewrite vec_0_mult. 1,2:apply vec_plus_0.
    1,2:rewrite mat_mult_mat_more_mat.
    1,2:rewrite hc_col, tc_col. 1,2: simpl.
      1,2:rewrite hc_col, tc_col.
      1,2:rewrite mat_mult_zeros.
      1,2:rewrite mat_mult_col.
      1,2:rewrite vec_hc_col; rewrite mat_mult_vec_empty.
      1,2:rewrite vec_0_mult.
      1,2:rewrite vec_plus_0; rewrite col_0_0.
      1,2:rewrite mat_mult_mat_0.
      1,2:rewrite mat_plus_col_step.
      1,2:rewrite <- col_0_0.
      1,2:rewrite ! hc_col, ! tc_col.
      1,2:rewrite vec_plus_0; rewrite mat_plus_comm.
      1,2:rewrite mat_plus_0.
      1,2:rewrite (@eye_cc_split _ 1).
      1,2:f_equal. 1,3: apply col_0_0.
      apply L.
      apply R.
  Qed.

  Corollary Hstep_unitary: forall {n} (u: vec (S n)) (Q: sqmatrix n),
  u <> 0%Vec -> unitary Q -> unitary (HstepH u Q).
  Proof.
  unfold unitary, HstepH.
  intros. destruct (unistep_uni Q H1). unfold Lunitary, Runitary. split.
      all: rewrite herm_dist.
      all: rewrite Hh_H.
      all: rewrite mat_mult_mat_mat_assoc.
      1: rewrite <- (mat_mult_mat_mat_assoc H).
      2: rewrite <- (mat_mult_mat_mat_assoc _ _ H).
      { rewrite HH_I. rewrite mat_mult_I. 2: auto. apply H2. }
      rewrite H3. rewrite mat_mult_I. apply HH_I. apply H0.
  Qed.

  Fixpoint Householder {n m} (A: matrix n m):
  sqmatrix n.
  destruct n, m.
    - apply [].
    - apply [].
    - apply I.
    - pose (x:= hc A).
      destruct (vec_eq_dec x 0%Vec).
      + apply (canon_e O :: col 0%Vec ++' (Householder _ _ (tl (tc A)))).
      + destruct (Ceq_dec (hd x) 0%C).
        * pose (a := (Vnorm x)%R).
          pose (u := (x + a * canon_e O)%Vec).
          pose (HH := @H (S n) u).
          apply (HstepH u (Householder n m (tl (tc (HH @@ A))))).
        * pose (a := (hd x * (Vnorm x * / Cnorm (hd x))%R)%C).
          pose (u := (x + a * canon_e O)%Vec).
          pose (HH := @H (S n) u).
          apply (HstepH u (Householder n m (tl (tc (HH @@ A))))).
  Defined.

  Theorem Householder_unitary: forall {n m}
  (A: matrix n m),
  unitary (Householder A).
  Proof. unfold unitary. unfold Lunitary, Runitary. induction n; intros; split.
    1,2: trivial.
    all: destruct m; auto.
    1,3: rewrite (eta0_col A).
    1,2: cbn. rewrite dot_0.
    - f_equal. f_equal. lca.
      rewrite (@eye_cc_split _ 1).
      rewrite <- col_0_0. rewrite hc_col, tc_col.
      change ((mapvec (fun x : C => (x ^*)%C) 0%Vec)) with ((0%Vec: vec n)^*)%Vec.
      rewrite vec_conj_0.
      change ((mapmat
            (fun x : vec (S n) => (x ^*)%Vec)
            (tM (0%Vec :: I)))) with (([0%Vec] ++ (I: sqmatrix n))^*).
      rewrite herm_app_dist.
      rewrite row_tm_col.
      rewrite <- col_conj.
      rewrite tc_col. rewrite mat_mult_mat_more_mat.
      simpl. rewrite hc_col, tc_col.
      rewrite hermit_I.
      rewrite mat_mult_I_r.
      change ([0%Vec]) with (0: matrix 1 n).
      rewrite mat_mult_mat_0_r.
      rewrite mat_plus_comm.
      rewrite mat_plus_0. trivial.
      rewrite (@eye_cc_split _ 1). f_equal.
      rewrite <- col_0_0. rewrite tc_col.
      change ((mapmat
            (fun x : vec (S n) => (x ^*)%Vec)
            (tM (0%Vec :: I)))) with (([0%Vec] ++ (I: sqmatrix n))^*).
      rewrite mat_tm_app_dist.
      rewrite row_tm_col.
      rewrite mat_conj_split_col.
      rewrite <- col_conj.
      rewrite hc_col.
      rewrite mat_mult_col.
      simpl hd. rewrite hc_col.
      rewrite vec_0_mult.
      simpl tl. rewrite vec_conj_0.
      rewrite mat_mult_zeros. f_equal.
      apply vec_plus_0.
      rewrite <- col_0_0.
      rewrite hc_col, tc_col.
      change ((mapvec (fun x : C => (x ^*)%C) 0%Vec))
      with (0%Vec^*: vec n)%Vec.
      rewrite vec_conj_0.
      change ((mapmat
            (fun x : vec (S n) => (x ^*)%Vec)
            (tM (0%Vec :: I)))) with (([0%Vec] ++ (I: sqmatrix n))^*).
      rewrite herm_app_dist.
      rewrite row_tm_col.
      rewrite <- col_conj.
      rewrite tc_col.
      rewrite hermit_I.
      rewrite mat_mult_mat_more_mat.
      simpl hd. simpl tl.
      rewrite tc_col, hc_col.
      change ([0%Vec]) with (0: matrix 1 n).
      rewrite mat_mult_mat_0_r.
      rewrite mat_mult_I_r.
      rewrite mat_plus_comm.
      rewrite mat_plus_0. trivial.
    - rewrite (@eye_cc_split _ 1).
      rewrite <- col_0_0.
      rewrite hc_col, tc_col.
      change ((mapvec (fun x : C => x ^*)%C 0%Vec))
      with (0%Vec^*: vec n)%Vec. rewrite vec_conj_0.
      rewrite dot_0.
      f_equal. f_equal. lca.
      change (mapmat (fun x : vec (S n) => (x ^*)%Vec)
         (tM (0%Vec :: I))) with (([0%Vec] ++ (I: sqmatrix n))^*).
      rewrite herm_app_dist.
      rewrite mat_mult_mat_more_mat.
      simpl hd. rewrite row_tm_col.
      rewrite <- col_conj.
      rewrite hc_col, tc_col.
      change ([0%Vec]) with (0: matrix 1 n).
      rewrite mat_mult_mat_0_r.
      rewrite mat_mult_I_r.
      rewrite mat_plus_comm. rewrite mat_plus_0.
      trivial.
      f_equal. f_equal.
      rewrite mat_mult_col.
      simpl. rewrite mat_mult_zeros.
      rewrite vec_plus_0.
      rewrite vec_mult_1.
      1,2: change ((mapmat (fun x : vec (S n) => (x ^*)%Vec) (tM (0%Vec :: I))))
        with (([0%Vec] ++ (I: sqmatrix n))^*).
      1,2:rewrite herm_app_dist.
      rewrite row_tm_col.
      rewrite <- col_conj. rewrite hc_col.
      apply vec_conj_0.
      rewrite mat_mult_mat_more_mat.
      simpl hd. simpl tl.
      rewrite mat_mult_I_r.
      rewrite row_tm_col.
      rewrite <- col_conj.
      rewrite tc_col.
      change ([0%Vec]) with (0: matrix 1 n).
      rewrite mat_mult_mat_0_r.
      rewrite mat_plus_comm.
      rewrite mat_plus_0. simpl. apply hermit_I.
    - unfold Householder. destruct (vec_eq_dec (hc A) 0%Vec).
      fold (@Householder n m).
      destruct (unistep_uni (Householder (tl (tc A))) (IHn _ _)).
      auto.
      destruct (Ceq_dec (hd (hc A)) 0%C).
      all: fold (@Householder n m).
      pose (x:= (hc A + Vnorm (hc A) * canon_e 0)%Vec).
      fold x.
      pose (Q:= (Householder (tl (tc ((@H _ x) @@ A))))).
      fold Q.
      assert (F:= Hstep_unitary x Q).
      assert (x <> 0%Vec).
      { intros G. subst x.
      apply (f_equal hd) in G.
      rewrite vec_hd_plus_dist in G.
      simpl in G. rewrite e in G.
      rewrite Cplus_0_l in G. rewrite Cmult_1_r in G.
      destruct (vnorm_iff_0 (hc A)). apply n0. apply H1. inversion G; subst. auto.  } 
      apply (F H0).
      apply IHn.
      pose (x := (hc A +
   (hd (hc A) * (Vnorm (hc A) * /
   Cnorm (hd (hc A)))%R)%C * canon_e 0)%Vec).
      fold x.
      pose (Q:= (Householder (tl (tc ((@H _ x) @@ A))))).
      fold Q.
      assert (F:= Hstep_unitary x Q).
      assert (x <> 0%Vec).
      { clear F Q. intros F.
        apply n1.
        assert (tl (hc A) = 0%Vec).
        { apply (f_equal tl) in F.
          subst x. rewrite vec_tl_plus_dist in F.
          rewrite vec_tl_scalar in F.
          simpl tl in F. rewrite vec_0_mult in F.
          rewrite  vec_plus_0 in F. apply F. }
        apply (f_equal hd) in F.
        subst x. rewrite vec_hd_plus_dist in F.
        simpl in F. rewrite ! Rmult_1_r in F.
        unfold Vnorm in F.
        rewrite (eta (hc A)) in F.
        simpl in F. rewrite ! Rmult_1_r in F.
        pose (a := fst (hd (hc A))). fold a in F.
        pose (b := snd (hd (hc A))). fold b in F.
        rewrite Cmult_1_r in F.
        destruct (vcnorm_iff_0 (tl (hc A))) as [T _].
        specialize (T H0). rewrite T in F.
        rewrite Rplus_0_r in F.
        rewrite Rinv_r in F.
        rewrite Cmult_1_r in F.
        replace (hd (hc A) + hd (hc A))%C 
        with (2 * (hd (hc A)))%C in F by lca.
        assert (forall c: C, (2 * c = 0 -> c = 0)%C).
        { intros. assert (fst c = 0%R).
          { destruct c. simpl.
            cbv in H1. assert (D:=f_equal fst H1).
          simpl in D. lra. }
          assert (snd c = 0%R).
          { cbv in H1. assert (D:=f_equal snd H1).
            simpl in D. destruct c. simpl in H2.
            rewrite H2 in D. simpl. rewrite Rmult_0_l in D.
            rewrite Rplus_0_r in D. lra. }
          lca. }
        apply H1. apply F.
        intros G.
        apply n1.
        apply (f_equal (fun x => x²)) in G.
        rewrite Rsqr_sqrt in G.
        replace (0²) with 0%R in G.
        replace (a * a + b * b)%R
        with (a² + b²)%R in G.
        assert (RR:= Rle_0_sqr a).
        assert (RF:= Rle_0_sqr b).
        assert (DL:=Rplus_eq_0_l _ _ RR RF G).
        rewrite Rplus_comm in G.
        assert (DD:=Rplus_eq_0_l _ _ RF RR G).
        assert (CC:=Rsqr_eq_0 _ DL).
        assert (CD:= Rsqr_eq_0 _ DD).
        subst a b.
        lca. cbv. lra. cbv. lra.
        apply Rplus_le_le_0_compat.
        change (a * a)%R with (a²).
        apply Rle_0_sqr.
        change (b * b)%R with (b²).
        apply Rle_0_sqr.
     } apply (F H0). apply IHn.
    - unfold Householder. destruct (vec_eq_dec (hc A) 0%Vec).
      fold (@Householder n m).
      destruct (unistep_uni (Householder (tl (tc A))) (IHn _ _)).
      auto.
      destruct (Ceq_dec (hd (hc A)) 0%C).
      all: fold (@Householder n m).
      pose (x:= (hc A + Vnorm (hc A) * canon_e 0)%Vec).
      fold x.
      pose (Q:= (Householder (tl (tc ((@H _ x) @@ A))))).
      fold Q.
      assert (F:= Hstep_unitary x Q).
      assert (x <> 0%Vec).
      { intros G. subst x.
      apply (f_equal hd) in G.
      rewrite vec_hd_plus_dist in G.
      simpl in G. rewrite e in G.
      rewrite Cplus_0_l in G. rewrite Cmult_1_r in G.
      destruct (vnorm_iff_0 (hc A)). apply n0. apply H1. inversion G; subst. auto.  } 
      apply (F H0).
      apply IHn.
      pose (x := (hc A +
   (hd (hc A) * (Vnorm (hc A) * /
   Cnorm (hd (hc A)))%R)%C * canon_e 0)%Vec).
      fold x.
      pose (Q:= (Householder (tl (tc ((@H _ x) @@ A))))).
      fold Q.
      assert (F:= Hstep_unitary x Q).
      assert (x <> 0%Vec).
      { clear F Q. intros F.
        apply n1.
        assert (tl (hc A) = 0%Vec).
        { apply (f_equal tl) in F.
          subst x. rewrite vec_tl_plus_dist in F.
          rewrite vec_tl_scalar in F.
          simpl tl in F. rewrite vec_0_mult in F.
          rewrite  vec_plus_0 in F. apply F. }
        apply (f_equal hd) in F.
        subst x. rewrite vec_hd_plus_dist in F.
        simpl in F. rewrite ! Rmult_1_r in F.
        unfold Vnorm in F.
        rewrite (eta (hc A)) in F.
        simpl in F. rewrite ! Rmult_1_r in F.
        pose (a := fst (hd (hc A))). fold a in F.
        pose (b := snd (hd (hc A))). fold b in F.
        rewrite Cmult_1_r in F.
        destruct (vcnorm_iff_0 (tl (hc A))) as [T _].
        specialize (T H0). rewrite T in F.
        rewrite Rplus_0_r in F.
        rewrite Rinv_r in F.
        rewrite Cmult_1_r in F.
        replace (hd (hc A) + hd (hc A))%C 
        with (2 * (hd (hc A)))%C in F by lca.
        assert (forall c: C, (2 * c = 0 -> c = 0)%C).
        { intros. assert (fst c = 0%R).
          { destruct c. simpl.
            cbv in H1. assert (D:=f_equal fst H1).
          simpl in D. lra. }
          assert (snd c = 0%R).
          { cbv in H1. assert (D:=f_equal snd H1).
            simpl in D. destruct c. simpl in H2.
            rewrite H2 in D. simpl. rewrite Rmult_0_l in D.
            rewrite Rplus_0_r in D. lra. }
          lca. }
        apply H1. apply F.
        intros G.
        apply n1.
        apply (f_equal (fun x => x²)) in G.
        rewrite Rsqr_sqrt in G.
        replace (0²) with 0%R in G.
        replace (a * a + b * b)%R
        with (a² + b²)%R in G.
        assert (RR:= Rle_0_sqr a).
        assert (RF:= Rle_0_sqr b).
        assert (DL:=Rplus_eq_0_l _ _ RR RF G).
        rewrite Rplus_comm in G.
        assert (DD:=Rplus_eq_0_l _ _ RF RR G).
        assert (CC:=Rsqr_eq_0 _ DL).
        assert (CD:= Rsqr_eq_0 _ DD).
        subst a b.
        lca. cbv. lra. cbv. lra.
        apply Rplus_le_le_0_compat.
        change (a * a)%R with (a²).
        apply Rle_0_sqr.
        change (b * b)%R with (b²).
        apply Rle_0_sqr.
     } apply (F H0). apply IHn.
  Qed.

  Lemma hc_rank_uno: forall {n m} (u: vec (n))
  (v: vec (S m)),
    hc (col u @@ [v^*]%Vec) = ((hd v)^*%C * u)%Vec.
  Proof. intros. rewrite (eta v).
  simpl. rewrite hc_col. rewrite mat_mult_col.
  simpl tl. rewrite mat_mult_vec_empty.
  rewrite vec_plus_0. rewrite vec_hc_col. trivial.
  Qed.

  Lemma Hooo: forall {n} (x: vec (S n)),
  (hd x)%Vec = 0%C -> x <> 0%Vec ->
  (@H (S n) (x + Vnorm x * canon_e O) @ x = (-Vnorm x)%R * canon_e O)%Vec.
  Proof. intros. unfold H.
    rewrite mat_mat_dist.
    rewrite mat_mult_mat_vec_assoc.
    rewrite vec_mult_I.
    simpl ([_] @ x).
    rewrite dot_conj_dist.
    rewrite <- dot_mult_commute.
    rewrite dot_dist_l.
    rewrite vcnorm2_dotC.
    rewrite <- dot_mult_commute.
    rewrite (eta x).
    rewrite dot_step.
    simpl tl. simpl hd. rewrite Cmult_1_l.
    rewrite dot_0.
    rewrite Cplus_0_r. simpl canon_e.
    replace ((hd x :: tl x) +
        Vnorm (hd x :: tl x) * (1%C :: 0))%Vec
    with (RtoC (Vnorm (tl x)) :: tl x)%Vec.
    2:{ cbn. rewrite H0. fold (@plusvecs n).
    change (mapvec
      (fun x0 : C => (Vnorm (0 :: tl x) * x0)%C)
      0)%Vec with ((Vnorm (0%C :: tl x))%R * (0: vec n))%Vec.
    rewrite vec_0_mult. rewrite vec_plus_0.
    f_equal. unfold Vnorm.
    rewrite Cplus_0_l. rewrite Cmult_1_r.
    f_equal. f_equal.
    simpl. lra. }
    rewrite H0.
    rewrite vnorm_0_step.
    rewrite vcnorm_0_step.
    rewrite Cconj_0.
    rewrite Cmult_0_r. rewrite Cplus_0_r.
    replace (/ Vnorm (RtoC(Vnorm (tl x)) :: tl x))%R
    with (/ (sqrt 2 *  Vnorm (tl x)))%R.
    2:{ f_equal. unfold Vnorm. simpl.
      rewrite Rmult_0_l. rewrite Rmult_1_r.
      rewrite Rplus_0_r.
      rewrite <- sqrt_mult.
      2: lra.
      f_equal. rewrite sqrt_def. lra.
      all: apply vcnorm_pos.
    }
      replace ((/ (sqrt 2 * Vnorm (tl x)))%R *
    Vcnorm2 (tl x))%R with
      (Vnorm (tl x) * / (sqrt 2))%R.
    2:{ unfold Vnorm.
      rewrite <- sqrt_inv by lra.
      rewrite <- ! sqrt_mult.
      2, 5: lra.  2,3: apply vcnorm_pos.
      rewrite <- sqrt_inv.
      2:{ destruct (notvcnorm_iff_0 (tl x)).
      assert (tl x <> 0%Vec). { intros F.
      apply H1. rewrite (eta x). rewrite H0. rewrite F. apply eta. }
      specialize (H2 H4).
      clear H3 H0. assert (B:= vcnorm_pos (tl x)).
      lra. }
      replace ((sqrt (/ (2 * Vcnorm2 (tl x))) * Vcnorm2 (tl x)))%R
      with (sqrt (/ (2 * Vcnorm2 (tl x)) * Vcnorm2 (tl x) * Vcnorm2 (tl x))).
      2:{ rewrite Rmult_assoc.
          rewrite sqrt_mult.
          f_equal.
          rewrite sqrt_mult.
          apply sqrt_def.
          1,2,3: apply vcnorm_pos.
          assert (A:=vcnorm_pos (tl x)).
          destruct (notvcnorm_iff_0 (tl x)).
          assert (tl x <> 0%Vec). { intros F.
          apply H1. rewrite (eta x). rewrite H0. rewrite F. apply eta. }
          specialize (H2 H4).
          clear H3 H0. assert (0 < Vcnorm2 (tl x)) by lra.
          left.
          apply Rinv_0_lt_compat. lra.
          apply Rmult_le_pos.
          all: apply vcnorm_pos.
        }
      f_equal.
      rewrite Rinv_mult_distr.
      2: lra.
      rewrite (Rmult_assoc (/ 2)).
      rewrite Rinv_l. rewrite Rmult_1_r.
      lra. all: apply notvcnorm_iff_0.
      all: intros F. all: apply H1.
      all: rewrite (eta x), H0, F. all: trivial.
      }
      replace ((/ (sqrt 2 * Vnorm (tl x)))%R *
    Vcnorm2 (tl x))%C with (Vnorm (tl x) * / sqrt 2)%C.
    2:{
      assert (forall (a b: R), (RtoC a * RtoC b = RtoC (a * b)%R)%C).
      { intros. lca. }
      assert (forall (a: R), a <> 0%R -> Cinv (RtoC a) = RtoC (Rinv a)).
      { intros. cbv. rewrite Rmult_1_r. rewrite Rmult_0_l.
        rewrite Rplus_0_r. change (R0) with 0%R. rewrite Ropp_0.
        rewrite Rmult_0_l. f_equal.
        rewrite Rinv_mult_distr.
        rewrite <- Rmult_assoc.
        apply Rinv_r_simpl_r.
        all: auto.
      }
      rewrite ! H2. rewrite H3.
      2: apply sqrt2_neq_0.
      assert (forall (a b: R), a = b -> RtoC a = RtoC b).
      { intros. lca. }
      rewrite H2.
      apply H4.
      replace (/ (sqrt 2 * Vnorm (tl x)) * Vcnorm2 (tl x))%R
      with (/ Vnorm (tl x) * Vcnorm2 (tl x) * / sqrt 2)%R.
    2:{ rewrite Rinv_mult_distr.
        lra. apply sqrt2_neq_0. apply (notvnorm_iff_0).
        intros F. apply H1. rewrite (eta x). rewrite H0, F. trivial. }
     f_equal.
      replace (Vcnorm2 (tl x))%R with
      (sqrt (Vcnorm2 (tl x)) * sqrt (Vcnorm2 (tl x)))%R.
      2:{ apply sqrt_def. apply vcnorm_pos. }
      rewrite <- Rmult_assoc.
      unfold Vnorm.
      assert (0 < Vcnorm2 (tl x))%R.
      { assert (Vcnorm2 (tl x) <> 0)%R.
        apply notvcnorm_iff_0. intros F. apply H1. rewrite (eta x). rewrite H0, F. trivial.
        assert (A:=vcnorm_pos (tl x)).
        lra.
      }
      rewrite Rinv_l. lra.
      intros F. assert (G:=sqrt_eq_0 (Vcnorm2 (tl x))).
      specialize (G (vcnorm_pos _) F).
      rewrite G in H5. lra.
      }
      replace (((Vnorm (tl x) * / sqrt 2) ^*)%C) with
      (RtoC (Vnorm (tl x) * / sqrt 2)%R).
      2:{ rewrite Cconj_mult_distr.
      replace ((/ sqrt 2) ^*)%C with (RtoC (/ sqrt 2)%R).
    2:{
      assert (forall (a: R), a <> 0%R -> Cinv (RtoC a) = RtoC (Rinv a)).
      { intros. cbv. rewrite Rmult_1_r. rewrite Rmult_0_l.
        rewrite Rplus_0_r. change (R0) with 0%R. rewrite Ropp_0.
        rewrite Rmult_0_l. f_equal.
        rewrite Rinv_mult_distr.
        rewrite <- Rmult_assoc.
        apply Rinv_r_simpl_r.
        all: auto.
      } rewrite H2. 2: apply sqrt2_neq_0.
        lca.
    } assert (forall (a: R), (RtoC a)^* = RtoC a)%C.
      { intros. lca. }
     rewrite H2. lca.
    } rewrite mat_mult_col.
      simpl tl. rewrite mat_mult_vec_empty.
      rewrite vec_plus_0.
      rewrite mat_hc_scalar.
      rewrite vec_hc_col.
      simpl hd.
      rewrite ! vec_scalar_scalar.
      replace (((Vnorm (tl x) * / sqrt 2)%R * -2 *
  (/ (sqrt 2 * Vnorm (tl x)))%R)%C) with (RtoC (-1))%R.
      2:{ 
      assert (forall (a b: R), (RtoC a * RtoC b = RtoC (a * b)%R)%C).
      { intros. lca. } rewrite ! H2.
      replace ((Vnorm (tl x) * / sqrt 2 * -2 *
 / (sqrt 2 * Vnorm (tl x)))%R) with
      (/ sqrt 2 * -2 * Vnorm (tl x) * / (sqrt 2 * Vnorm (tl x)))%R by lra.
      rewrite Rinv_mult_distr.
      2: apply sqrt2_neq_0.
      rewrite (Rmult_comm _ (/ _)).
      rewrite <- Rmult_assoc.
      rewrite (Rmult_assoc _ (-2)).
      rewrite (Rmult_assoc (/ _)).
      rewrite Rinv_r_simpl_l.
      rewrite Rmult_comm.
      rewrite <- Rmult_assoc.
      rewrite <- Rinv_mult_distr.
      rewrite sqrt_def.
      rewrite (Ropp_mult_distr_r_reverse (/_) 2).
      lca. lra. 1,2: apply sqrt2_neq_0.
      all: apply notvnorm_iff_0.
      all: intros F. all: apply H1.
      all: rewrite (eta x). all: rewrite H0, F. all: auto.
    }
     cbn.
     fold (@plusvecs n (tl x)).
     fold (@multvec n (-1) (tl x)).
     fold (@multvec n (Vnorm (tl x)) 0%Vec).
     f_equal. lca.
     fold (@multvec n (- (Vnorm (tl x)))%R 0%Vec).
     rewrite vec_0_mult.
     assert (forall m (x: vec m), -1 * x = -x)%Vec.
     { induction m. intros. etaeta. intros. rewrite (eta x0).
      cbn. f_equal. lca. apply IHm. }
     rewrite H2.
     rewrite vec_plus_sub. apply vec_sub_sub.
  Qed.

  Lemma HooS: forall {n} (x: vec (S n)),
  (hd x)%Vec <> 0%C -> x <> 0%Vec ->
  (@H (S n) (x +
      (hd x *
       (Vnorm x * / Cnorm (hd x))%R)%C *
      canon_e 0)%Vec @ x = (- hd x * (Vnorm x * / Cnorm (hd x))%R)%C * canon_e O)%Vec.
  Proof. intros. unfold H.
    pose (u := ((x +
      (hd x *
       (Vnorm x * / Cnorm (hd x))%R)%C *
      canon_e 0))%Vec).
    fold u.
    rewrite mat_mat_dist.
    rewrite mat_mult_mat_vec_assoc.
    rewrite vec_mult_I.
    simpl ([_] @ x).
    rewrite dot_conj_dist.
    rewrite <- dot_mult_commute.
    change (dot u x) with (dot ((x +
      (hd x * (Vnorm x * / Cnorm (hd x))%R)%C *
      canon_e 0)%Vec) x).
    rewrite dot_dist_l.
    rewrite vcnorm2_dotC.
    rewrite <- dot_mult_commute.
    rewrite dot_step.
    simpl tl. simpl hd. rewrite Cmult_1_l.
    rewrite dot_0.
    rewrite Cplus_0_r. simpl canon_e.
    rewrite ! Cconj_mult_distr.
    rewrite ! Cconj_plus_distr.
    rewrite ! Cconj_mult_distr.
    rewrite Cconj_involutive.
    assert (forall (a b: R), (RtoC a * RtoC b = RtoC (a * b)%R)%C).
      { intros. lca. }
      assert (forall (a: R), a <> 0%R -> Cinv (RtoC a) = RtoC (Rinv a)).
      { intros. cbv. rewrite Rmult_1_r. rewrite Rmult_0_l.
        rewrite Rplus_0_r. change (R0) with 0%R. rewrite Ropp_0.
        rewrite Rmult_0_l. f_equal.
        rewrite Rinv_mult_distr.
        rewrite <- Rmult_assoc.
        apply Rinv_r_simpl_r.
        all: auto.
      }
    assert (forall x: C, 0 <= Cnorm2 x).
    { intros. unfold Cnorm2. apply (Rplus_le_le_0_compat _ _ (pow2_ge_0 _) (pow2_ge_0 _)). }
    assert (forall x: C, Cnorm2 x = 0 -> x = 0)%R.
    { intros. destruct x0. simpl in H5.
      rewrite ! Rmult_1_r in H5.
      assert (G:= Rplus_sqr_eq_0_l r r0).
      specialize (G H5).
      rewrite G. rewrite G in H5.
      rewrite Rmult_0_l in H5. rewrite Rplus_0_l in H5.
      assert (L:=Rsqr_eq_0 r0).
      specialize (L H5). rewrite L. trivial. }
    assert (Cnorm2 (hd x) <> 0%R).
    { intros A. apply H0. apply (H5 _ A). }
    assert (u <> 0%Vec).
    { unfold u. intros F%(f_equal hd).
      rewrite vec_hd_plus_dist in F.
      rewrite vec_hd_scalar in F.
      simpl hd in F. rewrite Cmult_1_r in F.
      replace (hd x + hd x * (Vnorm x * / Cnorm (hd x))%R)%C with
      (hd x * (1 + (Vnorm x * / Cnorm (hd x))))%C in F.
      2:{ rewrite Cmult_plus_distr_l.
      rewrite Cmult_1_r. f_equal.
      f_equal. rewrite H3. lca. unfold Cnorm.
      intros G. assert (D:= sqrt_eq_0 _ (H4 _) G).
      apply (H6 D). }
      assert (forall (a b: C), (a * b = 0 -> a = 0 \/ b = 0)%C).
      { intros. destruct (Ceq_dec a 0%C).
        left. apply e. right.
        apply (f_equal (fun x => (/ a) * x)%C) in H7.
        rewrite Cmult_0_r in H7.
        rewrite <- Cmult_assoc in H7.
        rewrite (Cinv_l _ n0) in H7.
        rewrite Cmult_1_l in H7. apply H7.
      }
    destruct (H7 _ _ F).
      - apply (H0 H8).
      - assert (forall (a b: R), (RtoC a + RtoC b = 0)%C -> (a + b = 0)%R).
        { intros. assert (L:=f_equal fst H9). simpl in L. apply L. }
        replace (Vnorm x * / Cnorm (hd x))%C with
        (RtoC(Vnorm x * / Cnorm (hd x))%R) in H8.
        specialize (H9 _ _ H8).
        assert (0 <= Vnorm x * / Cnorm (hd x))%R.
        { apply Fourier_util.Rle_mult_inv_pos. apply vnorm_pos.
          unfold Cnorm.
          assert (R:= sqrt_positivity).
          destruct (R _ (H4 (hd x))).
          apply H10. symmetry in H10. assert (L:=sqrt_eq_0 _ (H4 _) H10).
          contradiction.
        } lra.
      rewrite H3. rewrite H2. trivial.
      intros FF. unfold Cnorm in FF.
      assert (GG:=sqrt_eq_0 _ (H4 (hd x)) FF). lra.
    }

    replace ((Vcnorm2 x) ^*)%C with (RtoC (Vcnorm2 x)) by lca.
    replace ((Vnorm x * / Cnorm (hd x))%R ^*)%C
    with (RtoC ((Vnorm x * / Cnorm (hd x))%R)) by lca.
    replace ((/ Vnorm u)%R ^*)%C with (RtoC (/ Vnorm u)%R) by lca.
    replace ((hd x) ^* * (Vnorm x * / Cnorm (hd x))%R *
    hd x)%C with (RtoC (Cnorm (hd x) * Vnorm x)%R).
    2:{
      replace ((hd x) ^* * (Vnorm x * / Cnorm (hd x))%R *
 hd x)%C with ((hd x)^* * hd x * / Cnorm (hd x) * Vnorm x)%C.
    2:{ rewrite ! Cmult_assoc. f_equal.
        rewrite (Cmult_comm _ (hd x)).
        f_equal. rewrite Rmult_comm.
       rewrite H3. apply H2.
        intros F.
        assert (Cnorm2 (hd x) = 0)%R.
        { unfold Cnorm in F. apply (sqrt_eq_0 _ (H4 _) F). }
        apply H0. apply H5. apply H8.
      }
      rewrite Conj_mult_norm2.
      replace (Cnorm2 (hd x) * / Cnorm (hd x))%C
      with (RtoC (Cnorm (hd x)))%R.
      lca. unfold Cnorm.
      replace (Cnorm2 (hd x))%R with
      (sqrt (Cnorm2 (hd x) * Cnorm2 (hd x)))%R at 2.
      2:{ apply sqrt_square. apply H4. }
      rewrite H3.
      rewrite inv_sqrt.
      rewrite ! H2.
      rewrite <- sqrt_mult.
      f_equal. f_equal. symmetry.
      apply Rinv_r_simpl_m.
      intros F. apply H0.
      apply (H5 _ F).
      assert (P:=pow2_ge_0). simpl in P.
      specialize (P (Cnorm2 (hd x))).
      rewrite Rmult_1_r in P.
      apply P.
      rewrite <- Rmult_1_l.
      apply Rle_mult_inv_pos. lra.
      1,2:specialize (H4 (hd x)). 1,2:lra.
      intros F. apply H6. apply (sqrt_eq_0 _ (H4 _) F).
      }
      pose (xx:= ((Vcnorm2 x + (Cnorm (hd x) * Vnorm x)%R)%C)).
      fold xx.
      rewrite mat_mult_col. simpl tl.
      simpl hd.
      rewrite mat_mult_vec_empty.
      rewrite vec_plus_0.
      rewrite mat_hc_scalar.
      rewrite vec_hc_col.
      replace (((/ Vnorm u)%R * xx)%C *
 (-2 * ((/ Vnorm u)%R * u)))%Vec with
      ((-2 * / Vcnorm2 u * xx)%C * u)%Vec.
      2:{ rewrite ! vec_scalar_scalar. f_equal.
          rewrite (Cmult_assoc _ xx).
          rewrite (Cmult_comm xx).
          rewrite (Cmult_assoc _ (-2 * _)%C).
          rewrite (Cmult_assoc _ xx).
          rewrite (Cmult_comm xx).
          rewrite <- ! Cmult_assoc. f_equal.
          rewrite (Cmult_comm _ (-2)%C).
          rewrite Cmult_assoc. f_equal. rewrite H2.
          unfold Vnorm.
          rewrite <- Rinv_mult_distr.
          rewrite sqrt_def. apply H3.
          2: apply vcnorm_pos.
          apply notvcnorm_iff_0.
          apply H7.
          all: apply notvnorm_iff_0.
          all: apply H7.
        } replace (xx) with (RtoC ((Vcnorm2 u)) * / 2)%C.
          2:{ subst xx u.
              rewrite vcnorm_plus_dist.
              rewrite (Cmult_comm (hd x)).
              rewrite <- vec_scalar_scalar.
              rewrite vcnorm_scalarR.
          replace (Vcnorm2 (hd x * canon_e 0)%Vec) with
          (Cnorm2 (hd x))%R.
          2:{ simpl. fold (@multvec n (hd x)).
          rewrite vec_0_mult. replace (Vcnorm2 0%Vec) with 0%R.
          2:{ symmetry. apply vcnorm_iff_0. trivial. }
          lra. }
          replace ((Vnorm x * / Cnorm (hd x))² * Cnorm2 (hd x))%R
          with ((Vnorm x)²)%R.
          2:{ rewrite Rsqr_mult. unfold Cnorm.
              rewrite <- sqrt_inv.
              rewrite Rsqr_sqrt.
              rewrite Rmult_assoc. rewrite (Rmult_comm (/ _)).
              rewrite Rinv_r. 1,2:lra. left. apply Rinv_0_lt_compat.
              all: specialize (H4 (hd x)). all: lra.
            }
          replace ((Vnorm x)²)%R with (Vcnorm2 x)%R.
          2:{ unfold Vnorm. rewrite Rsqr_sqrt. auto. apply vcnorm_pos. }
          replace (Vcnorm2 x + Vcnorm2 x)%R
          with (Vcnorm2 x * 2)%R by lra.
          replace ((Vcnorm2 x * 2 +
  2 *
  fst
    (dot x
       ((Vnorm x * / Cnorm (hd x))%R *
        (hd x * canon_e 0))%Vec))%R * 
 / 2)%C with (RtoC (Vcnorm2 x +
  fst
    (dot x
       ((Vnorm x * / Cnorm (hd x))%R *
        (hd x * canon_e 0))%Vec))%R)%C by lca.
      rewrite dot_comm.
      rewrite <- dot_mult_commute.
      replace (dot (hd x * canon_e 0)%Vec x)%C with
      (RtoC (Cnorm2 (hd x))).
      2:{ rewrite dot_step.
      rewrite vec_hd_scalar.
      rewrite vec_tl_scalar. simpl hd. simpl tl.
      rewrite vec_0_mult. rewrite dot_0.
      lca. } rewrite ! H2.
      assert (forall (a b: R), (RtoC a + RtoC b)%C = ((RtoC (a + b))%R)).
      { intros. lca. }
      rewrite H8. f_equal. f_equal.
      replace (Cnorm2 (hd x)) with
      (Cnorm (hd x) * Cnorm (hd x))%R.
      2:{ unfold Cnorm. apply sqrt_def. apply H4. }
      rewrite <- Rmult_assoc.
      rewrite (Rmult_assoc (Vnorm _)).
      rewrite Rinv_l. rewrite Rmult_1_r.
      replace ((Vnorm x * Cnorm (hd x))%R ^*)%C with 
      (RtoC (Vnorm x * Cnorm (hd x))%R) by lca.
      rewrite Rmult_comm.
      simpl. lra.
      intros F. unfold Cnorm in F.
      assert (A:= sqrt_eq_0 _ (H4 _) F).
      apply (H6 A).
    } rewrite <- Cmult_assoc.
      rewrite (Cmult_assoc (-2)).
      rewrite H3. rewrite H2.
      rewrite Rinv_l. 2,3: apply notvcnorm_iff_0.
      2,3: apply H7.
      rewrite Cmult_1_r.
      rewrite H3 by lra. rewrite H2.
      rewrite <- (Ropp_mult_distr_l 2) by lra.
      rewrite (Rinv_r 2) by lra.
      unfold u. assert (forall (a b: R), (RtoC a + RtoC b)%C = ((RtoC (a + b))%R)).
      { intros. lca. }
      rewrite vec_mult_dist_r.
      rewrite <- (vec_plus_assoc x).
      replace ((- (1))%R) with (-1)%C by lra.
      assert (forall {m} (y:vec m), (-1) * y = - y)%Vec.
      { induction m. intros; etaeta. intros. rewrite (eta y).
        cbn. f_equal. lca. apply IHm. }
      rewrite ! H9.
      rewrite (vec_plus_sub x).
      rewrite (vec_sub_sub). rewrite vec_plus_comm.
      rewrite vec_plus_0.
      assert (forall (a: C) {m} (y: vec m),
        - (a * y) = (-a)%C * y)%Vec.
      { induction m; intros. etaeta.
        rewrite (eta y). cbn. f_equal. lca.
        apply IHm. }
      rewrite H10. f_equal. lca. Qed.

  Theorem Householder_upTri: forall {n m}
    (A: matrix n m),
  is_upTri ((Householder A) @@ A).
  Proof.
  induction n, m.
    1,2: intros; rewrite (eta0 (_ @@ _)); constructor.
    - intros. rewrite (eta0_col _). rewrite <- (eta0_col 0). constructor.
    - intros. unfold Householder.
      destruct (vec_eq_dec (hc A)).
      fold (@Householder n m).
      rewrite mat_mult_mat_row_step.
      rewrite mat_mult_col.
      simpl hd. simpl tl.
      rewrite vec_mult_1. rewrite mat_mult_zeros.
      rewrite vec_plus_0.
      rewrite mat_mult_mat_more_mat.
      rewrite hc_col, tc_col.
      rewrite col_0_0. rewrite mat_mult_mat_0.
      rewrite mat_plus_comm. rewrite mat_plus_0.
      rewrite mat_mult_mat_step.
      rewrite <- mat_tl_hc_commute.
      rewrite e. simpl tl. rewrite mat_mult_zeros.
      apply S_upTri. rewrite mat_tl_tc_commute. apply IHn.
      destruct (Ceq_dec (hd (hc A)) 0)%C.
      + fold (@Householder n m).
      pose (x := (hc A + (Vnorm (hc A))%R * canon_e 0)%Vec).
      fold x.
      unfold HstepH.
      rewrite mat_mult_mat_mat_assoc.
      rewrite (mat_mult_mat_step (@H (S n) x) A).
      rewrite tc_col.
      rewrite (mat_mult_mat_step _ A).
      replace (H @ (hc A)) with ((-Vnorm (hc A))%R * (@canon_e (S n) O))%Vec.
      2:{ symmetry. apply Hooo.
        apply e. apply n0.
      }
      rewrite mat_mult_mat_row_step.
      simpl hd. simpl tl.
      rewrite mat_tm_mult_vec.
      rewrite tc_col, hc_col.
      rewrite mat_mult_col. simpl hd.
      simpl tl.
      rewrite mat_mult_zeros.
      rewrite vec_plus_0.
      pose (f:=(dot ((- Vnorm (hc A))%R * canon_e 0)%Vec
      ((1%C :: (0: vec n)) ^*)%Vec)%Vec).
      change (dot ((- Vnorm (hc A))%R * canon_e 0)%Vec
      ((1%C :: (0: vec m)) ^*)%Vec)%Vec with f.
      rewrite vec_mult_1.
      rewrite (mat_mult_mat_more_mat (col _ ++' _)).
      rewrite tc_col, hc_col.
      simpl hd. simpl tc.
      rewrite (mat_tl_cc_dist (col _)).
      rewrite vec_tl_col_commute.
      rewrite (vec_tl_scalar _ (canon_e O)).
      simpl tl.
      rewrite vec_0_mult.
      rewrite Cmult_1_r.
      rewrite col_0_0.
      rewrite mat_mult_mat_0.
      rewrite mat_plus_comm.
      rewrite mat_plus_0.
      rewrite <- col_0_0.
      rewrite (mat_mult_mat_step _ (col _ ++' _)).
      rewrite hc_col, tc_col.
      rewrite mat_mult_zeros.
      apply S_upTri.
      apply IHn.
      + fold (@Householder n m).
      pose (x := (hc A +
      (hd (hc A) *
       (Vnorm (hc A) * / Cnorm (hd (hc A)))%R)%C *
      canon_e 0)%Vec).
      fold x.
      unfold HstepH.
      rewrite mat_mult_mat_mat_assoc.
      rewrite (mat_mult_mat_step (@H (S n) x) A).
      rewrite tc_col.
      rewrite (mat_mult_mat_step _ A).
      replace (H @ (hc A)) with ((- hd (hc A) * (Vnorm (hc A) * / Cnorm (hd (hc A)))%R)%C * (@canon_e (S n) O))%Vec.
      2:{ symmetry. apply HooS.
        apply n1. apply n0.
      }
      rewrite mat_mult_mat_row_step.
      simpl hd. simpl tl.
      rewrite mat_tm_mult_vec.
      rewrite tc_col, hc_col.
      rewrite mat_mult_col. simpl hd.
      simpl tl.
      rewrite mat_mult_zeros.
      rewrite vec_plus_0.
      pose (f:=(dot ((- Vnorm (hc A))%R * canon_e 0)%Vec
      ((1%C :: (0: vec n)) ^*)%Vec)%Vec).
      change (dot ((- Vnorm (hc A))%R * canon_e 0)%Vec
      ((1%C :: (0: vec m)) ^*)%Vec)%Vec with f.
      rewrite vec_mult_1.
      rewrite (mat_mult_mat_more_mat (col _ ++' _)).
      rewrite tc_col, hc_col.
      simpl hd. simpl tc.
      rewrite (mat_tl_cc_dist (col _)).
      rewrite vec_tl_col_commute.
      rewrite (vec_tl_scalar _ (canon_e O)).
      simpl tl.
      rewrite vec_0_mult.
      rewrite Cmult_1_r.
      rewrite col_0_0.
      rewrite mat_mult_mat_0.
      rewrite mat_plus_comm.
      rewrite mat_plus_0.
      rewrite <- col_0_0.
      rewrite (mat_mult_mat_step _ (col _ ++' _)).
      rewrite hc_col, tc_col.
      rewrite mat_mult_zeros.
      apply S_upTri.
      apply IHn.
  Qed.

End Householder.

Corollary QR_decomp: forall {n m} (A: matrix n m),
  exists (Q: sqmatrix n) (R: matrix n m),
    unitary Q /\ is_upTri R /\ A = Q @@ R.
Proof.
  intros. exists ((Householder A)^*), (Householder A @@ A).
  assert (unitary ((Householder A)^*)).
  { destruct (Householder_unitary A). split.
    1: unfold Runitary.
    2: unfold Lunitary.
    all: rewrite mat_herm_herm.
    all: assumption. }
  split. - apply H.
    - split.
      -- apply Householder_upTri.
      -- rewrite <- mat_mult_mat_mat_assoc.
         destruct H. unfold Runitary in H. rewrite mat_herm_herm in H.
         rewrite H.
         rewrite mat_mult_I. auto.
Qed.

Close Scope mat_scope.
Close Scope vec_scope.
Close Scope C_scope.