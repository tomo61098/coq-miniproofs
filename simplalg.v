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

  Hint Resolve P0: core.

  Lemma pred_increasing : forall n m,
      n <= m ->
      Nat.pred n <= Nat.pred m.
  Proof.
    induction n; cbn; intros.
    apply le_0_n.
    induction H; subst; cbn; eauto.
    destruct m; eauto.
  Qed.

  Hint Resolve le_S_n: core.

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

Require Import Lia.

Theorem induction_shift: forall (n0: nat) (P: nat -> Prop),
 (forall n, n0 <= n -> P n) <-> (forall n, P (n0 + n)).
Proof.
  intros.
  split.
    - intros. apply H. lia.
    - intros. specialize (H (n - n0)).
      replace (n0 + (n - n0)) with n in H.
      + apply H.
      + lia.
Qed.

Fixpoint Fibonacci (n: nat) :=
  match n with
    | 0 => 0
    | 1 => 1
    | S m => Fibonacci m + 
      match m with
        | 0 => 0
        | S m' => Fibonacci m'
      end
  end.

Lemma Fibonacci_step: forall (n: nat),
  Fibonacci (S (S n)) = Fibonacci (S n) + Fibonacci n.
Proof. intros. trivial. Qed.

Require Import PeanoNat Nat.
Import Nat.

Theorem simpl_grad: forall (Q: nat -> nat),
  (forall x: nat, Q (x + 1) <= Q x + Q 1)
  -> (forall (n x: nat), Q (x + n) <= Q x + n * Q 1).
Proof.
  induction n.
    - intuition.
      rewrite <- plus_n_O. lia.
    - intros.
      replace (x + S n) with (x + n + 1) by lia.
      rewrite H.
      replace (S n * Q 1) with (n * Q 1 + Q 1) by lia.
      rewrite add_assoc. apply add_le_mono_r.
      apply IHn.
Qed.

Goal forall (n: nat),
  Fibonacci n <= 2^n.
Proof. refine (fix f n :=
  match n with
    | O => _
    | 1 => _
    | S (S m) => _
  end).
  - simpl. lia.
  - simpl. lia.
  - rewrite Fibonacci_step.
    admit.
Admitted.

Require Import List.
Import ListNotations.

Fixpoint sum (A: list nat): nat :=
  match A with
    | x :: xs => x + sum xs
    | _ => O end.

Fixpoint elem (y: nat) (xs: list nat): bool :=
  match xs with
    | x::xs => if eqb x y then true else elem y xs
    | _ => false end.

Fixpoint distinct (A: list nat): nat :=
  match A with
    | x :: xs => (if elem x xs then 0 else 1) + distinct xs
    | _ => O end.

Goal forall (A: list nat) (m: nat),
  (sum A = m) -> (distinct A) ^ 2 <= m.
Proof.
  induction A; intuition.
  

Section EvenOdd.

Local Definition even (x: nat) := exists k, 2*k = x.
Local Definition odd (x: nat) := exists k, 2*k + 1 = x.

Theorem even_odd_induction:
  forall P: nat -> Prop,
  P 0 -> P 1 -> (forall n: nat, P n -> P (2 + n))
  -> (forall n: nat, P n).
Proof. intros P A B C.
  refine (fix f n :=
    match n with
      | O => A
      | S O => B
      | (S (S m)) => C m (f m)
    end).
Qed.

Tactic Notation "evenodd" "induction" ident(n) := induction n using even_odd_induction.

Lemma evenodd_dec: forall n: nat, even n \/ odd n.
Proof.
  evenodd induction n.
    1: left. 2: right.
    1,2: exists O.
    1,2: trivial.
    destruct IHn.
    1,2: destruct H.
    1: left. 2: right.
    1,2: exists (S x).
    1,2: simpl.
    all: lia.
Qed.

Goal forall P: nat -> Prop,
    (forall k, P (2*k)) ->
    (forall k, P (2*k + 1)) ->
    forall n, P n.
Proof.
  intros.
  destruct (evenodd_dec n).
  all:destruct H1.
    - rewrite <- H1.
      apply H.
    - rewrite <- H1.
      apply H0.
Qed.

Goal forall n: nat, even (n * (n+1)).
Proof.
  intros. destruct (evenodd_dec n).
    - destruct H.
      exists (x*(n + 1)).
      lia.
    - destruct H. rewrite <- H.
      exists ((2 * x + 1) * (x + 1)).
      lia.
Qed.

Goal forall a b: nat, even a -> even b ->
even (a+b).
Proof.
  intros a b [ka A] [kb B].
  exists (ka + kb).
  lia.
Qed.

Goal forall a b: nat, odd a -> odd b ->
even (a+b).
Proof.
  intros a b [ka A] [kb B].
  exists (ka + kb+1).
  lia.
Qed.

Goal forall n: nat, even n <-> odd (S n).
Proof.
  intros. split; intros [k A].
  all: exists k.
  all: lia.
Qed.

Goal forall n: nat, odd n -> even (S n).
Proof.
  intros n [k A].
  exists (S k); lia.
Qed.

Goal forall n: nat, even n -> even (2 + n).
Proof. intros n [k A]. exists (S k).
  lia.
Qed.

Goal forall n: nat, odd n -> odd (2 + n).
Proof. intros n [k A]. exists (S k).
  lia.
Qed.

Lemma l1: forall n: nat, even n -> forall x, even (x * n).
Proof.
  intros n [k A] x.
  exists (k * x). lia.
Qed.

Lemma l6: forall n m: nat, odd n -> odd m ->
odd (n * m).
Proof. intros n m [kn A] [km B].
  exists (2 * kn * km + kn + km).
  lia.
Qed.

Fixpoint div2 (n: nat): nat :=
  match n with
    | S (S m) => S (div2 m)
    | _ => O
  end.

Lemma l2: forall n: nat, even (2 + n) -> even n.
Proof.
  intros n [k A].
  exists (pred k).
  lia.
Qed.

Lemma l5: forall n: nat, div2 (2*n) = n.
Proof. induction n.
  - trivial.
  - rewrite (PeanoNat.Nat.mul_add_distr_l _ 1).
    simpl. simpl in IHn. f_equal. apply IHn.
Qed.

Lemma l5': forall n: nat, div2 (2*n + 1) = n.
Proof. induction n.
  - trivial.
  - rewrite (PeanoNat.Nat.mul_add_distr_l _ 1).
    simpl. simpl in IHn. f_equal. apply IHn.
Qed.

Goal forall n: nat, even n -> 2 * div2 n = n.
Proof. intros n [k A].
  rewrite <- A. rewrite l5. trivial.
Qed.

Lemma l7: forall n: nat, even n -> ~odd n.
Proof. intros n [ka A] [kb B]. (* lia. *)
  assert (ka = kb).
  { apply (f_equal div2) in A.
    apply (f_equal div2) in B.
    rewrite (l5 _) in A.
    rewrite (l5' _) in B.
    rewrite A, B. trivial.
  } rewrite H in A. rewrite A in B.
  rewrite plus_n_O in B.
  apply Plus.plus_reg_l in B.
  change (match O with | O => False | _ => True end).
  rewrite <- B. apply I.
Qed.

Corollary l7': forall n: nat, odd n -> ~even n.
Proof. intros n A F. apply (l7 n F A). Qed.

Lemma l3: forall n m: nat, even (n*m) ->
  even n \/ even m.
Proof. intros.
  destruct (evenodd_dec n).
    - left. apply H0.
    - right.
      destruct (evenodd_dec m).
      + apply H1.
      + apply (l6 _ _ H0) in H1.
        exfalso. apply (l7 _ H H1).
Qed.

Goal forall n: nat, even n -> (exists k, 3*k = n)
  -> (exists k, 6*k = n).
Proof.
  intros n A [kb B].
  rewrite <- B in A.
  destruct (l3 _ _ A).
    + destruct H. lia.
    + destruct H.
      rewrite <- H in B.
  exists x. rewrite <- B. lia.
Qed.

End EvenOdd.

Section Palindrome.

Inductive Palindrome {T: Type}: list T -> Prop :=
  | empty_pal: Palindrome []
  | singl_pal: forall x: T, Palindrome [x]
  | app_pal: forall (x: T) (xs: list T),
    Palindrome xs -> Palindrome ([x] ++ xs ++ [x]).

Lemma list_nat_nat_ind: forall (T: Type) (P: list T -> Prop),
  (P []) -> (forall n: nat,
    (forall xs: list T, length xs = n -> P xs) ->
      (forall xs: list T, length xs = S n -> P xs))
    -> (forall (n: nat) (xs: list T), length xs = n -> P xs).
Proof. intros T P A B n.
  induction n.
    - intros. apply length_zero_iff_nil in H. rewrite H. apply A.
    - intros. destruct xs.
      -- apply A.
      -- apply (B n).
      intros. apply IHn. apply H0.
      apply H.
Qed.

Lemma list_nat_ind: forall (T: Type) (P: list T -> Prop),
  (P []) -> (forall n: nat,
    (forall xs: list T, length xs = n -> P xs) ->
      (forall xs: list T, length xs = S n -> P xs))
    -> (forall (xs: list T), P xs).
Proof. intros T P A B.
  assert (F: (forall (n: nat) (ys: list T),
    length ys = n -> P ys) -> (forall ys: list T, P ys)).
  { intros. apply (H (length ys) _ (eq_refl _)). }
  apply F.
  apply list_nat_nat_ind; auto.
Qed.

Lemma len_last: forall (n: nat) (T: Type) (xs: list T),
  length xs = S n -> exists (y: T) (ys: list T), xs = ys ++ [y].
Proof. induction xs.
  - intros. simpl in H. congruence.
  - intros. simpl in H.

Lemma rev_ind: forall (T: Type) (P: list T -> Prop),
  (P []) -> (forall (x: T) (xs: list T), P xs -> P (xs ++ [x])) ->
  (forall xs: list T, P xs).
Proof. intros T P A B.
  apply list_nat_ind.
    - apply A.
    - intros. specialize (H (remove_last xs)).

Goal forall (T: Type) (xs: list T),
  Palindrome xs <-> rev xs = xs.
Proof. intros.
  split.
    - intros. induction H; trivial.
      simpl. rewrite rev_unit.
      simpl. rewrite IHPalindrome. trivial.
    - intros.
      induction xs.
      + apply empty_pal.
      + rewrite <- H. simpl.
        * simpl. apply singl_pal.
        * simpl.

End Palindrome.

Section Related.

End Related.

Section Group.

  Structure Group := make_group {
    group :> Set;
    opp: group -> group -> group ;
    inv: group -> group ;
    z: group ;
  plus_assoc: forall a b c: group, opp (opp a b) c = opp a (opp b c);
  plus_inv_l: forall a: group, opp (inv a) a = z;
  plus_inv_r: forall a: group, opp a (inv a) = z;
  plus_0_l: forall a: group, opp z a = a ;
  plus_0_r: forall a: group, opp a z = a ;
  }.

  Context {G: Group}.

  Arguments z {g}.
  Arguments opp {g} _ _.
  Arguments inv {g} _.
  Arguments plus_assoc {g} _ _ _.
  Arguments plus_inv_l {g} _.
  Arguments plus_inv_r {g} _.
  Arguments plus_0_l {g} _.
  Arguments plus_0_r {g} _.

  Local Notation "0" := (z).
  Local Infix "+" := (opp).
  Local Notation "- x" := (inv x).

  Theorem zero_unique: forall a: G,
    (forall b: G, a + b = b)
    -> a = 0.
  Proof.
    intros.
    rewrite <- (plus_0_r a).
    apply H.
  Qed.

  Theorem inv_zero: (@inv G 0) = 0.
  Proof.
    rewrite <- (plus_0_l (-0)).
    apply plus_inv_r.
  Qed.

  Lemma inverse3: forall (a b: G), - a + (a + b) = b.
  Proof.
    intros.
    rewrite <- plus_assoc, plus_inv_l.
    apply plus_0_l.
  Qed.

  Lemma inverse4: forall (a b: G), a + (- a + b) = b.
  Proof.
    intros.
    rewrite <- plus_assoc, plus_inv_r.
    apply plus_0_l.
  Qed.

  Hint Rewrite inverse3: core.
  Hint Rewrite inverse4: core.

  Lemma group_cancel_l: forall (a b c: G),
    a + b = a + c -> b = c.
  Proof. intros.
    rewrite <- (inverse3 a b).
    rewrite H.
    apply inverse3.
  Qed.

  Lemma group_cancel_r: forall (a b c: G),
    b + a = c + a -> b = c.
  Proof. intros.
    rewrite <- (plus_0_r b).
    rewrite <- (plus_inv_r a).
    rewrite <- plus_assoc. rewrite H.
    rewrite plus_assoc.
    rewrite plus_inv_r.
    apply plus_0_r.
  Qed.

  Lemma inv_unique_r: forall (a b: G),
    a + b = 0 -> b = -a.
  Proof.
    intros.
    rewrite <- (plus_0_r (-a)).
    rewrite <- H.
    symmetry.
    apply inverse3.
  Qed.

  Lemma inv_unique_l: forall (a b: G),
    a + b = 0 -> a = -b.
  Proof.
    intros.
    rewrite <- (plus_0_l (-b)).
    rewrite <- H. rewrite plus_assoc.
    rewrite plus_inv_r.
    symmetry. apply plus_0_r.
  Qed.

  Lemma plus_inv_commute: forall (a b: G),
    a + b = 0 <-> b + a = 0.
  Proof.
    intros.
    split.
      - intros.
        rewrite (inv_unique_l _ _ H).
        apply plus_inv_r.
      - intros.
        rewrite (inv_unique_l _ _ H).
        apply plus_inv_r.
  Qed.

  Theorem inverse_cancel:
    forall (a: G), - (- a) = a.
  Proof.
    intros.
    symmetry. apply inv_unique_l.
    apply plus_inv_r.
  Qed.

  Hint Rewrite inverse_cancel: core.

  Lemma inverse_cancel2:
    forall (a b: G), -a = -b -> a = b.
  Proof. intros.
    rewrite <- (inverse_cancel b).
    apply inv_unique_r.
    rewrite <- H. apply plus_inv_l.
  Qed.

  Hint Rewrite inverse3: core.
  Hint Rewrite inverse4: core.

  Hint Rewrite inverse_cancel: core.

  Lemma inverse_dist: forall (a b: G),
  -(a + b) = -b + -a.
  Proof.
    intros.
    symmetry.
    apply inv_unique_r.
    rewrite <- plus_assoc.
    rewrite (plus_assoc a b).
    rewrite plus_inv_r.
    rewrite plus_0_r.
    apply plus_inv_r.
  Qed.

  Lemma inverse_swap:
    forall (a b c: G),
      a = -b + c <-> b + a = c.
  Proof. intros.
    split.
      - intros.
        rewrite <- (inverse_cancel c).
        apply inv_unique_l.
        rewrite H. rewrite <- plus_assoc.
        rewrite plus_inv_r.
        rewrite plus_0_l.
        apply plus_inv_r.
      - intros.
        rewrite <- (inverse_cancel (_ + _)).
        rewrite inverse_dist.
        rewrite inverse_cancel.
        apply inv_unique_r.
        rewrite plus_assoc.
        rewrite H. apply plus_inv_l.
  Qed.
End Group.

Section Homomorphism.
  Context {G1 G2: Group}.

  Arguments z {g}.
  Arguments opp {g} _ _.
  Arguments inv {g} _.
  Arguments plus_assoc {g} _ _ _.
  Arguments plus_inv_l {g} _.
  Arguments plus_inv_r {g} _.
  Arguments plus_0_l {g} _.
  Arguments plus_0_r {g} _.


  Local Notation "0" := (z).
  Local Notation "0'" := (@z G2).
  Local Infix "+" := (opp).
  Local Infix "+'" := (@opp G2) (at level 50, left associativity).
  Local Notation "- x" := (inv x).
  Local Notation "-' x" := (@inv G2 x) (at level 35, right associativity).


  Variable f: G1 -> G2.
  Hypothesis homomorphism: (forall a b: G1, f (a + b) = f a +' f b).

  (* https://math.stackexchange.com/questions/1877444/proving-that-a-group-homomorphism-preserves-the-identity-element
     https://math.stackexchange.com/questions/647697/tricks-prove-homomorphism-maps-identity-to-identity-fraleigh-p-128-theorem *)

  Theorem homo_0:
    f 0 = 0'.
  Proof.
  apply (group_cancel_l (f 0)).
  rewrite <- homomorphism.
  rewrite plus_0_l. symmetry.
  apply inverse_swap. symmetry.
  apply plus_inv_l.
  Qed.

  Theorem homo_inv: forall a: G1,
    f (-a) = -' (f a).
  Proof.
  intros.
  apply inv_unique_l.
  rewrite <- homomorphism.
  rewrite plus_inv_l. apply homo_0.
  Qed.

  Goal forall a b c: G1,
    f (a + b) +' f c = f a +' f (b + c).
  Proof.
    intros. rewrite ! homomorphism.
    apply plus_assoc. Qed.

  (* Ker is subgroup *)

  Goal forall a b: G1,
    (f a = 0') /\ (f b = 0') -> f (a + b) = 0'.
  Proof.
    intros a b [A B].
    rewrite homomorphism.
    rewrite A, B.
    apply plus_0_l.
  Qed.

End Homomorphism.

Section Ring.

  Arguments z {g}.
  Arguments opp {g} _ _.
  Arguments inv {g} _.
  Arguments plus_assoc {g} _ _ _.
  Arguments plus_inv_l {g} _.
  Arguments plus_inv_r {g} _.
  Arguments plus_0_l {g} _.
  Arguments plus_0_r {g} _.


  Local Notation "0" := (z).
  Local Infix "+" := (opp).
  Local Notation "- x" := (inv x).


  Structure Ring := make_ring {
    ring :> Group ;
    plus_comm: forall a b: ring, a + b = b + a ;
    opp2: ring -> ring -> ring ;
    e: ring ;
    mult_1_l: forall a: ring, opp2 e a = a ;
    mult_1_r: forall a: ring, opp2 a e = a ;
    mult_assoc: forall a b c: ring, opp2 (opp2 a b) c = opp2 a (opp2 b c) ;
    mult_dist_l: forall a b c: ring, opp2 a (b + c) = opp2 a b + opp2 a c ;
    mult_dist_r: forall a b c: ring, opp2 (a + b) c = opp2 a c + opp2 b c ;
  }.

  Arguments e {r}.
  Arguments opp2 {r} _ _.
  Arguments plus_comm {r} _ _.
  Arguments mult_1_l {r} _.
  Arguments mult_1_r {r} _.
  Arguments mult_dist_l {r} _ _ _.
  Arguments mult_dist_r {r} _ _ _.

  Local Notation "1" := e.
  Local Infix "*" := opp2.

  Context {R: Ring}.

  Theorem mult_0_l: forall a: R, 0 * a = 0.
  Proof. intros.
    rewrite <- (plus_inv_l a) at 2.
    rewrite inverse_swap.
    rewrite <- (mult_1_l a) at 1.
    rewrite <- mult_dist_r.
    rewrite plus_0_r.
    apply mult_1_l.
  Qed.

  Theorem mult_0_r: forall a: R, a * 0 = 0.
  Proof. intros.
    rewrite <- (plus_inv_l a) at 2.
    rewrite inverse_swap.
    rewrite <- (mult_1_r a) at 1.
    rewrite <- mult_dist_l.
    rewrite plus_0_r.
    apply mult_1_r.
  Qed.

  Theorem trivial_ring:
    0 = (@e R) -> forall a: R, a = 0.
  Proof.
    intros.
    rewrite <- (mult_0_r a).
    rewrite H. symmetry.
    apply mult_1_r.
  Qed.

  (* https://math.stackexchange.com/questions/2239445/proving-unity-is-unique *)

  Theorem one_unique: forall a: R,
    (forall b: R, a * b = b) -> a = 1.
  Proof. intros.
    rewrite <- (mult_1_r a).
    apply H.
  Qed.

  Lemma mult_inv_r : forall a b: R,
  a * (-b) = - (a * b).
  Proof.
    intros.
    apply inv_unique_r.
    rewrite <- mult_dist_l.
    rewrite plus_inv_r.
    apply mult_0_r.
  Qed.

  Lemma mult_inv_l : forall a b: R,
    (-a) * b = - (a * b).
  Proof.
    intros.
    apply inv_unique_r.
    rewrite <- mult_dist_r.
    rewrite plus_inv_r.
    apply mult_0_l.
  Qed.

  Hint Rewrite mult_inv_r: core.
  Hint Rewrite mult_inv_l: core.

  Corollary mult_inv_inv: forall a b: R,
    (-a) * (-b) = a * b.
  Proof. intros. rewrite mult_inv_l.
  rewrite mult_inv_r. apply inverse_cancel.
  Qed.

End Ring.


Require Import Lra Reals.
Import Reals.

Open Scope R_scope.

Goal forall H: R -> R,
  (forall (x y: R), H (x + y) = H x * H y)
  -> ~(forall y: R, exists x, H x = y).
Proof.
  intros H T.
  assert (A0: H 0 * H 0 = H 0 * 1).
  { rewrite <- T. rewrite Rplus_0_r. intuition. }
  assert (A1: forall c: R, H c * H 0 = H c).
  { intros. rewrite <- T. intuition. }
  destruct (Req_EM_T (H 0) 0).
    + assert (forall c: R, H c = 0).
      { intros. specialize (A1 c). rewrite e in A1.
        rewrite <- (Rmult_0_r (H c)). intuition. }
      intros B.
      specialize (B 1) as [x B].
      rewrite H0 in B. intuition.
   +  assert (H 0 = 1).
      { apply (Rmult_eq_reg_l (H 0)); auto. }
      assert (A2: forall c: R, H c * H (-c) = 1).
      { intros. rewrite <- T. rewrite Rplus_opp_r. auto. }
      intros B.
      specialize (B 0) as [x B].
      specialize (A2 x).
      rewrite B in A2. rewrite Rmult_0_l in A2.
      intuition.
Qed.

Goal forall H: R -> R,
  (forall (x y: R), H (x + y) = H x * H y)
  -> (forall x y: R, H x = H y -> x = y) <-> H 0 = 1 /\ forall x: R, x <> 0 -> H x <> 1.
Proof.
  intros H T.
  assert (A0: H 0 * H 0 = H 0 * 1).
  { rewrite <- T. rewrite Rplus_0_r. intuition. }
  assert (A1: forall c: R, H c * H 0 = H c).
  { intros. rewrite <- T. intuition. }
  destruct (Req_EM_T (H 0) 0).
  + assert (A2: forall c: R, H c = 0).
      { intros. specialize (A1 c). rewrite e in A1.
        rewrite <- (Rmult_0_r (H c)). intuition. }
    split.
      * intros D.
        specialize (D 0 1).
        rewrite 2 A2 in D. intuition. rewrite e. apply H0.
      * intros [B0 _]. rewrite e in B0. exfalso. intuition.
  + assert (H 0 = 1).
      { apply (Rmult_eq_reg_l (H 0)); auto. }
      assert (A2: forall c: R, H c * H (-c) = 1).
      { intros. rewrite <- T. rewrite Rplus_opp_r. auto. }
      split.
      * intros. clear n.
        split.
        ** apply H0.
        ** intros. intros X. apply H2. apply H1.
           rewrite X, H0. trivial.
      * intros [B0 B1] x y C.
        assert (H (x - y) = 1).
        { replace (_ - _) with (x + (-y)) by intuition. rewrite T. rewrite C. apply A2. }
        assert (B2:= B1 (x - y)).
        destruct (Req_EM_T (x - y) 0).
        { intuition. }
        specialize (B2 n0). intuition.
Qed.
Close Scope R_scope.