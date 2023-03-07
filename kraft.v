Require Import Lia.
Require Import Nat PeanoNat.
Import Nat.
Require Import List.
Import ListNotations.

Fixpoint sum (l: list nat): nat :=
  match l with
    | (x::xs) => x + sum xs
    | _ => 0
  end.

Fixpoint map {A B: Type} (f: A -> B) (l: list A) : list B :=
  match l with
    | (x::xs) => f x :: map f xs
    | _ => []
  end.

Fixpoint maximum (l: list nat) : nat :=
  match l with
   | (x::xs) => max x (maximum xs)
   | _ => 0
  end.

Inductive bintree : Type :=
  | Leaf : bintree
  | Node : forall (l r: bintree), bintree.

Fixpoint depths (T: bintree) : list nat :=
  match T with
    | Node Leaf Leaf => [0]
    | Node L R => map S (depths L) ++ map S (depths R)
    | _ => []
  end.

Inductive sortedGe: (list nat) -> Prop :=
  | emptySortedGe: sortedGe []
  | singleSortedGe: forall x, sortedGe [x]
  | stepSortedGe: forall x y ys, (x >= y) -> sortedGe (y::ys) -> sortedGe (x::y::ys)
.

Lemma sortedGeMax: forall (l: list nat) (x: nat) ,
  sortedGe (x::l) ->
  maximum (x::l) = x.
Proof. induction l.
  - intros. simpl. apply max_0_r.
  - intros. inversion H; subst.
    simpl. specialize (IHl _ H4).
    simpl in IHl.
    rewrite IHl. lia.
Qed.

Lemma sortedGeSkip: forall (x y: nat) (l: list nat),
  sortedGe (x::y::l) -> sortedGe (x::l).
Proof. intros.
  destruct l.
    - apply singleSortedGe.
    - inversion H; subst. inversion H4; subst.
      apply stepSortedGe; auto. lia.
Qed.

Local Hint Constructors sortedGe: core.

Fixpoint chain (d: nat) : bintree :=
  match d with
    | S d' => Node (chain d') Leaf
    | _ => Leaf
  end.

Lemma chainExist: forall (n: nat),
  depths (chain (S n)) = [n].
Proof. induction n.
  - simpl. auto.
  - simpl. simpl in IHn. rewrite IHn. trivial.
Qed.

Lemma sumN: forall (l: list nat) (y x: nat),
  sortedGe (x::y::l) ->
    sum (map (fun z => 2^(x - z)) l) = 2 ^ (x - y) * (sum (map (fun z => 2^(y - z)) l)).
Proof. induction l.
  - intros. simpl. lia.
  - intros. simpl.
    rewrite mul_add_distr_l.
   rewrite <- pow_add_r.
   inversion H; subst.
   inversion H4; subst.
   replace (x - y + (y - a)) with (x - a) by lia.
   f_equal.
   apply IHl. apply (stepSortedGe _ _ _ H2).
   apply (sortedGeSkip _ _ _ H4).
Qed.

Lemma fbh: forall (n m k: nat),
  n > m ->
  n - m + k = n -> k = m.
Proof. lia. Qed.

Lemma sumpow2: forall (x y z: nat),
  2 ^ x + 2 ^ y = 2 ^ z -> S y = z.
Proof.
    assert (K: forall y, 0 < 2 ^ y).
    { induction y; simpl; lia. }
 induction x, y.
  - intros. simpl in H.
    apply (f_equal log2_up) in H.
    rewrite log2_up_pow2 in H by lia.
    apply H.
  - intros.
    simpl (2 ^ 0) in H.
    apply (f_equal log2_up) in H.
    rewrite log2_up_succ_pow2 in H by lia.
    rewrite log2_up_pow2 in H by lia.
    lia.
  - intros.
    simpl (2 ^ 0) in H.
    assert (B: 0 <= S x) by lia.
    assert (C1: forall y, 1 < 2 ^ S y).
    { intros. specialize (K y). simpl. lia. }
    assert (C: 0 <= 1 < 2 ^ S x) by auto.
    symmetry in H.
    assert (A:= (log2_unique' (2^z) (S x) 1) B C H).
    rewrite log2_pow2 in A by lia.
    subst. lia.
  - intros.
    destruct z.
    ++ simpl in H. lia.
    ++ destruct z.
      ** simpl in H.
         assert (A:=K x).
         assert (B:=K y). lia.
      ** replace (2 ^ S x + 2 ^ S y) with
         (2 * (2 ^ x + 2 ^ y)) in H.
          2:{ simpl. lia. }
         change (2 ^ S (S z)) with (2 * 2 ^ S z) in H.
         assert (F: 2 <> 0) by lia.
         assert (B:= mul_cancel_l (2 ^ x + 2 ^ y) (2 ^ S z) _ F).
         destruct B.
         apply  H0 in H.
         specialize (IHx _ _ H). lia.
Qed.

Corollary sumpow2_eq: forall (x y z: nat),
  2 ^ x + 2 ^ y = 2 ^ z -> x = y.
Proof. intros. assert (A:= sumpow2 _ _ _ H).
  rewrite add_comm in H. assert (B:= sumpow2 _ _ _ H). lia.
Qed.

Require Import Even.

Lemma pow2odd: forall (x: nat),
  odd (2 ^ x) -> x = 0.
Proof. destruct x; auto. intros.
  change (2 ^ S x) with (2 * 2 ^ x) in H.
  assert (A: even 2) by intuition.
  assert (F:= even_mult_l 2 (2 ^ x) A).
  exfalso. apply (not_even_and_odd _ F H).
Qed.

Lemma sumneqpow2x: forall (x a: nat),
  S (2 * a) = 2 ^ x -> x = 0.
Proof. intros. apply pow2odd.
  assert (A: even 2) by intuition.
  assert (F:= even_mult_l 2 a A).
  apply odd_S in F.
  rewrite H in F. apply F.
Qed.

Lemma sumneqpow2a: forall (x a: nat),
  S (2 * a) = 2 ^ x -> a = 0.
Proof. intros. assert (A:= sumneqpow2x _ _ H).
  rewrite A in H. simpl in H. lia.
Qed.

Lemma summultpow2: forall (y x z a: nat),
  a > 0 ->
  2 ^ x + a * 2 ^ y = 2 ^ z -> y <= x.
Proof. intros.
  assert (A1: forall n, 0 < 2 ^ n).
  { induction n; intuition. simpl. lia. }
  destruct (Compare_dec.le_gt_dec y x); auto.
  assert (F2:= A1 y).
  assert (A: 2 ^ x < 2 ^ z) by lia.
  assert (D: x < z).
  { apply (pow_lt_mono_r_iff 2 x z); lia. }
  assert (A2: S (a * 2 ^ (y - x)) = 2 ^ (z - x)).
  { assert (F1:= A1 x). apply (mul_cancel_l _ _ (2 ^ x)). lia.
    rewrite mul_succ_r.
    rewrite add_comm.
    rewrite mul_comm at 1.
    rewrite <- mul_assoc.
    rewrite <-2 pow_add_r.
    rewrite (sub_add x y) by lia.
    rewrite (add_comm x).
    rewrite (sub_add) by lia. apply H0.
  }
  assert (G: forall n m, m > n -> exists k, m - n = S k).
  { induction n. - intros. exists (pred m). destruct m; lia.
    - intros. destruct m. lia. destruct (IHn m). lia.
      exists (x0). lia. }
  destruct (G _ _ g).
  rewrite H1 in A2.
  replace (a * 2 ^ S x0) with (2 * (a * 2 ^ x0)) in A2.
  2:{ simpl. lia. }
  assert (R:= sumneqpow2a (z - x) _ A2).
  assert (2 ^ x0 = 0) by lia.
  specialize (A1 x0). lia.
Qed.

Lemma sumEq: forall (x y: nat) (l: list nat),
  sortedGe (x::y::l) ->
  ((sum (map (fun z => 2^(x - z)) (x::y::l)) = 2^x))
    -> x = y.
Proof.
  intros. inversion H; subst.
  change (sum
       (map (fun z : nat => 2 ^ (x - z))
          (x :: y :: l))) with
  ( 2 ^ (x - x) + sum
       (map (fun z : nat => 2 ^ (x - z))
          (y :: l))) in H0.
  rewrite (sumN (y::l) y x) in H0.
  rewrite mul_comm in H0.
  assert (sum
       (map (fun z : nat => 2 ^ (y - z))
          (y :: l)) > 0).
  { simpl. rewrite sub_diag. simpl. lia. }
  apply (summultpow2 _ _ _ _ H1) in H0.
  lia. constructor; auto.
Qed.

Lemma sumLt: forall (l: list nat) (x y: nat)  ,
  sortedGe (x::y::l) ->
  x > y -> (sum (map (fun z => 2^(x - z)) (x::y::l)) <= 2^x)
  -> (sum (map (fun z => 2^(x - z)) (x::y::l)) < 2^x).
Proof. intros.
  destruct (Compare_dec.le_lt_eq_dec _ _ H1); auto.
  assert (F:= sumEq _ _ _ H e).
  lia.
Qed.

Proposition maximumListStep:
  forall (l: list nat) (x: nat),
  maximum l <= maximum (x::l).
Proof. intros. simpl. lia. Qed.

Theorem maxListNatInduction:
  forall (P: list nat -> Prop),
  P [] ->
  (forall (n: nat),
    (forall l, maximum l < n -> P l) ->
    (forall l, maximum l < S n -> P l)
  ) -> forall l, P l.
Proof. intros.
  

Theorem Kraft : forall (l: list nat),
  (sortedGe l) -> (
  (sum (map (fun x => 2^(maximum l - x)) l) <= 2^(maximum l))
    <->
  exists T: bintree, sortedGe (depths T) /\ depths T = l
  ).
Proof.
  refine (fix f l: (sortedGe l) -> (
  (sum (map (fun z => 2^(maximum l - z)) l) <= 2^(maximum l))
    <->
  exists T: bintree, sortedGe (depths T) /\ depths T = l
  ) :=
  match l with
    | [] => _
    | [x] => _
    | (y::x::xs) => _
  end).
  - simpl. intros. split.
    + intros. exists Leaf. intuition.
    + lia.
  - intros.
    simpl. split.
    + intros. exists (chain (S x)).
      rewrite chainExist. auto.
    + intros [T [E F]].
      simpl. rewrite max_0_r.
      rewrite sub_diag.
      rewrite <- plus_n_O. cbn.
      assert (forall n, 1 <= 2^n).
      { induction n; auto. simpl. lia. }
      apply H0.
  - intros. rewrite sortedGeMax by auto. inversion H; subst. split; intros.
    + destruct (Compare_dec.le_lt_eq_dec _ _ H2).
      * apply (sumLt _ _ _ H l1) in H0.
        assert (B1: sortedGe (S y :: xs)).
        { destruct xs; auto. inversion H; subst. inversion H7; subst. apply stepSortedGe; auto. lia. }
        destruct (f (S y :: xs) B1) as [A _].
        rewrite sortedGeMax in A by auto.
        