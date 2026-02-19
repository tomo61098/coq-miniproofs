From Coq Require Import Arith PeanoNat Lia.
From Coq Require Import List.
Import ListNotations.

(* If g is a proper divisor of a positive m, then 2*g <= m. *)
Lemma two_mul_le_of_proper_divisor :
  forall g m : nat,
    m <> 0 ->
    Nat.divide g m ->
    g <> m ->
    2 * g <= m.
Proof.
  intros g m Hm0 [k Hk] Hgneq.
  subst m.
  destruct k as [|k].
  - (* k = 0 -> m = 0, contradiction *)
    exfalso. apply Hm0. lia.
  - destruct k as [|k].
    + (* k = 1 -> m = g, contradiction with g <> m *)
      exfalso. apply Hgneq. lia.
    + (* k >= 2 *)
      (* goal: 2*g <= g * (S (S k)) *)
      rewrite Nat.mul_comm with (n := 2) (m := g).  (* 2*g = g*2 *)
      lia.
Qed.

Theorem min_gcd_trichotomy :
  forall x y : nat,
    ({Nat.min x y = 0} + {Nat.gcd x y = Nat.min x y}) + {2 * Nat.gcd x y <= Nat.min x y}.
Proof.
  intros x y.
  set (m := Nat.min x y).
  set (g := Nat.gcd x y).

  destruct (Nat.eq_dec m 0) as [Hm0 | Hm0].
  - (* min = 0 *)
    left; left; exact Hm0.
  - (* min <> 0 *)
    destruct (Nat.eq_dec g m) as [Hgm | Hgm].
    + (* gcd = min *)
      left; right; exact Hgm.
    + (* gcd <> min, show 2*g <= min *)
      right.
      assert (Hdiv : Nat.divide g m).
      {
        unfold g, m.
        destruct (Nat.min_spec x y) as [[Hmin Hle] | [Hmin Hle]];
          rewrite Hle;
          [ exact (Nat.gcd_divide_l x y)
          | exact (Nat.gcd_divide_r x y) ].
      }
      apply (two_mul_le_of_proper_divisor g m); auto.
Qed.


Theorem max_gcd_trichotomy :
  forall a b : nat,
    ({Nat.min a b = 0} + {a = b}) + {2 * Nat.gcd a b <= Nat.max a b}.
Proof.
  intros a b.
  set (mn := Nat.min a b).
  set (mx := Nat.max a b).
  set (g  := Nat.gcd a b).

  destruct (Nat.eq_dec mn 0) as [Hmn0 | Hmn0].
  - left; left; exact Hmn0.
  - destruct (Nat.eq_dec a b) as [Hab | Hab].
    + left; right; exact Hab.
    + destruct (le_lt_dec a b) as [Hab_le | Hab_gt].
      * (* a <= b, so mx = b and mn = a *)
        assert (Hmx : mx = b) by (unfold mx; now rewrite Nat.max_r).
        assert (Hmn : mn = a) by (unfold mn; now rewrite Nat.min_l).
        subst mx mn.

        assert (Ha0 : a <> 0) by (intro Ha; apply Hmn0; now rewrite Hmn, Ha).
        assert (Hb0 : b <> 0) by (lia).

        assert (Hdiv : Nat.divide g b).
        { unfold g. exact (Nat.gcd_divide_r a b). }
        assert (Hab_lt : a < b) by lia.
        destruct (min_gcd_trichotomy a b) as [[M|M]|M].
        -- contradiction.
        -- right. rewrite Hmn in M.
           rewrite Hmx. subst g. rewrite M.
           rewrite M in Hdiv. destruct Hdiv.
           destruct x; [lia|].
           destruct x; [lia|].
           lia.
        -- right. lia.
      * (* b < a, so mx = a and mn = b *)
        assert (Hmx : mx = a) by (unfold mx; now rewrite Nat.max_l; lia).
        assert (Hmn : mn = b) by (unfold mn; now rewrite Nat.min_r; lia).
        subst mx mn.

        assert (Hb0 : b <> 0) by (intro Hb; apply Hmn0; now rewrite Hmn, Hb).
        assert (Ha0 : a <> 0) by (lia).

        assert (Hdiv : Nat.divide g a).
        { unfold g. exact (Nat.gcd_divide_l a b). }
        destruct (min_gcd_trichotomy a b) as [[M|M]|M].
        -- contradiction.
        -- right. rewrite Hmn in M.
           rewrite Hmx. subst g. rewrite M.
           rewrite M in Hdiv. destruct Hdiv.
           destruct x; [lia|].
           destruct x; [lia|].
           lia.
        -- right. lia.
Qed.


(* ---------- Rolling gcds ---------- *)

Fixpoint rolling_gcds_iter (g : nat) (l : list nat) : list nat :=
  match l with
   | [] => [g]
   | y :: ys => g :: rolling_gcds_iter (Nat.gcd g y) ys
   end
.

Definition rolling_gcds (l : list nat) : list nat :=
  match l with
   | [] => []
   | y :: ys => rolling_gcds_iter y ys
  end
.

(* Drop only consecutive duplicates (good enough for rolling gcds) *)
Fixpoint dedup_changes (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs =>
    match xs with
      | [] => [x]
      | y :: ys =>
        if Nat.eqb x y then dedup_changes xs
        else x :: dedup_changes xs
    end
  end
.

Definition rolling_gcd_uniques (l : list nat) : list nat :=
  dedup_changes (rolling_gcds l).

(* max of a list (0 for empty) *)
Fixpoint max_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => Nat.max x (max_list xs)
  end.

Lemma max_list_ge_hd :
  forall x xs, x <= max_list (x :: xs).
Proof.
  simpl; intros; apply Nat.le_max_l.
Qed.

Lemma max_list_ge_in :
  forall x l, In x l -> x <= max_list l.
Proof.
  induction l as [|a l IH]; simpl; intros Hin; [contradiction|].
  destruct Hin as [<-|Hin].
  - apply Nat.le_max_l.
  - etransitivity. 2: apply Nat.le_max_r.
    apply IH; exact Hin.
Qed.

Lemma dedup_rolling_eq: forall a b l,
  Nat.gcd a b = a ->
  dedup_changes (rolling_gcds_iter a (b::l)) = dedup_changes (rolling_gcds_iter a l)
.
Proof.
  intros. simpl rolling_gcds_iter.
  rewrite H.
  destruct l; auto; simpl; rewrite Nat.eqb_refl; auto.
Qed.

Lemma dedup_rolling_0: forall a l,
  dedup_changes (rolling_gcds_iter a (0::l)) = dedup_changes (rolling_gcds_iter a l)
.
Proof.
  intros.
  apply (dedup_rolling_eq a 0 l).
  apply Nat.gcd_0_r.
Qed.

Theorem rolling_gcds_iter_len : forall l a,
  a <> 0 ->
  2 ^ length (dedup_changes (rolling_gcds_iter a l)) <= 2 * a
.
Proof.
  induction l.
    - intros. simpl. lia.
    - intros b negb.
      assert (Eb:= Nat.gcd_divide_r a b).
      assert (Ea:= Nat.gcd_divide_l a b).
      destruct (zerop a); [subst; rewrite dedup_rolling_0; auto|].
      assert (Gnen : Nat.gcd a b <> 0).
      { destruct Eb, Ea; lia. }
      + destruct (le_dec a b).
      ++ destruct (le_lt_eq_dec _ _ l1).
         -- assert (F: Nat.gcd a b <> b).
            { destruct Ea, Eb.
              destruct x, x0; try lia. }
            assert (G := two_mul_le_of_proper_divisor (Nat.gcd a b) b negb (Nat.gcd_divide_r a b) F).
            specialize (IHl _ Gnen).
            assert (2 * 2 ^ length (dedup_changes (rolling_gcds_iter (Nat.gcd a b) l)) <= 2 * b) by lia.
            simpl rolling_gcds_iter.
            simpl dedup_changes.
            rewrite Nat.gcd_comm in H.
            destruct (rolling_gcds_iter (Nat.gcd b a) l).
            * simpl. lia.
            * destruct (b =? n); [lia|auto].
         -- subst. rewrite dedup_rolling_eq; auto using Nat.gcd_diag.
      ++ assert (N: b < a) by lia.
         destruct Eb.
         destruct x; [lia|].
         destruct x.
         * assert (F: b = Nat.gcd a b) by lia.
           rewrite Nat.gcd_comm in F.
           rewrite dedup_rolling_eq; auto.
         * assert (F: Nat.gcd a b <> b) by lia.
           assert (G := two_mul_le_of_proper_divisor (Nat.gcd a b) b negb (Nat.gcd_divide_r a b) F).
           specialize (IHl _ Gnen).
            assert (2 * 2 ^ length (dedup_changes (rolling_gcds_iter (Nat.gcd a b) l)) <= 2 * b) by lia.
            simpl rolling_gcds_iter.
            simpl dedup_changes.
            rewrite Nat.gcd_comm in H0.
            destruct (rolling_gcds_iter (Nat.gcd b a) l).
            ** simpl. lia.
            ** destruct (b =? n0); [lia|auto].
Qed.