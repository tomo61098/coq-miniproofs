Add LoadPath "C:\Progis\Coq\Prog\matrix" as Matrix.
Load Cprops.

Open Scope C.
Open Scope vec_scope.
Open Scope mat_scope.

(* MEM def *)

Require Import Bool.
Definition set (A : Set) := A -> bool.

Definition is_mem {A: Set} (H: set A) (a : A) := H a = true.

Theorem is_mem_dec (A : Set) (H : set A) :
  forall a, { is_mem H a } +  { ~(is_mem H a) }.
  unfold is_mem. intros a.
  apply (bool_dec (H a)).
Qed.

Theorem is_mem_contradict (A : Set) (H : set A) :
  forall a, is_mem H a -> ~is_mem H a -> False.
  intros a; auto.
Qed.

Theorem is_mem_not (A : Set) (H : set A):
  forall a, ~is_mem H a <-> (H a) = false.
  intros a.
  unfold is_mem.
  rewrite <- not_true_iff_false.
  reflexivity.
Qed.

Structure img {n m} (A: matrix n m) := make_img {
  img_mem :> set (vec n) ;
  has_og: forall z, is_mem img_mem z <-> exists x, A@x = z ;
}.

Structure ker {n m} (A: matrix n m) := make_ker {
  ker_mem :> set (vec m) ;
  is_0: forall z, is_mem ker_mem z <-> A@z = 0%Vec ;
}.

(* SPAN def *)

Definition lin_ind {n m} (A: matrix n m) :=
  forall x, ((tM A) @ x = 0 -> x = 0)%Vec.

Definition spans {n m} (A: matrix n m) :=
  forall x, {y | tM A @ y = x}.

(* SPAN proofs *)

Goal lin_ind [[1; 0];[0;1]]%C.
Proof.
  unfold lin_ind.
  intros.
  simpl tM in H.
  assert (B:= vec_mult_I x).
  simpl I in B.
  rewrite B in H.
  apply H.
Qed.

Lemma lin_ind_step: forall {n m} (A: matrix (S n) m),
  lin_ind A -> lin_ind (tl A).
Proof. unfold lin_ind.
  intros. specialize (H (0%C::x))%Vec.
  rewrite mat_mult_col in H.
  simpl in H. rewrite vec_mult_0 in H.
  rewrite vec_plus_comm in H.
  rewrite vec_plus_0 in H.
  rewrite mat_tm_tc_commute in H.
  specialize (H H0).
  apply (f_equal tl) in H.
  simpl in H.
  apply H.
Qed.

Lemma lin_ind_conc: forall {n m} (A: matrix n m)
  ,
  ~lin_ind A -> forall (x: vec m), ~lin_ind (x::A).
Proof. unfold lin_ind. intros.
  intros F. apply H.
  intros.
  specialize (F (0%C::x0)).
  rewrite mat_mult_col in F.
  simpl in F. rewrite vec_mult_0 in F.
  rewrite vec_plus_comm in F.
  rewrite vec_plus_0 in F.
  rewrite mat_tm_tc_commute in F.
  specialize (F H0).
  apply (f_equal tl) in F.
  apply F.
Qed.

Lemma spans_conc: forall {n m} (A: matrix n m),
  spans A -> forall x, spans (x::A).
Proof.
  unfold spans.
  intros. destruct (H x0).
  exists ((0%C::x1)).
  rewrite mat_mult_col.
  simpl. rewrite vec_mult_0.
  rewrite vec_plus_comm.
  rewrite vec_plus_0.
  rewrite mat_tm_tc_commute.
  simpl. apply e.
Qed.

Lemma spans_step: forall {n m} (A: matrix (S n) m),
  ~inhabited (spans A) -> ~inhabited (spans (tl A)).
Proof. unfold spans.
  intros. intros F. destruct F.
  apply H.
  apply inhabits. intros.
  destruct (H0 x).
  exists (0%C::x0).
  rewrite mat_mult_col.
  simpl. rewrite vec_mult_0.
  rewrite vec_plus_comm.
  rewrite vec_plus_0.
  rewrite mat_tm_tc_commute.
  simpl. apply e.
Qed.

Goal forall {n m} (A: matrix n m),
  ~(lin_ind (0%Vec :: A)).
Proof.
  intros n m A H.
  specialize (H (1%C::0%Vec)).
  assert (tM (0%Vec :: A) @ (1%C :: 0%Vec) = 0%Vec).
  { rewrite mat_mult_col in H.
  rewrite mat_hc_hd_commute in H.
  rewrite mat_tm_tc_commute in H.
  simpl in H. rewrite vec_0_mult in H.
  rewrite mat_mult_zeros in H.
  rewrite vec_plus_0 in H.
  specialize (H (eq_refl _)).
  apply (f_equal hd) in H.
  simpl in H.
  assert (B:=C1_neq_C0).
  contradiction. }
  specialize (H H0).
  apply (f_equal hd) in H.
  simpl in H.
  assert (B:=C1_neq_C0).
  contradiction.
Qed.

Lemma lin_ind_dep: forall {n m} (A: matrix n m)
  (x: vec m), {y| (tM A)@y = x} -> ~lin_ind (x::A).
Proof.
  unfold lin_ind.
  intros n m A x [y E] F.
  specialize (F ((-(1%C))%C::y))%Vec.
  rewrite mat_mult_col in F.
  simpl in F.
  rewrite mat_tm_tc_commute in F.
  rewrite mat_hc_hd_commute in F.
  simpl in F.
  rewrite E in F.
  rewrite vec_mult_neg1 in F.
  rewrite vec_plus_comm in F.
  rewrite vec_plus_sub in F.
  rewrite vec_sub_sub in F.
  specialize (F (eq_refl _)).
  apply (f_equal hd) in F.
  simpl in F.
  inversion F; subst.
  lra.
Qed.

Lemma lin_ind_not_ex: forall {n m} (A: matrix n m),
  lin_ind A <-> ~(exists x, x <> 0 /\ (tM A)@x = 0)%Vec.
Proof.
   unfold lin_ind.
      intros.
      split.
      + intros.
        intros [x [E F]].
         apply (E (H _ F)).
      + intros.
        destruct (vec_eq_dec x 0)%Vec; auto.
        exfalso. apply H. exists x.
        auto.
Qed.

Lemma ex_not_lin_ind: forall {n m} (A: matrix n m),
  (exists x, x <> 0 /\ (tM A)@x = 0)%Vec -> ~lin_ind A.
Proof.
      intros n m A [x [E H]]. intros F.
      apply (E (F _ H)).
Qed.

Lemma lin_ind_mat: forall {k n m} (A: matrix n m),
  lin_ind A -> forall (D: matrix n k), (tM A) @@ D = 0 -> D = 0.
Proof.
  induction k.
    - intros. rewrite eta0_col. apply eta0_col.
    - intros.
      simpl in H0.
      rewrite (eta_col D), (eta_col 0).
      f_equal.
      + apply (f_equal hc) in H0.
        rewrite hc_col in H0.
        rewrite mat_hc_0 in H0.
        rewrite mat_hc_0.
        f_equal.
        apply (H _ H0).
      + rewrite mat_tc_0.
        apply (f_equal tc) in H0.
        rewrite tc_col in H0.
        rewrite mat_tc_0 in H0.
        apply (IHk _ _ _ H). apply H0.
Qed.

Lemma spans_mat: forall {n m} (A: matrix n m),
  spans A -> forall {k} (X: matrix m k),  {D| (tM A) @@ D = X }.
Proof.
  intros n m A E.
  induction k.
    - intros. exists emptyM.
      rewrite eta0_col. apply eta0_col.
    - intros.
      destruct (IHk (tc X)).
      destruct (E (hc X)).
      exists (col x0 ++' x).
      simpl. rewrite tc_col, hc_col.
      rewrite e. rewrite e0. symmetry.
      apply eta_col.
Qed.

Lemma lin_ind_hd: forall {n m} (A: matrix (S n) m),
  ~lin_ind A -> (forall y, (tM A) @ y = 0%Vec -> hd y = 0%C) ->
  ~lin_ind (tl A).
Proof.
  intros. intros F.
  apply H. intros x G.
  specialize (H0 _ G).
  rewrite mat_mult_col in G.
  rewrite mat_tm_tc_commute in G.
  rewrite H0 in G.
  rewrite vec_mult_0 in G.
  rewrite vec_plus_comm in G.
  rewrite vec_plus_0 in G.
  rewrite (eta x). simpl.
  f_equal. { apply H0. }
  apply (F _ G).
Qed.

Lemma dot_eq_dec: forall {n} (a: C) (x: vec n),
  {y | dot y x = a} + {~exists y, dot y x = a}.
Proof.
  induction n.
    - intros. destruct (Ceq_dec a 0%C).
      + left. exists []. rewrite e. trivial.
      + right. intros [y F]. rewrite (eta0 y) in F. simpl in F.
        apply n. symmetry. apply F.
    - intros. destruct (IHn a (tl x)).
      + left. destruct s. exists (0%C::x0).
        rewrite dot_step.
        simpl hd. simpl tl. rewrite e. lca.
      + destruct (Ceq_dec (a) 0%C).
        { left. exists 0%Vec. rewrite e. apply dot_0. }
        destruct (Ceq_dec (hd x) 0%C).
        2:{ left. exists ((a * / (hd x)^*)%C :: 0%Vec).
            rewrite dot_step. simpl tl.
            rewrite dot_0. rewrite Cplus_0_r.
            simpl hd.
            rewrite Cmult_assoc.
            rewrite (Cmult_comm (/ _)).
            rewrite Cinv_r. lca.
            intros F. apply n2. rewrite <- Cconj_0 in F.
            apply (f_equal (fun x => x^*%C)) in F.
            rewrite ! Cconj_involutive in F.
            apply F.
      } right.
        intros [y Z].
        apply n0.
        rewrite dot_step in Z.
        rewrite e in Z. rewrite Cconj_0 in Z.
        rewrite Cmult_0_r in Z.
        rewrite Cplus_0_l in Z.
        exists (tl y).
        apply Z.
Qed.

Section Axb_solutions.

  Fixpoint solution_upTri {n m: nat} (R: matrix n m)
  (Rp: is_upTri R) (x: vec n): option (vec m).
  destruct m.
    - apply (Some []).
    - 

End Axv_solutions.

Lemma FF: forall {n m} (A: matrix n m) (x: vec m),
  {y | tM A @ y = x} + {forall y, tM A @ y <> x}.
Proof.
  induction n.
    - intros. destruct (vec_eq_dec x 0%Vec).
      + left. exists []. rewrite e. apply mat_mult_vec_empty.
      + right. intros y H. apply n. rewrite <- H. rewrite (eta0 y). apply mat_mult_vec_empty.
    - intros. destruct (IHn _ (tl A) x).
      + destruct s as [y E]. left.
      exists (0%C::y). rewrite mat_mult_col.
      simpl hd. rewrite vec_mult_0.
      rewrite vec_plus_comm. rewrite vec_plus_0.
      simpl tl. rewrite mat_tm_tc_commute. apply E.
      + 

Lemma lin_dep_step: forall {n m} (A: matrix (S n) m),
  ~lin_ind A -> (exists y, (tM (tl A)) @ y = hd A) \/ ~lin_ind (tl A).
Proof. intros n m. revert n.
  induction m.
    - intros.
      left. exists 0%Vec. etaeta.
    - intros.
      unfold lin_ind in H.
      

Lemma FF: forall {n m} (A: matrix n m),
  ~lin_ind A -> (exists x, x <> 0 /\ (tM A) @ x = 0)%Vec.
Proof. induction n.
  - intros. exfalso. apply H.
    intros x F. rewrite eta0. apply eta0.
  - intros. destruct (IHn m (tl A)).

Lemma lin_dec: forall {n m} (A: matrix n m),
  {(exists x, x <> 0 /\ A@x = 0)%Vec}+{lin_ind A}.
Proof.

Lemma lin_dec: forall {n m} (A: matrix n m)
  (x: vec n), {exists y, A@y = x}+{~exists y, A@y = x}.
Proof.
  induction n.
    - intros. left. exists 0%Vec. rewrite eta0. apply eta0.
    - intros. destruct (IHn _ (tl A) (tl x)).
      destruct (Ceq_dec (dot (hd A) (^*)) 0)%Vec.
      destruct e.

Lemma linv_dec: forall {n m} (A: matrix n m),
  lin_ind A \/ ~lin_ind A.
Proof. induction n.
    - intros. left. rewrite eta0. apply empty_ind.
    - intros. destruct (vec_eq_dec (tM A @ hd A) (tl A))
      destruct (IHn m (tl A)).
      + 

Lemma is_lin_inv_dec: forall {n m} (x: vec m) (B: matrix n m),
  {~(exists z, tM B @ z = x)} + {exists z, tM B @ z = x}.
Proof.
  induction n.
    - intros.
      assert (A := vec_eq_dec x 0%Vec).
      inversion A.

Fixpoint rank {n m} (A: matrix n m) : nat :=
  match A with
    | [] => O
    | x::B => if is_lin_inv_dec x B then S (rank B) else rank B end
.

Close Scope vec_scope.
Close Scope mat_scope.
Close Scope R.