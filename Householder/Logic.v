Require Import Vector.
Import VectorNotations VectorDef.

Theorem eta0 {A}: forall x: t A O, x = [].
Proof. apply case0. auto. Qed.

Require Import Bool.
Import BoolNotations.

Notation vec := (t bool).

Fixpoint take_bool (m: nat) {n: nat} (v: vec n): bool :=
  match m, v with
    | _, [] => true
    | O, x::xs => x
    | S m', _::xs => take_bool m' xs
  end
.

Inductive Expression: Type :=
  | Var: nat -> Expression
  | Or: Expression -> Expression -> Expression
  | And: Expression -> Expression -> Expression
  | Not: Expression -> Expression
.

Fixpoint eval_expression (E: Expression) {n: nat} (V: vec n): bool :=
  match E with
    | Var x => take_bool x V
    | Or X Y => eval_expression X V || eval_expression Y V
    | And X Y => eval_expression X V && eval_expression Y V
    | Not X => negb (eval_expression X V)
  end
.

Fixpoint prepend_var (E: Expression): Expression :=
  match E with
    | Var n => Var (S n)
    | Or X Y => Or (prepend_var X) (prepend_var Y)
    | And X Y => And (prepend_var X) (prepend_var Y)
    | Not X => Not (prepend_var X)
  end
.

Lemma prepend_red: forall (n: nat) (b: bool) (v: vec n) (E: Expression),
  eval_expression (prepend_var E) (b::v) = eval_expression E v.
Proof.
  induction E.
    -- trivial.
    -- simpl. rewrite IHE1, IHE2. trivial.
    -- simpl. rewrite IHE1, IHE2. trivial.
    -- simpl. rewrite IHE. trivial.
Qed.

Theorem global_bool:
  forall (n: nat) (f: vec n -> bool),
    exists (E: Expression),
      forall (v: vec n), f v = eval_expression E v.
Proof.
  induction n; intros.
    - destruct (bool_dec (f []) true).
      -- exists (Var 0). intros. rewrite (eta0 v). apply e.
      -- exists (Not (Var 0)). intros. rewrite (eta0 v). apply (not_true_is_false _ n).
    - pose (g1 := fun (v: vec n) => f (true::v)).
      pose (g2 := fun (v: vec n) => f (false::v)).
      destruct (IHn g1), (IHn g2).
      exists (Or (And (Var 0) (prepend_var x)) (And (Not (Var 0)) (prepend_var x0))).
      intros. rewrite (eta v).
      destruct (hd v).
        -- simpl. rewrite orb_false_r.
           rewrite prepend_red.
           apply H.
        -- simpl. rewrite prepend_red.
           apply H0.
Qed.

Inductive ExpressionNand: Type :=
  | VarNand: nat -> ExpressionNand
  | Nand: ExpressionNand -> ExpressionNand -> ExpressionNand
.

Fixpoint eval_expressionnand (N: ExpressionNand) {n: nat} (V: vec n): bool :=
  match N with
    | VarNand x => take_bool x V
    | Nand X Y => negb (eval_expressionnand X V && eval_expressionnand Y V)
  end
.

Theorem global_nand: forall (E: Expression),
  exists (N: ExpressionNand),
   forall (n: nat) (v: vec n),
     eval_expression E v = eval_expressionnand N v.
Proof.
  induction E.
    - exists (VarNand n). trivial.
    - destruct IHE1, IHE2.
      exists (Nand (Nand x x) (Nand x0 x0)).
      intros. simpl. rewrite 2 andb_diag.
      rewrite negb_andb. rewrite 2 negb_involutive.
      rewrite H, H0. trivial.
    - destruct IHE1, IHE2.
      exists (Nand (Nand x x0) (Nand x x0)).
      intros. simpl. rewrite ? andb_diag.
      rewrite negb_involutive.
      rewrite H, H0. trivial.
    - destruct IHE. exists (Nand x x).
      intros. simpl. rewrite andb_diag.
      rewrite H. trivial.
Qed.


