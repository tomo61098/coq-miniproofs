namespace LeanProofs

/-!
This file sets up a Lean skeleton for the reduction from ordinary
`PARTITION` to equal-cardinality partition restricted to perfect squares.
-/

def listSum : List Nat -> Nat
  | [] => 0
  | x :: xs => x + listSum xs

def listSumSquares : List Nat -> Nat
  | [] => 0
  | x :: xs => x * x + listSumSquares xs

def countTrue : List Bool -> Nat
  | [] => 0
  | true :: bs => countTrue bs + 1
  | false :: bs => countTrue bs

def signedSum : List Bool -> List Nat -> Int
  | [], [] => 0
  | b :: bs, x :: xs =>
      (if b then (x : Int) else -((x : Int))) + signedSum bs xs
  | _, _ => 0

def IsSquare (n : Nat) : Prop :=
  Exists fun k : Nat => n = k * k

def AllSquares (xs : List Nat) : Prop :=
  forall x, List.Mem x xs -> IsSquare x

/-- Ordinary partition: choose signs so the signed sum is zero. -/
def Partition (xs : List Nat) : Prop :=
  Exists fun signs : List Bool =>
    signs.length = xs.length /\
    signedSum signs xs = 0

/--
Equal-cardinality partition, restricted to inputs whose entries are all
perfect squares.

The Boolean list records membership in the left side. The equation
`2 * countTrue signs = xs.length` says the two sides have equal size.
-/
def EqualCardinalitySquarePartition (xs : List Nat) : Prop :=
  AllSquares xs /\
    Exists fun signs : List Bool =>
      signs.length = xs.length /\
      2 * countTrue signs = xs.length /\
      signedSum signs xs = 0

/-
For an original number `a_i`, the reduction creates the pair

  u_i = (K^(n+i) + K^(n-i) a_i) / 2
  v_i = (K^(n+i) - K^(n-i) a_i) / 2

and outputs the two perfect squares `u_i^2`, `v_i^2`.
-/


def squareReductionAux (K n i : Nat) : List Nat -> List Nat
  | [] => []
  | x :: xs => (K^(n+i) + x * K^(n-i))^2 :: (K^(n+i) - x * K^(n-i))^2 :: squareReductionAux K n (i + 1) xs

theorem squareReductionAux_allSquares:
  forall (xs: List Nat) (K n i: Nat),
  AllSquares (squareReductionAux K n i xs) := by
  intro xs
  induction xs with
  | nil =>
      intro K n i y hy
      cases hy
  | cons x xs ih =>
      intro K n i y hy
      cases hy
      case head =>
          exists K^(n+i) + x * K^(n-i)
          grind
      case tail hy =>
          cases hy
          case head =>
              exists K^(n+i) - x * K^(n-i)
              grind
          case tail hy =>
              exact ih K n (i + 1) y hy

def squareReduction (B : Nat) (xs : List Nat) : List Nat :=
  squareReductionAux B xs.length 1 xs

theorem squareReduction_allSquares :
  forall (K: Nat) (xs: List Nat),
    AllSquares (squareReduction K xs) := by
    intros K xs
    apply squareReductionAux_allSquares

def K_sum: List Nat -> Nat
  | [] => 2
  | y::ys => 2 * y^2 + 4 * y + K_sum ys

inductive PairBinSigns : List Bool -> Prop :=
  | nil : PairBinSigns []
  | cons_l : forall xs, PairBinSigns xs -> PairBinSigns (true :: false :: xs)
  | cons_r : forall xs, PairBinSigns xs -> PairBinSigns (false :: true :: xs)

theorem squarePartition_divides:
  forall (xs: List Nat) (K: Nat) (signs: List Bool),
  signs.length = 2 * xs.length ->
  signedSum signs (squareReduction (K_sum xs) xs) = 0 ->
    PairBinSigns signs := by
    intro xs
    induction xs
    case nil =>
      intros K signs L M
      simp [squareReduction, squareReductionAux] at *
      cases signs
      case nil => constructor
      case cons x xs =>
        contradiction
    case cons x xs H =>
      intros K signs L M
      cases signs
      case nil => grind
      case cons s sx =>
        cases sx
        case nil => grind
        case cons z sx =>
          have L2: sx.length = 2 * xs.length := by grind
          specialize H K sx L2
          simp [squareReduction, squareReductionAux, signedSum] at M




theorem partition_to_squarePartition
    (xs : List Nat)
    (h : Partition xs) :
    EqualCardinalitySquarePartition (squareReduction (K_sum xs) xs) := by
  induction xs
  case nil =>
    simp [squareReduction, squareReductionAux]
    constructor
    case left =>
      intros x M
      cases M
    case right =>
      cases h
      case intro w h =>
        exists w
        constructor
        case left => grind
        case right =>
          constructor
          case left =>
          cases h
          case intro L R =>
            simp at L
            rw [L]
            simp [countTrue]
  case cons x xs H =>
    simp [EqualCardinalit]



theorem squarePartition_to_partition
    (xs : List Nat)
    (h : EqualCardinalitySquarePartition (squareReduction (K_sum xs) xs)) :
    Partition xs := by
  sorry

/--
Correctness of the many-one reduction, for any sufficiently large even base
`B`.

Together with the polynomial-size construction lemma, this is the core
statement needed for NP-hardness of equal-cardinality partition on perfect
squares.
-/
theorem squareReduction_correct
    {B : Nat} {xs : List Nat}
    (hB : GoodBase B xs) :
    Partition xs <-> EqualCardinalitySquarePartition (squareReduction B xs) := by
  exact Iff.intro (partition_to_squarePartition hB) (squarePartition_to_partition hB)

end LeanProofs
