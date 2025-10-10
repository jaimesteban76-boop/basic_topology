
import basic_topology.T3_sequences

variable {X Y D: Type*}



-- cauchy sequence in terms of diameters of tails
def cauchy [DistanceSpaceStruct D] (d: X → X → D) (x: Nat → X): Prop :=
  ∀ ε, ⊥ < ε → ∃ t, ∀ m n, t ≤ m → t ≤ n → d (x m) (x n) < ε

def cauchy_with_top [CompleteDistanceSpace D] (d: X → X → D) (x: Nat → X): Prop :=
  ∀ ε, ⊥ < ε → ∃ t, diameter d (Set.range (tail x t)) < ε


def cauchy_sequence_diameter [CompleteDistanceSpace D] (d: X → X → D) (x: Nat → X): cauchy d x ↔ ∀ r, ⊥ < r → ∃ t, diameter d (Set.range (tail x t)) < r := by
  sorry

theorem convergent_cauchy [DistanceSpaceStruct D] {d: X → X → D} {x: Nat → X} (h: convergent_distance d x): cauchy d x := by
  sorry

example [DistanceSpace D] {d: X → X → D} {x: Nat → X} {a: X} (h1: cauchy d x) (h2: adherent_value (metric_opensets d) x a): converges_distance d x a := by
  sorry

def complete [DistanceSpaceStruct D] (d: X → X → D): Prop :=
  ∀ x, cauchy d x → convergent_distance d x

-- If A ⊆ X is complete then it is closed.
-- todo : use subspace metric?
example [DistanceSpaceStruct D] (d: X → X → D) (A: Set X) (h: complete (fun (a b: A) => d a b)): metric_closedset d A := by
  sorry

example [DistanceSpaceStruct D] (d: X → X → D) (A: Set X) (h1: complete d) (h2: metric_closedset d A): complete (fun (a b: A) => d a b) := by
  sorry

-- If two metrics are uniformly equivalent, then Cauchy iff Cauchy.
-- Hence complete iff complete.

-- If dX, dY complete then dX x dY (the product metric given by max) is complete

structure Completion [DistanceSpace D] {X0 X1: Type*} (d0: X0 → X0 → D) (d1: X1 → X1 → D) (i: X0 → X1): Prop where
  isometry: isometry d0 d1 i
  dense: dense (metric_opensets d1) (Set.range i)
  complete: complete d1
