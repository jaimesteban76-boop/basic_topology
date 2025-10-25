import basic_topology.Metric
import Mathlib.Data.Set.Finite.Basic

variable {X Y D: Type*}

-- diameter of a set
noncomputable def diameter [CompleteDistanceSpace D] (d: X → X → D) (A: Set X): D :=
  sSup (⋃ (a ∈ A) (b ∈ A), {d a b})


theorem diameter_monotone [CompleteDistanceSpace D] (d: X → X → D) {A B: Set X} (h: A ⊆ B): diameter d A ≤ diameter d B := by
  sorry

theorem diameter_singleton [CompleteDistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x: X): diameter d {x} = 0 := by
  simp [diameter]--, hd.dist_self_bot x]
  sorry -- missing import?

example [CompleteDistanceSpace D] (d: X → X → D): diameter d ∅ = 0 := by
  simp [diameter]
  sorry

example [CompleteDistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x y: X): diameter d {x, y} = d x y := by
  simp [diameter]
  sorry

example [CompleteDistanceSpace D] (d: X → X → D) (hd: IsMetric d) (x: X) (r: D): diameter d (openball d x r) ≤ 2 • r := by
  simp [diameter]
  intros
  have := hd.triangle
  sorry

-- a set is bounded if it has finite diameter.
def bounded [CompleteDistanceSpace D] (d: X → X → D) (A: Set X): Prop :=
  diameter d A < ⊤

-- a set is boudned iff. it is contained in a ball of finite radius.
-- maybe closed ball easier.
theorem bounded_iff [CompleteDistanceSpace D] (d: X → X → D) (A: Set X): bounded d A ↔ ∃ x r, r < ⊤ ∧ A ⊆ openball d x r := by
  sorry

theorem bounded_subset [CompleteDistanceSpace D] (d: X → X → D) {A B: Set X} (h1: A ⊆ B) (h2: bounded d B): bounded d A := by
  exact lt_of_le_of_lt (diameter_monotone _ h1) h2

-- TODO if a finite family is all bounded their union is bounded.
theorem bounded_finite_union [CompleteDistanceSpace D] (d: X → X → D) (F: Set (Set X)) (h1: Finite F) (h2: ∀ A ∈ F, bounded d A): bounded d (⋃₀ F) := by
  sorry

def totally_bounded [CompleteDistanceSpace D] (d: X → X → D) (A: Set X): Prop :=
  ∀ ε, ⊥ < ε → ∃ C: Set X, Finite C ∧ A ⊆ ⋃ (x ∈ C), openball d x ε

theorem totally_bounded_bounded [CompleteDistanceSpace D] {d: X → X → D} {A: Set X} (h: totally_bounded d A): bounded d A := by
  sorry
