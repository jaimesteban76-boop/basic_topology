
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Lattice

set_option linter.style.multiGoal false

variable {X Y: Type*}

/-

Definition of topological space. Like for metric spaces:
- Given a type X and a collection of subsets 𝒯, `IsTopology 𝒯` is the statement that 𝒯 forms a topology.
- `Topology X` is the type of all topologies on `X`.
- `TopologicalSpace` is the type of all topological spaces.

For simplicity I guess we will work with `IsTopology` mostly.

-/

class Family (X: Type u) where
  Open: Set (Set X)

class Topology (X: Type u) extends Family X where
  union_open: ∀ 𝒰 ⊆ Open, ⋃₀ 𝒰 ∈ Open
  inter_finite_open: ∀ 𝒰 ⊆ Open, Finite 𝒰 → ⋂₀ 𝒰 ∈ Open

open Family Topology

def DiscreteTopology (X: Type u): Topology X := {
  Open := ⊤
  union_open := by exact fun 𝒰 a ↦ trivial
  inter_finite_open := by exact fun 𝒰 a a ↦ trivial
}

theorem empty_open [Topology X]: Open (⊥: Set X) := by
  have: (⊥: Set X) = ⋃₀ ⊥ := by ext; simp
  rw [this]
  apply union_open
  apply Set.empty_subset

-- Binary unions and intersections of open sets are open
theorem binary_union_open [Topology X] {A B: Set X} (hA: Open A) (hB: Open B): Open (A ∪ B) := by
  have: A ∪ B = ⋃₀ {A, B} := by ext; simp
  rw [this]
  apply union_open
  exact Set.pair_subset hA hB

-- The union of a sequence of open sets is open
theorem seq_union_open [Topology X] {U: Nat → Set X} (h: ∀ n, Open (U n)): Open (⋃ i, U i) := by
  apply union_open
  exact Set.range_subset_iff.mpr h

-- theorem: finite intersection property is equivalent to binary intersections plus whole set
 theorem finite_inter_iff {T: Set (Set X)}: (∀ U ⊆ T, U.Finite → ⋂₀ U ∈ T) ↔ Set.univ ∈ T ∧ ∀ A ∈ T, ∀ B ∈ T, A ∩ B ∈ T := by
  constructor
  · intro h
    constructor
    · rw [←Set.sInter_empty]
      apply h
      · apply Set.empty_subset
      · exact Set.finite_empty
    · intro _ hA _ hB
      rw [(Set.sInter_pair _ _).symm]
      apply h
      · exact Set.pair_subset hA hB
      · apply Set.toFinite
  intro ⟨_, hAB⟩ _ hU1 hU2
  refine Set.Finite.induction_on_subset _ hU2 ?empty ?insert
  · simp_all
  · intro _ _ hS _ _ ih
    rw [Set.sInter_insert]
    apply hAB
    · exact hU1 hS
    · exact ih

def Closed [Topology X] (A: Set X): Prop :=
  Open Aᶜ

def Continuous [Topology X] [Topology Y] (f: X → Y): Prop :=
  ∀ V, Open V → Open (f ⁻¹' V)

class Distance (D: Type u) where

class Metric (X: Type u) (D: outParam (Type v)) [Distance D] where
  distance: X → X → D

instance (X: Type u) (D: Type v) [Distance D] [Metric X D]: Topology X :=
  sorry


example [Distance D] [Metric X D] [Metric Y D] (f: X → Y) (h: Continuous f): True :=
  sorry
