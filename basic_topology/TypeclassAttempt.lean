import basic_topology.Relation
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Lattice

set_option linter.style.multiGoal false

variable {X Y Z: Type*}

/-

Definition of topological space. Like for metric spaces :
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

structure TopologicalSpace: Type (u + 1) where
  points: Type u
  topology: Topology points

def TopologicalSpace': Type (u + 1) :=
  Σ X: Type u, Topology X

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

def ContinuousAt [Topology X] [Topology Y] (f: X → Y) (x: X): Prop :=
  ∀ V, Open V → Open (f ⁻¹' V)

def Continuous [Topology X] [Topology Y] (f: X → Y): Prop :=
  ∀ V, Open V → Open (f ⁻¹' V)

def Function.id {X: Type u}: X → X :=
  fun x => x

theorem Continuous.id [Topology X]: Continuous (@Function.id X) := by
  intro V
  exact fun h => h

theorem Continuous.comp [Topology X] [Topology Y] [Topology Z] {f: X → Y} {g: Y → Z}
  (hf: Continuous f) (hg: Continuous g): Continuous (g ∘ f) := by
  sorry

class Distance (D: Type u) where

class Metric (X: Type u) (D: outParam (Type v)) [Distance D] where
  distance: X → X → D

instance (X: Type u) (D: Type v) [Distance D] [Metric X D]: Topology X :=
  sorry


example [Distance D] [Metric X D] [Metric Y D] (f: X → Y) (h: Continuous f): True :=
  sorry

def Connected (T: Topology X): Prop :=
  ∀ U V: Set X, Open U → Open V → U.Nonempty → V.Nonempty → U ∪ V = Set.univ → (U ∩ V).Nonempty

noncomputable def Function.Inverse {f: X → Y} (h: Function.Bijective f): Y → X :=
  Classical.choose (Function.bijective_iff_has_inverse.mp h)

structure Homeomorphism (X: Type u) (Y: Type v) [Topology X] [Topology Y] where
  map: X → Y
  inv: Y → X
  map_continuous: Continuous map
  inv_continuous: Continuous inv
  id_left: inv ∘ map = id
  id_right: map ∘ inv = id

def Homeomorphism.id [Topology X]: Homeomorphism X X := {
  map := Function.id
  inv := Function.id
  map_continuous := Continuous.id
  inv_continuous := Continuous.id
  id_left := rfl
  id_right := rfl
}

def Homeomorphism.comp [Topology X] [Topology Y] [Topology Z] (f: Homeomorphism X Y) (g: Homeomorphism Y Z): Homeomorphism X Z := {
  map := g.map ∘ f.map
  inv := f.inv ∘ g.inv
  map_continuous := Continuous.comp f.map_continuous g.map_continuous
  inv_continuous := Continuous.comp g.inv_continuous f.inv_continuous
  id_left := by
    rw [Function.comp_assoc, ←Function.comp_assoc g.inv]
    simp [g.id_left, f.id_left]
  id_right := by
    rw [Function.comp_assoc, ←Function.comp_assoc f.map]
    simp [f.id_right, g.id_right]
}

def Homeomorphic (X: Type u) (Y: Type v) [Topology X] [Topology Y]: Prop :=
  Nonempty (Homeomorphism X Y)

def Homeomorphic.relation: Endorelation TopologicalSpace :=
  fun X Y => @Homeomorphic _ _ X.topology Y.topology

theorem Homeomorphic.reflexive: Reflexive' Homeomorphic.relation := by
  intro X
  use id, id
  sorry
  sorry
  rfl; rfl

theorem Homeomorphic.symmetric: Symmetric' Homeomorphic.relation := by
  intro X Y h
  sorry

theorem Homeomorphic.transitive: Transitive' Homeomorphic.relation := by
  intro X Y h
  sorry

theorem Homeomorphic.equivalence: Equivalence Homeomorphic.relation := by
  sorry

-- a property is called a topological property if it's preserved under homeomorphism
def TopologicalProperty (P: TopologicalSpace → Prop): Prop :=
  ∀ X Y, Homeomorphic.relation X Y → P X → P Y
