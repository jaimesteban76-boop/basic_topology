import basic_topology.Topology

variable {X Y: Type*} {𝒯: Family X}

def neighborhood (𝒯: Family X) (N: Set X) (x: X): Prop :=
  ∃ U ∈ 𝒯, x ∈ U ∧ U ⊆ N

def OpenNeighborhood (𝒯: Family X) (U: Set X) (x: X): Prop :=
  x ∈ U ∧ U ∈ 𝒯

theorem OpenNeighborhood.neighborhood (h: OpenNeighborhood 𝒯 U x): neighborhood 𝒯 U x := by
  exists U
  repeat' constructor
  exact h.2
  exact h.1
  exact fun ⦃a⦄ a ↦ a

-- The whole space is a neighborhood of every point
theorem neighborhood_univ (h: IsTopology 𝒯) (x: X): neighborhood 𝒯 Set.univ x := by
  exists Set.univ
  simp
  exact univ_open h

-- If x ∈ U and U is open then U is a neighborhood of x
theorem open_neighborhood {U: Set X} {x: X} (h1: x ∈ U) (h2: U ∈ 𝒯): neighborhood 𝒯 U x := by
  exists U

-- A set is open iff. it is a neighborhood of all its points.
theorem open_iff_neighborhood_of_all_points (h𝒯: IsTopology 𝒯) (A: Set X): Open 𝒯 A ↔ ∀ x ∈ A, neighborhood 𝒯 A x := by
  constructor
  · intro hA x hx
    exists A
  · intro h
    have: A = ⋃₀ {U | ∃ x ∈ A, U ∈ 𝒯 ∧ x ∈ U ∧ U ⊆ A} := by
      ext y
      constructor
      · intro hy
        rcases h y hy with ⟨U, hU, hyU, hUA⟩
        refine Set.mem_sUnion.mpr ⟨U, ?_, hyU⟩
        exact ⟨y, hy, hU, hyU, hUA⟩
      · intro hy
        rcases Set.mem_sUnion.mp hy with ⟨U, ⟨x, hxA, hU, hxU, hUA⟩, hyU⟩
        exact hUA hyU
    rw [this]
    apply h𝒯.sUnion
    intro U hU
    rcases hU with ⟨x,hx⟩
    rcases hx with ⟨h1,h2,h3⟩
    exact h2

-- In the discrete topology, N is a neighborhood of x iff x ∈ N.
theorem discrete_neighborhood_iff (N: Set X) (x: X): neighborhood Set.univ N x ↔ x ∈ N := by
  constructor
  · intro ⟨U, _, hU2, hU3⟩
    exact hU3 hU2
  · intro
    exists {x}
    simp_all

-- In the indiscrete topology, N is a neighborhood of x iff N is the whole space
theorem indiscrete_neighborhood_iff (N: Set X) (x: X): neighborhood {∅, Set.univ} N x ↔ N = Set.univ := by
  constructor
  · intro ⟨_, _, hU2, _⟩
    simp_all [ne_of_mem_of_not_mem' hU2]
  · intro h
    rw [h]
    apply neighborhood_univ (indiscrete_is_topology X)

-- The set of neighborhoods of a point
def Nbhds (𝒯: Family X) (x: X): Family X :=
 {N | neighborhood 𝒯 N x}

-- neighborhood properties
-- N1: if A is a neighborhood and A ⊆ B then B is a neighborhood
theorem neighborhood_upward_closed (x: X) {A B: Set X} (h1: neighborhood 𝒯 A x) (h2: A ⊆ B): neighborhood 𝒯 B x := by
  obtain ⟨U, hU1, hU2, hU3⟩ := h1
  exists U
  repeat' constructor
  · exact hU1
  · exact hU2
  · exact le_trans hU3 h2

-- N2: every finite intersection of neighborhoods is a neighborhood
theorem neighborhood_binary_inter {𝒯: Family X} {x: X} {A: Set X} (h𝒯: IsTopology 𝒯) {B: Set X} (hA: neighborhood 𝒯 A x)(hB: neighborhood 𝒯 B x): neighborhood 𝒯 (A ∩ B) x := by
  simp [neighborhood]
  obtain ⟨ U,⟨hU1,hU2,hU3⟩⟩  := hA
  obtain ⟨ V,⟨hV1,hV2,hV3⟩⟩ := hB
  use U∩V
  repeat constructor
  · exact binary_inter_open h𝒯 hU1 hV1
  · constructor
    · exact Set.mem_inter hU2 hV2
    · constructor
      · have: U∩V⊆ U := by exact Set.inter_subset_left
        exact fun ⦃a⦄ a_1 ↦ hU3 (this a_1)
      · have: U∩V⊆ V := by exact Set.inter_subset_right
        exact fun ⦃a⦄ a_1 ↦ hV3 (this a_1)

-- N2: every finite intersection of neighborhoods is a neighborhood
theorem neighborhood_finite_inter {𝒯: Family X} (h𝒯: IsTopology 𝒯) (x: X) (𝒩: Family X) (h1: 𝒩 ⊆ Nbhds 𝒯 x) (h2: Finite 𝒩): ⋂₀ 𝒩 ∈ Nbhds 𝒯 x := by
  apply finite_inter_iff.mpr
  · simp [Nbhds]
    constructor
    · apply neighborhood_univ h𝒯
    · intro _ hA _ hB
      exact neighborhood_binary_inter h𝒯 hA hB
  · exact h1
  · exact h2

-- N3: x belongs to all its neighborhoods

theorem neighborhood_mem {𝒯: Family X} {x: X} {N: Set X} (h: neighborhood 𝒯 N x): x ∈ N := by
  obtain ⟨_, _, hU2, hU3⟩ := h
  exact hU3 hU2

-- N4: if V is a neighborhood of x, there exists a neighborhood W of x
-- such that for all y in W, V is a neighborhood of y.
theorem neighborhood_linking {𝒯: Family X} {x: X} {V: Set X} (h: neighborhood 𝒯 V x): ∃ W ∈ Nbhds 𝒯 x, ∀ y ∈ W, V ∈ Nbhds 𝒯 y := by
  obtain ⟨U, hU₁, hU₂, _⟩ := h
  exists U
  constructor
  · apply open_neighborhood hU₂ hU₁
  · intro y hy
    exists U

-- preceding 4 properties packaged as follows :
structure neighborhood_axioms (𝒩: X → Family X): Prop where
  upward_closed: ∀ x, ∀ A B: Set X, A ∈ 𝒩 x → A ⊆ B → B ∈ 𝒩 x
  finite_inter: ∀ x, ∀ 𝒰 ⊆ 𝒩 x, Finite 𝒰 → ⋂₀ 𝒰 ∈ 𝒩 x
  point_mem: ∀ x, ∀ N ∈ 𝒩 x, x ∈ N
  linking: ∀ x, ∀ V ∈ 𝒩 x, ∃ W ∈ 𝒩 x, ∀ y ∈ W, V ∈ 𝒩 y -- rename

-- Nhbds satisties these as we just showed
theorem nbhds_obeys_neighborhood_axioms {𝒯: Family X} (h𝒯: IsTopology 𝒯): neighborhood_axioms (Nbhds 𝒯) := {
  upward_closed := neighborhood_upward_closed
  finite_inter := neighborhood_finite_inter h𝒯
  point_mem := fun _ _ => neighborhood_mem
  linking := fun _ _ => neighborhood_linking
}

def neighborhood_topology (𝒩: X → Family X): Family X :=
 {U | ∀ x ∈ U, U ∈ 𝒩 x}

theorem neighborhood_axioms_unique_topology (𝒩: X → Family X) (h𝒩: neighborhood_axioms 𝒩): ∃! 𝒯, (IsTopology 𝒯 ∧ 𝒩 = Nbhds 𝒯) := by
  exists neighborhood_topology 𝒩
  repeat' (apply And.intro)
  · sorry -- show that `neighborhood_topology 𝒩` is a topology
  · sorry -- show that `𝒩 = Nbhds (neighborhood_topology 𝒩)`
  · intro 𝒩' ⟨h1, h2⟩
    sorry -- suppose 𝒩' is a topology and 𝒩 = Nbhds 𝒩', want to show 𝒩' = neighborhood_topology 𝒩
