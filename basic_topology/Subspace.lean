import basic_topology.Topology

variable {X Y: Type*}

-- Given A ⊆ X and U ⊆ A returns U ⊆ X.
def subspace_up {A: Set X} (U: Set A): Set X :=
  Subtype.val '' U

-- Given A ⊆ X and U ⊆ X returns U ∩ A ⊆ A.
def subspace_down (A: Set X) (U: Set X): Set A :=
  Subtype.val ⁻¹' (U ∩ A)

-- -- Given A ⊆ X and T ⊆ 𝒫(A) retursn T ⊆ 𝒫(X).
def supspace {A: Set X} (T: Set (Set A)): Family X :=
  subspace_down A ⁻¹' T

-- Given A ⊆ X and T ⊆ 𝒫(X) retursn T ⊆ 𝒫(A).
-- i.e. the subspace topology
def subspace (T: Family X) (A: Set X): Set (Set A) :=
  subspace_down A '' T

-- basic helpers
theorem subspace_open_exists {T: Family X} {A: Set X} {V: Set A} (hV: V ∈ subspace T A): ∃ U ∈ T, subspace_down A U = V := by
  simp_all [subspace_down, subspace]

theorem subspace_open_if {T: Family X} {A U: Set X} (hU: U ∈ T): subspace_down A U ∈ subspace T A := by
  simp [subspace, subspace_down]
  exists U

-- theorem subspace_open (T: Family X) (A: Set X) {U: Set X} (hU: U ∈ T) :
--   Subtype.val ⁻¹' (U ∩ A) ∈ subspace T A := by
--   exists U


-- TODO: show if U is open in T then U ∩ A is open in A

theorem subspace_topology_is_topology {T: Family X} (hT: IsTopology T) (A: Set X) :
  IsTopology (subspace T A) := by
  sorry
