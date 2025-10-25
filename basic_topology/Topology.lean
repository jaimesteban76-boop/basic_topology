import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Lattice

set_option linter.style.commandStart false

variable {X Y: Type*}

/-

Definition of topological space. Like for metric spaces :
- Given a type X and a collection of subsets 𝒯, `IsTopology 𝒯` is the statement that 𝒯 forms a topology.
- `Topology X` is the type of all topologies on `X`.
- `TopologicalSpace` is the type of all topological spaces.

For simplicity I guess we will work with `IsTopology` mostly.

-/

abbrev Family (X: Type u): Type u :=
  Set (Set X)

structure IsTopology (𝒯: Family X): Prop where
  sUnion: ∀ 𝒰 ⊆ 𝒯, ⋃₀ 𝒰 ∈ 𝒯
  finite_sInter: ∀ 𝒰 ⊆ 𝒯, Finite 𝒰 → ⋂₀ 𝒰 ∈ 𝒯

structure Topology (X: Type u) where
  opensets: Family X
  is_topology: IsTopology opensets

structure TopologicalSpace: Type (u + 1) where
  points: Type u
  topology: Topology points

theorem empty_open {𝒯: Family X} (h𝒯: IsTopology 𝒯): ∅ ∈ 𝒯 := by
  have: (∅: Set X) = ⋃₀ ∅ := by ext; simp
  rw [this]
  apply h𝒯.sUnion
  exact Set.empty_subset 𝒯

-- Binary unions and intersections of open sets are open
theorem binary_union_open {𝒯: Family X} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: A ∈ 𝒯) (hB: B ∈ 𝒯): A ∪ B ∈ 𝒯 := by
  have: A ∪ B = ⋃₀ {A, B} := by ext; simp
  rw [this]
  apply h𝒯.sUnion
  exact Set.pair_subset hA hB

-- The union of a sequence of open sets is open
theorem seq_union_open {𝒯: Family X} (h𝒯: IsTopology 𝒯) {A: ℕ → Set X} (h: ∀ n, A n ∈ 𝒯): Set.iUnion A ∈ 𝒯 := by
  apply h𝒯.sUnion
  exact Set.range_subset_iff.mpr h

-- theorem: finite intersection property is equivalent to binary intersections plus whole set
 theorem finite_inter_iff {T: Family X}: (∀ U ⊆ T, U.Finite → ⋂₀ U ∈ T) ↔ Set.univ ∈ T ∧ ∀ A ∈ T, ∀ B ∈ T, A ∩ B ∈ T := by
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

theorem univ_open {𝒯: Family X} (h𝒯: IsTopology 𝒯): Set.univ ∈ 𝒯 := by
  exact (finite_inter_iff.mp h𝒯.finite_sInter).left

theorem binary_inter_open {𝒯: Family X} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: A ∈ 𝒯) (hB: B ∈ 𝒯): A ∩ B ∈ 𝒯 := by
  exact (finite_inter_iff.mp h𝒯.finite_sInter).right _ hA _ hB



def openset (𝒯: Family X) (A: Set X): Prop :=
  A ∈ 𝒯

def closedset (𝒯: Family X) (A: Set X): Prop :=
  openset 𝒯 Aᶜ

def clopenset (𝒯: Family X) (A: Set X): Prop :=
  openset 𝒯 A ∧ closedset 𝒯 A

-- pointless definition but sometimes feels right
def opensets (𝒯: Family X): Family X :=
  𝒯

def closedsets (𝒯: Family X): Family X :=
  {A | closedset 𝒯 A}

def clopensets (𝒯: Family X): Family X :=
  opensets 𝒯 ∩ closedsets 𝒯

theorem closedset_sInter {𝒯: Family X} (h𝒯: IsTopology 𝒯): ∀ 𝒰 ⊆ closedsets 𝒯, ⋂₀ 𝒰 ∈ closedsets 𝒯 := by
  sorry

theorem closedset_finite_sUnion {𝒯: Family X} (h𝒯: IsTopology 𝒯): ∀ 𝒰 ⊆ closedsets 𝒯, Finite 𝒰 → ⋃₀ 𝒰 ∈ closedsets 𝒯 := by
  sorry

theorem binary_union_closed {𝒯: Family X} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: closedset 𝒯 A) (hB: closedset 𝒯 B): closedset 𝒯 (A ∪ B) := by
  rw [closedset, Set.compl_union]
  exact binary_inter_open h𝒯 hA hB

theorem binary_inter_closed {𝒯: Family X} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: closedset 𝒯 A) (hB: closedset 𝒯 B): closedset 𝒯 (A ∩ B) := by
  rw [closedset, Set.compl_inter]
  exact binary_union_open h𝒯 hA hB

-- The union of a sequence of open sets is open
theorem seq_inter_closed {𝒯: Family X} (h𝒯: IsTopology 𝒯) {A: ℕ → Set X} (h: ∀ n, closedset 𝒯 (A n)): closedset 𝒯 (Set.iInter A) := by
  exact closedset_sInter h𝒯 _ (Set.range_subset_iff.mpr h)

-- the set of all subsets is a topology, aka the discrete topology
theorem discrete_is_topology (X: Type*): IsTopology (@Set.univ (Set X)) := {
  sUnion := by intros; trivial
  finite_sInter := by intros; trivial
}

-- the indiscrete (aka antidiscrete) topology! it is slightly less trivial to prove..
theorem indiscrete_is_topology (X: Type*): IsTopology {∅, @Set.univ X} := {
  sUnion := by apply Set.sUnion_mem_empty_univ
  finite_sInter := by
    intro 𝒰 h𝒰 _
    simp
    by_cases h: ∅ ∈ 𝒰
    · apply Or.inl
      exact Set.subset_eq_empty (fun x hx ↦ hx ∅ h) rfl
    · apply Or.inr
      intro _ hU
      match h𝒰 hU with
      | Or.inl h' => rw [h'] at hU; contradiction
      | Or.inr h' => exact h'
}



-- the Sierpiński topology define on Bool with {true} open
def sierpiński_opensets: Set (Set Bool) :=
 {{}, {true}, {false, true}}

-- Helper lemma: in the sierpinski topology a set is open iff. it's subsingleton or the whole space.
theorem sierpiński_open_iff (A: Set Bool): A ∈ sierpiński_opensets ↔ A ⊆ {true} ∨ A = Set.univ := by
  constructor
  · intro h
    rcases h with _ | _ | _
    repeat simp_all
  · intro; simp [sierpiński_opensets]
    by_cases false ∈ A <;> by_cases true ∈ A
    repeat simp_all
    · right; left; ext x; match x with
      | false => simp_all
      | true => simp_all
    · left; ext x; match x with
      | false => simp_all
      | true => simp_all

-- this proof was very difficult despite being a space containig 2 points...
theorem sierpiński_is_topology: IsTopology sierpiński_opensets := {
  sUnion := by
    intro 𝒰 h𝒰
    by_cases h: ∀ U ∈ 𝒰, U ⊆ {true} -- either all of them are subsingleton, or one of them is the universe
    · apply (sierpiński_open_iff _).mpr
      exact Or.inl (Set.sUnion_subset h)
    · apply (sierpiński_open_iff _).mpr
      apply Or.inr
      simp at h
      obtain ⟨U, hU⟩ := h
      apply Set.univ_subset_iff.mp
      apply Set.subset_sUnion_of_subset _ U
      · have: U = Set.univ := by
          match (sierpiński_open_iff U).mp (h𝒰 hU.left) with
          | Or.inl _ => simp_all
          | Or.inr h => exact h
        rw [this]
      · exact hU.left
  finite_sInter := by
    intro 𝒰 h𝒰 _ -- either all of them are universes, or at least one is subsingleton
    by_cases h: ∀ U ∈ 𝒰, U = Set.univ
    · apply (sierpiński_open_iff _).mpr
      exact Or.inr (Set.sInter_eq_univ.mpr h)
    · simp at h
      obtain ⟨U, hU⟩ := h
      have: U ⊆ {true} := by have := ((sierpiński_open_iff U).mp (h𝒰 hU.left)); simp_all
      have: ⋂₀ 𝒰 ⊆ {true} := by simp; exists U; simp_all
      apply (sierpiński_open_iff _).mpr
      exact Or.inl this
}

def sierpiński_topology: Topology Bool := {
  opensets := sierpiński_opensets
  is_topology := sierpiński_is_topology
}
