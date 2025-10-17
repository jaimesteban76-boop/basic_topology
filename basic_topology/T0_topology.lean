
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

structure IsTopology (𝒯: Set (Set X)): Prop where
  sUnion: ∀ 𝒰 ⊆ 𝒯, ⋃₀ 𝒰 ∈ 𝒯
  finite_sInter: ∀ 𝒰 ⊆ 𝒯, Finite 𝒰 → ⋂₀ 𝒰 ∈ 𝒯

structure Topology (X: Type u) where
  opensets: Set (Set X)
  is_topology: IsTopology opensets

structure TopologicalSpace: Type (u + 1) where
  points: Type u
  topology: Topology points

theorem empty_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): ∅ ∈ 𝒯 := by
  have: (∅: Set X) = ⋃₀ ∅ := by ext; simp
  rw [this]
  apply h𝒯.sUnion
  exact Set.empty_subset 𝒯

theorem univ_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): Set.univ ∈ 𝒯 := by
  have: (@Set.univ X) = ⋂₀ ∅ := by ext; simp
  rw [this]
  apply h𝒯.finite_sInter
  · exact Set.empty_subset 𝒯
  · exact Finite.of_subsingleton

-- Binary unions and intersections of open sets are open
theorem binary_union_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: A ∈ 𝒯) (hB: B ∈ 𝒯): A ∪ B ∈ 𝒯 := by
  have: A ∪ B = ⋃₀ {A, B} := by ext; simp
  rw [this]
  apply h𝒯.sUnion
  exact Set.pair_subset hA hB

theorem binary_inter_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: A ∈ 𝒯) (hB: B ∈ 𝒯): A ∩ B ∈ 𝒯 := by
  have: A ∩ B = ⋂₀ {A, B} := by ext; simp
  rw [this]
  apply h𝒯.finite_sInter
  · exact Set.pair_subset hA hB
  · exact Finite.Set.finite_insert A {B}

-- The union of a sequence of open sets is open
theorem seq_union_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A: ℕ → Set X} (h: ∀ n, A n ∈ 𝒯): Set.iUnion A ∈ 𝒯 := by
  apply h𝒯.sUnion
  exact Set.range_subset_iff.mpr h

-- theorem: finite intersection property is equivalent to binary intersections plus whole set
 theorem finite_inter_iff (T: Set (Set X)): (∀ U ⊆ T, U.Finite → ⋂₀ U ∈ T) ↔ Set.univ ∈ T ∧ ∀ A ∈ T, ∀ B ∈ T, A ∩ B ∈ T := by
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

def openset (𝒯: Set (Set X)) (A: Set X): Prop :=
  A ∈ 𝒯

def closedset (𝒯: Set (Set X)) (A: Set X): Prop :=
  Aᶜ ∈ 𝒯

def clopenset (𝒯: Set (Set X)) (A: Set X): Prop :=
  openset 𝒯 A ∧ closedset 𝒯 A

-- pointless definition but sometimes feels right
def opensets (𝒯: Set (Set X)): Set (Set X) :=
  𝒯

def closedsets (𝒯: Set (Set X)): Set (Set X) :=
  {A | closedset 𝒯 A}

def clopensets (𝒯: Set (Set X)): Set (Set X) :=
  opensets 𝒯 ∩ closedsets 𝒯

theorem closedset_sInter {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): ∀ 𝒰 ⊆ closedsets 𝒯, ⋂₀ 𝒰 ∈ closedsets 𝒯 := by
  sorry

theorem closedset_finite_sUnion {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): ∀ 𝒰 ⊆ closedsets 𝒯, Finite 𝒰 → ⋃₀ 𝒰 ∈ closedsets 𝒯 := by
  sorry

theorem binary_union_closed {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: closedset 𝒯 A) (hB: closedset 𝒯 B): closedset 𝒯 (A ∪ B) := by
  sorry

theorem binary_inter_closed {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: closedset 𝒯 A) (hB: closedset 𝒯 B): closedset 𝒯 (A ∩ B) := by
  sorry

-- The union of a sequence of open sets is open
theorem seq_inter_closed {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A: ℕ → Set X} (h: ∀ n, closedset 𝒯 (A n)): closedset 𝒯 (Set.iInter A) := by
  sorry

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





-- Definition: ℬ is a base for 𝒯 if every open set of 𝒯 is a union of sets from ℬ
def base (𝒯 ℬ: Set (Set X)): Prop :=
  ℬ ⊆ 𝒯 ∧ ∀ U ∈ 𝒯, ∃ 𝒰 ⊆ ℬ, U = ⋃₀ 𝒰

-- Every topology is a base for itself.
theorem base_self (𝒯: Set (Set X)): base 𝒯 𝒯 := by
constructor
· rfl
· intro U hU
  exists {U}
  constructor
  · exact Set.singleton_subset_iff.mpr hU
  · ext; simp

-- ℬ is a base for 𝒯 iff. ∀ U ∈ 𝒯, ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ⊆ U. Does not require 𝒯 to be a topology.
theorem base_iff (𝒯 ℬ: Set (Set X)): base 𝒯 ℬ ↔ ℬ ⊆ 𝒯 ∧ ∀ U ∈ 𝒯, ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ U := by
  constructor
  · intro h
    constructor
    · exact h.left
    · intro U hU x hx
      obtain ⟨C, hC⟩ := h.right U hU
      rw [hC.right] at hx
      obtain ⟨Bx, hBx⟩ := hx
      exists Bx
      repeat' constructor
      · exact hC.left hBx.left
      · exact hBx.right
      · rw [hC.right]
        intro x hx
        apply Set.mem_sUnion.mpr
        exists Bx
        constructor
        · exact hBx.left
        · exact hx
  · intro h
    constructor
    · exact h.left
    · intro U hU
      exists {B ∈ ℬ | B ⊆ U}
      simp
      ext x
      constructor
      · intro hx
        obtain ⟨B, _, _, _⟩ := h.right U hU x hx
        exists B
      · intro  ⟨B, ⟨_, hB2⟩, hB3⟩
        exact hB2 hB3

-- The set ℬ = {{x} | x ∈ X} is a base for the discrete topology.
theorem discrete_base (X: Type*): base (@Set.univ (Set X)) (⋃ x, {x}) := by
  apply (base_iff _ _).mpr
  constructor
  · exact fun _ _ => trivial
  · intro U hU x hx
    exists {x}
    repeat' (apply And.intro)
    · simp
    · rfl
    · exact Set.singleton_subset_iff.mpr hx

-- The set ℬ = {{X}} is a base for the indiscrete topology.
theorem indiscrete_base (X: Type*): base {∅, @Set.univ X} {@Set.univ X} := by
  constructor
  · apply Set.subset_insert
  · intro U hU
    match hU with
    | Or.inl _ => exists ∅; simp_all
    | Or.inr _ => exists {Set.univ}; simp_all

-- sierpiński base
theorem sierpiński_base : base (sierpiński_opensets) {{true}, {false, true}} := by
  constructor
  · simp [sierpiński_opensets]
  · intro U hU
    by_cases false ∈ U
    · exists {{false, true}}
      constructor
      · apply Set.subset_insert
      · by_cases true ∈ U <;>
          cases hU with
          | inl => simp_all
          | inr h => cases h with
            | inl => simp_all
            | inr => simp_all
    · by_cases ht: true ∈ U
      · exists {{true}}
        cases hU with
        | inl => simp_all
        | inr h => cases h with
          | inl => simp_all
          | inr => simp_all
      · exists {}
        cases hU with
        | inl => simp_all
        | inr h => cases h with
          | inl => simp_all
          | inr => simp_all

-- We say ℬ "is a base" if there exists a topology for which it is a base.
def is_base (ℬ: Set (Set X)): Prop :=
  ∃ 𝒯, IsTopology 𝒯 ∧ base 𝒯 ℬ

-- If 𝒯 is a topology then 𝒯 is a base... for itself.
theorem topology_is_base {𝒯: Set (Set X)} (h: IsTopology 𝒯): is_base 𝒯 := by
  exists 𝒯
  exact ⟨h, base_self 𝒯⟩

-- If ℬ is a base for a topology 𝒯 is a topology then ℬ is a base... for 𝒯.
theorem base_is_base {𝒯 ℬ: Set (Set X)} (h1: IsTopology 𝒯) (h2: base 𝒯 ℬ): is_base ℬ := by
  exists 𝒯

-- Given an arbitrary collection ℬ, `unions ℬ` is the set of unions obtained of sets from ℬ.
def unions (ℬ: Set (Set X)): Set (Set X) :=
  ⋃ 𝒰 ⊆ ℬ, {⋃₀ 𝒰}

-- some simple theorems about `unions`
theorem unions_sub (ℬ: Set (Set X)): ℬ ⊆ unions ℬ := by
  intro U _
  simp [unions]
  exists {U}
  simp_all

theorem unions_mono {ℬ ℬ': Set (Set X)} (h: ℬ ⊆ ℬ'): unions ℬ ⊆ unions ℬ' := by
  simp_all [unions]
  intro B hB
  exists B
  constructor
  · exact le_trans hB h
  · rfl

-- the unions operator is idempotent
-- forward direction is obvious
-- for the reverse, the idea is if U = ⋃ i, V i and each V i = ⋃ j, B i j then U = ⋃ i j, B i j
theorem unions_idem {ℬ: Set (Set X)}: unions ℬ = unions (unions ℬ) := by
  apply le_antisymm
  · apply unions_sub
  · intro U hU
    simp_all [unions]
    obtain ⟨a, ha1, ha2⟩ := hU
    simp_all
    rw [←ha2]
    exists a
    sorry

theorem unions_topology {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): 𝒯 = unions 𝒯 := by
  apply le_antisymm
  · apply unions_sub
  · intro U hU
    simp_all [unions]
    obtain ⟨𝒰, h𝒰1, h𝒰2⟩ := hU
    rw [h𝒰2]
    exact h𝒯.sUnion 𝒰 h𝒰1

theorem base_unions (ℬ: Set (Set X)): base (unions ℬ) ℬ := by
  constructor
  · apply unions_sub
  · intro U hU
    simp_all [unions]

theorem base_iff_unions {𝒯 ℬ: Set (Set X)}: base 𝒯 ℬ ↔ ℬ ⊆ 𝒯 ∧ 𝒯 = unions ℬ := by
  constructor
  · intro h
    constructor
    · exact h.left
    · sorry
  · sorry

-- ℬ is a base iff. `unions ℬ` is a topology.
theorem is_base_iff_unions_topology (ℬ: Set (Set X)): is_base ℬ ↔ IsTopology (unions ℬ) := by
  --simp [unions]
  apply Iff.intro
  · intro ⟨𝒯, h𝒯₁, h𝒯₂, h𝒯₃⟩
    have: 𝒯 = unions ℬ := by
      apply le_antisymm


      sorry -- exact?
      rw [unions_topology h𝒯₁]
      exact unions_mono h𝒯₂
    rw [←this]
    exact h𝒯₁
  · intro h
    exists unions ℬ
    constructor
    · exact h
    · constructor
      · apply unions_sub
      · simp [unions]

structure base_conditions (ℬ: Set (Set X)): Prop where
  B1: X = ⋃₀ ℬ
  B2: ∀ B' ∈ ℬ, ∀ B'' ∈ ℬ, ∀ x ∈ B' ∩ B'', ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ B' ∩ B''

theorem is_base_iff_base_conditions (ℬ: Set (Set X)): is_base ℬ ↔ base_conditions ℬ := by
  constructor
  · intro ⟨T, hT₁, hT₂⟩
    constructor
    · sorry
    · intro B'  hb' B'' hB'' x hx
      sorry
  · intro h
    sorry

-- TODO: suppose T is generated by B. Then U is open iff. forall x in U, exists B in B, x in B sub U.





def neighborhood (𝒯: Set (Set X)) (N: Set X) (x: X): Prop :=
  ∃ U ∈ 𝒯, x ∈ U ∧ U ⊆ N

-- The whole space is a neighborhood of every point
theorem neighborhood_univ {𝒯: Set (Set X)} (h: IsTopology 𝒯) (x: X): neighborhood 𝒯 Set.univ x := by
  exists Set.univ
  simp
  exact univ_open h

-- If x ∈ U and U is open then U is a neighborhood of x
theorem open_neighborhood (𝒯: Set (Set X)) {U: Set X} {x: X} (h1: x ∈ U) (h2: U ∈ 𝒯): neighborhood 𝒯 U x := by
  exists U

-- A set is open iff. it is a neighborhood of all its points.
theorem open_iff_neighborhood_of_all_points {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A: Set X): A ∈ 𝒯 ↔ ∀ x ∈ A, neighborhood 𝒯 A x := by
  constructor
  · intro hA x hx
    exists A
  · intro h
    have : A = ⋃₀ {U | ∃ x ∈ A, U ∈ 𝒯 ∧ x ∈ U ∧ U ⊆ A} := by
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
theorem discrete_neighborhood_iff {X: Type*} (N: Set X) (x: X): neighborhood Set.univ N x ↔ x ∈ N := by
  constructor
  · intro ⟨U, _, hU2, hU3⟩
    exact hU3 hU2
  · intro
    exists {x}
    simp_all

-- In the indiscrete topology, N is a neighborhood of x iff N is the whole space
theorem indiscrete_neighborhood_iff {X: Type*} (N: Set X) (x: X): neighborhood {∅, Set.univ} N x ↔ N = Set.univ := by
  constructor
  · intro ⟨_, _, hU2, _⟩
    simp_all [ne_of_mem_of_not_mem' hU2]
  · intro h
    rw [h]
    apply neighborhood_univ (indiscrete_is_topology X)

-- The set of neighborhoods of a point
def Nbhds (𝒯: Set (Set X)) (x: X): Set (Set X) :=
 {N | neighborhood 𝒯 N x}

-- neighborhood properties
-- N1: if A is a neighborhood and A ⊆ B then B is a neighborhood
theorem neighborhood_upward_closed {𝒯: Set (Set X)} (x: X) {A B: Set X} (h1: neighborhood 𝒯 A x) (h2: A ⊆ B): neighborhood 𝒯 B x := by
  obtain ⟨U, hU1, hU2, hU3⟩ := h1
  exists U
  repeat' constructor
  · exact hU1
  · exact hU2
  · exact le_trans hU3 h2

-- N2: every finite intersection of neighborhoods is a neighborhood
theorem neighborhood_finite_inter {𝒯: Set (Set X)} (x: X) (𝒩: Set (Set X)) (h1: 𝒩 ⊆ Nbhds 𝒯 x) (h2: Finite 𝒩): ⋂₀ 𝒩 ∈ Nbhds 𝒯 x := by
  sorry

-- N3: x belongs to all its neighborhoods
theorem neighborhood_mem {𝒯: Set (Set X)} {x: X} {N: Set X} (h: neighborhood 𝒯 N x): x ∈ N := by
  obtain ⟨_, _, hU2, hU3⟩ := h
  exact hU3 hU2

-- N4: if V is a neighborhood of x, there exists a neighborhood W of x such that for all y in W, V is a neighborhood of y.
theorem neighborhood_N4 {𝒯: Set (Set X)} {x: X} {V: Set X} (h: neighborhood 𝒯 V x): ∃ W ∈ Nbhds 𝒯 x, ∀ y ∈ W, V ∈ Nbhds 𝒯 y := sorry

-- preceding 4 properties packaged as follows:
structure neighborhood_axioms (𝒩: X → Set (Set X)): Prop where
  upward_closed: ∀ x, ∀ A B: Set X, A ∈ 𝒩 x → A ⊆ B → B ∈ 𝒩 x
  finite_inter: ∀ x, ∀ 𝒰 ⊆ 𝒩 x, Finite 𝒰 → ⋂₀ 𝒰 ∈ 𝒩 x
  point_mem: ∀ x, ∀ N ∈ 𝒩 x, x ∈ N
  N4: ∀ x, ∀ V ∈ 𝒩 x, ∃ W ∈ 𝒩 x, ∀ y ∈ W, V ∈ 𝒩 y -- rename

-- Nhbds satisties these as we just showed
theorem nbhds_obeys_neighborhood_axioms {𝒯: Set (Set X)}: neighborhood_axioms (Nbhds 𝒯) := {
  upward_closed := neighborhood_upward_closed
  finite_inter := neighborhood_finite_inter
  point_mem := fun _ _ => neighborhood_mem
  N4 := fun _ _ => neighborhood_N4
}

def neighborhood_topology (𝒩: X → Set (Set X)): Set (Set X) :=
 {U | ∀ x ∈ U, U ∈ 𝒩 x}

theorem neighborhood_axioms_unique_topology (𝒩: X → Set (Set X)) (h𝒩: neighborhood_axioms 𝒩): ∃! 𝒯, (IsTopology 𝒯 ∧ 𝒩 = Nbhds 𝒯) := by
  exists neighborhood_topology 𝒩
  repeat' (apply And.intro)
  · sorry -- show that `neighborhood_topology 𝒩` is a topology
  · sorry -- show that `𝒩 = Nbhds (neighborhood_topology 𝒩)`
  · intro 𝒩' ⟨h1, h2⟩
    sorry -- suppose 𝒩' is a topology and 𝒩 = Nbhds 𝒩', want to show 𝒩' = neighborhood_topology 𝒩

-- TODO: define neighrbohood topology

-- TODO: fundamental neighborhood system aka neighborhood basis





def interior_point (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  neighborhood 𝒯 A x

def interior (𝒯: Set (Set X)) (A: Set X): Set X :=
 {x | interior_point 𝒯 A x}

-- Interior is monotone: if A ⊆ B then interior(A) ⊆ interior(B)
theorem interior_monotone (𝒯: Set (Set X)) {A B: Set X} (h: A ⊆ B): interior 𝒯 A ⊆ interior 𝒯 B := by
  simp [interior, interior_point]
  intro x hx
  exact neighborhood_upward_closed x hx h

-- Interior of the empty set is empty
theorem interior_empty (𝒯: Set (Set X)): interior 𝒯 ∅ = ∅ := by
  simp [interior, neighborhood, interior_point]

-- Interior of the universe is itself
theorem interior_univ {𝒯: Set (Set X)} (h: IsTopology 𝒯): interior 𝒯 Set.univ = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  intro _ _
  apply neighborhood_univ h

-- Interior is a subset of the original set
theorem interior_subset_self (𝒯: Set (Set X)) (A: Set X): interior 𝒯 A ⊆ A := by
  exact fun _ => neighborhood_mem

-- Interior is idempotent: interior(interior(A)) = interior(A)
theorem interior_idempotent (𝒯: Set (Set X)) (A: Set X): interior 𝒯 (interior 𝒯 A) = interior 𝒯 A := by
  apply le_antisymm
  · apply interior_subset_self
  · intro _ hx
    simp_all [interior, interior_point, neighborhood]
    obtain ⟨U, _, _, _⟩ := hx
    exists U
    repeat' constructor; simp_all
    intro _ _
    exists U

-- The interior is open
theorem interior_open {𝒯: Set (Set X)} (h: IsTopology 𝒯) (A: Set X): interior 𝒯 A ∈ 𝒯 := by
  apply (open_iff_neighborhood_of_all_points h (interior 𝒯 A)).mpr
  intro _ hx
  obtain ⟨U, hU₁, hU₂, _⟩ := hx
  exists U
  repeat' constructor
  · exact hU₁
  · exact hU₂
  · intro _ _
    exists U

-- The interior of A is largest open subset of A
theorem interior_largest_open_subset {𝒯: Set (Set X)} {A U: Set X} (h1: U ∈ 𝒯) (h2: U ⊆ A): U ⊆ interior 𝒯 A := by
  rw[interior]
  intro y hy
  refine Set.mem_setOf.mpr ?_
  rw[interior_point]
  rw[neighborhood]
  use U

-- The interior of A is the union of all open subsets of A.
-- (Is this proof beautiful or ugly?)
theorem interior_eq_union_open_subsets {𝒯: Set (Set X)} {A: Set X}: interior 𝒯 A = ⋃₀ {U ∈ 𝒯 | U ⊆ A} := by
  ext
  constructor
  · intro ⟨U, _, _, _⟩
    exists U
  · intro ⟨U, ⟨_, _⟩, _⟩
    exists U

-- A set is open iff. it is its own interior
theorem open_iff_eq_interior {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A: Set X): A ∈ 𝒯 ↔ A = interior 𝒯 A := by
  constructor
  · intro h
    apply Set.Subset.antisymm_iff.mpr
    constructor
    · apply interior_largest_open_subset h; rfl
    · apply interior_subset_self
  · intro h
    rw [h]
    apply interior_open h𝒯


-- interior (A ∩ B) = interior A ∩ interior B
theorem interior_inter_eq {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A B: Set X): interior 𝒯 (A ∩ B) = interior 𝒯 A ∩ interior 𝒯 B := by
  ext
  constructor
  · intro hx
    constructor
    · exact interior_monotone 𝒯 Set.inter_subset_left hx
    · exact interior_monotone 𝒯 Set.inter_subset_right hx
  · intro ⟨hA, hB⟩
    obtain ⟨U, hU₁, hU₂, hU₃⟩ := hA
    obtain ⟨V, hV₁, hV₂, hV₃⟩ := hB
    exists U ∩ V
    repeat' constructor
    · exact binary_inter_open h𝒯 hU₁ hV₁
    · exact hU₂
    · exact hV₂
    · exact Set.inter_subset_inter hU₃ hV₃

-- in the discrete topology, the interior of any set is itself
theorem discrete_interior (A: Set X): interior Set.univ A = A := by
  apply le_antisymm
  · apply interior_subset_self
  · intro
    apply (discrete_neighborhood_iff _ _).mpr

def adherent (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  ∀ N ∈ Nbhds 𝒯 x, Set.Nonempty (N ∩ A)

def closure (𝒯: Set (Set X)) (A: Set X): Set X :=
 {x | adherent 𝒯 A x}

-- Duality: closure(A) = interior(Aᶜ)ᶜ
-- Lets us prove results about closure in terms of interior
-- TODO: this proof is ugly!
theorem closure_eq (𝒯: Set (Set X)) (A: Set X): closure 𝒯 A = (interior 𝒯 Aᶜ)ᶜ := by
  ext x
  constructor
  · intro hx
    simp_all [interior, neighborhood, interior_point]
    intro U h1 h2 h3
    have := hx U (open_neighborhood 𝒯 h2 h1)
    have: U ∩ A = ∅ := by
      ext
      constructor
      · intro ⟨hz1, hz2⟩
        exact h3 hz1 hz2
      · exact False.elim
    simp_all [Set.not_nonempty_empty]
  · intro hx N hN
    simp_all [interior, neighborhood, interior_point]
    obtain ⟨U, hU₁, hU₂, hU₃⟩ := hN
    have := hx U hU₁ hU₂
    have: ∃ x, x ∈ U ∧ x ∉ Aᶜ := by exact Set.not_subset.mp (hx U hU₁ hU₂)
    obtain ⟨x, hx1, hx2⟩ := this
    exists x
    constructor
    exact hU₃ hx1
    exact Set.not_notMem.mp hx2

theorem closure_empty {𝒯: Set (Set X)} (h: IsTopology 𝒯): closure 𝒯 ∅ = ∅ := by
  simp [closure_eq, interior_univ h]

theorem closure_univ (𝒯: Set (Set X)): closure 𝒯 Set.univ = Set.univ := by
  simp [closure_eq, interior_empty]

theorem closure_compl_eq_compl_interior (𝒯: Set (Set X)) (A: Set X): closure 𝒯 Aᶜ = (interior 𝒯 A)ᶜ := by
  simp [closure_eq]

theorem compl_closure_eq_interior_compl (𝒯: Set (Set X)) (A: Set X): (closure 𝒯 A)ᶜ = interior 𝒯 Aᶜ := by
  simp [closure_eq]

theorem closure_monotone (𝒯: Set (Set X)) (A B: Set X){h:A⊆ B}: closure 𝒯 A ⊆ closure 𝒯 B := by
simp[closure, adherent]
intro x hx
intro U hU
apply hx at hU
have h1: U ∩ A ⊆ U ∩ B := by
  exact Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) h
exact Set.Nonempty.mono h1 hU

theorem closure_interior (𝒯: Set (Set X)) (A: Set X): closure 𝒯 (interior 𝒯 A) ⊆ closure 𝒯 A := by
  apply closure_monotone
  apply interior_subset_self

theorem closure_idempotent (𝒯: Set (Set X)) (A: Set X): closure 𝒯 (closure 𝒯 A) = closure 𝒯 A := by
  simp [closure_eq, interior_idempotent]

-- the closure is closed
theorem closure_closed {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A: Set X): closedset 𝒯 (closure 𝒯 A) := by
  simp [closure_eq, closedset]
  apply interior_open h𝒯

-- closure is a superset of the original
theorem closure_supset_self (𝒯: Set (Set X)) (A: Set X): A ⊆ closure 𝒯 A := by
  simp [closure_eq]
  apply Set.subset_compl_comm.mpr
  apply interior_subset_self

-- The closure of A is smallest closed supset of A
theorem closure_smallest_closed_supset {𝒯: Set (Set X)} {A U: Set X} (h1: Uᶜ ∈ 𝒯) (h2: A ⊆ U): closure 𝒯 A ⊆ U := by
  simp [closure_eq]
  have: Uᶜ ⊆ Aᶜ := Set.compl_subset_compl_of_subset h2
  have := interior_largest_open_subset h1 this
  exact Set.compl_subset_comm.mp this

theorem closure_eq_inter_closed_supsets {𝒯: Set (Set X)} {A: Set X}: closure 𝒯 A = ⋂₀ {U | Uᶜ ∈ 𝒯 ∧ A ⊆ U} := by
  simp [closure_eq]
  apply compl_inj_iff.mp
  simp
  rw [interior_eq_union_open_subsets]
  sorry

theorem closed_iff_eq_closure {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A: Set X): closedset 𝒯 A ↔ A = closure 𝒯 A := by
  simp [closure_eq, closedset]
  calc
    Aᶜ ∈ 𝒯 ↔ Aᶜ  = interior 𝒯 Aᶜ      := by apply open_iff_eq_interior h𝒯
         _ ↔ Aᶜᶜ = (interior 𝒯 Aᶜ)ᶜ   := by apply symm compl_inj_iff
         _ ↔ A   = (interior 𝒯 Aᶜ)ᶜ   := by rw [compl_compl]

-- closure (A ∪ B) = (closure A) ∪ (closure B)
theorem closure_union_eq {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A B: Set X): closure 𝒯 (A ∪ B) = closure 𝒯 A ∪ closure 𝒯 B := by
  simp [closure_eq]
  apply compl_inj_iff.mp
  simp
  apply interior_inter_eq h𝒯

-- in the discrete topology, the closure of any set is itself
theorem discrete_closure (A: Set X): closure Set.univ A = A := by
  simp [closure_eq, discrete_interior]

-- the frontier, aka boundary
def frontier_point (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  ∀ N ∈ Nbhds 𝒯 x, Set.Nonempty (N ∩ A) ∧ Set.Nonempty (N ∩ Aᶜ)

def frontier (𝒯: Set (Set X)) (A: Set X): Set X :=
  {x | frontier_point 𝒯 A x}

theorem frontier_eq (𝒯: Set (Set X)) (A: Set X): frontier 𝒯 A = closure 𝒯 A ∩ closure 𝒯 Aᶜ := by
  simp [frontier, frontier_point, closure, adherent]
  ext
  exact forall₂_and

-- the frontier of the closure is the same as the frontier
theorem frontier_closure_eq (𝒯: Set (Set X)) (A: Set X): frontier 𝒯 (closure 𝒯 A) = frontier 𝒯 A := by
  calc
    frontier 𝒯 (closure 𝒯 A) = closure 𝒯 (closure 𝒯 A) ∩ closure 𝒯 (closure 𝒯 A)ᶜ := by rw [frontier_eq]
                           _ = closure 𝒯 A ∩ closure 𝒯 (closure 𝒯 A)ᶜ := by rw [closure_idempotent]
                           _ = closure 𝒯 A ∩ closure 𝒯 (interior 𝒯 Aᶜ) := by rw [compl_closure_eq_interior_compl]
                           _ = closure 𝒯 A ∩ closure 𝒯 Aᶜ := sorry
                           _ = frontier 𝒯 A := by rw [frontier_eq]

theorem frontier_closed (𝒯: Set (Set X)) (A: Set X): closedset 𝒯 (frontier 𝒯 A) := by
  sorry

-- TODO: is basic neighborhood worth defining?
theorem frontier_mem_iff {𝒯 ℬ: Set (Set X)} (h: base 𝒯 ℬ) (A: Set X) (x: X): x ∈ frontier 𝒯 A ↔ ∀ N ∈ Nbhds 𝒯 x ∩ ℬ, N ∩ A = ∅ ∧ N ∩ Aᶜ = ∅ := by
  sorry

theorem frontier_univ {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): frontier 𝒯 Set.univ = ∅ := by
  simp [frontier_eq, closure_empty h𝒯]

theorem frontier_empty {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): frontier 𝒯 ∅ = ∅ := by
  simp [frontier_eq, closure_empty h𝒯]

-- in the discrete topology, the frontier of every set is empty
theorem discrete_frontier (A: Set X): frontier Set.univ A = ∅ := by
  simp [frontier_eq, discrete_closure]

def exterior_point (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  x ∈ interior 𝒯 Aᶜ

def exterior (𝒯: Set (Set X)) (A: Set X): Set X :=
  {x | exterior_point 𝒯 A x}

theorem exterior_eq (𝒯: Set (Set X)) (A: Set X): exterior 𝒯 A = (closure 𝒯 A)ᶜ := by
  simp [exterior, exterior_point, compl_closure_eq_interior_compl]

-- TODO this is clunky
-- the interior, frontier, and exterior form a disjoint union of the whole space.
theorem interior_frontier_exterior_partition (𝒯: Set (Set X)) (A: Set X):
  (interior 𝒯 A ∪ frontier 𝒯 A ∪ exterior 𝒯 A = X) ∧ (interior 𝒯 A ∩ frontier 𝒯 A = ∅) ∧ (interior 𝒯 A ∩ exterior 𝒯 A = ∅) ∧ (frontier 𝒯 A ∩ exterior 𝒯 A = ∅) := by
  repeat' constructor
  · sorry
  · sorry
  · sorry
  · sorry

-- in the discrete topology, the exterior of a set is its complement
theorem discrete_exterior (A: Set X): exterior Set.univ A = Aᶜ := by
  simp [exterior_eq, closure_eq, discrete_interior]

theorem closure_eq_interior_union_frontier (𝒯: Set (Set X)) (A: Set X): closure 𝒯 A = interior 𝒯 A ∪ frontier 𝒯 A := by
  sorry

theorem interior_eq_set_minus_frontier (𝒯: Set (Set X)) (A: Set X): interior 𝒯 A = A \ frontier 𝒯 A := by
  sorry





def dense (𝒯: Set (Set X)) (A: Set X): Prop :=
  ∀ U ∈ 𝒯, Set.Nonempty U → Set.Nonempty (A ∩ U)

theorem dense_univ (𝒯: Set (Set X)): dense 𝒯 Set.univ := by
  simp [dense]

theorem dense_iff_dense_in_base (𝒯 ℬ: Set (Set X)) (h: base 𝒯 ℬ) (A: Set X): dense 𝒯 A ↔ ∀ U ∈ ℬ, Set.Nonempty U → Set.Nonempty (A ∩ U) := by
  sorry

-- some theorems ? Q is dense, I is dense, is C is countable then Cᶜ is dense

theorem discrete_dense_iff (A: Set X): dense Set.univ A ↔ A = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_univ_subset
    intro x _
    simp [dense] at h
    exact Set.inter_singleton_nonempty.mp (h {x} (by exists x))
  · intro h
    rw [h]
    apply dense_univ

theorem indiscrete_dense (A: Set X): Set.Nonempty A → dense {∅, Set.univ} A := by
  intro h
  simp [dense]
  intro--
  exact h

-- theorem : dense in euclidean topology iff. dense in sorgenfry
theorem dense_iff (𝒯: Set (Set X)) (A: Set X): dense 𝒯 A ↔ closure 𝒯 A = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_univ_subset
    intro x _
    simp_all [closure, adherent, dense]
    intro N hN
    simp_all [Nbhds, neighborhood]
    obtain ⟨U, hU1, hU2, hU3⟩ := hN
    have := h U hU1 (by exists x)
    rw [Set.inter_comm]
    exact Set.Nonempty.mono (Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) hU3) this
  · intro h
    simp [dense]
    intro U hU1 hU2
    simp_all [closure, adherent]
    obtain ⟨x, hx⟩ := hU2
    have: x ∈ Set.univ := by exact trivial
    rw [←h] at this
    simp at this
    have: ∀ N ∈ Nbhds 𝒯 x, (N ∩ A).Nonempty := this
    have: U ∈ Nbhds 𝒯 x := by
      simp [Nbhds]
      exact open_neighborhood 𝒯 hx hU1
    rw [Set.inter_comm]
    (expose_names; exact this_1 U this)

theorem dense_antimono {𝒯₁ 𝒯₂: Set (Set X)} (h1: 𝒯₁ ⊆ 𝒯₂) {A: Set X} (h2: dense 𝒯₂ A): dense 𝒯₁ A := by
  intro U hU1
  exact h2 U (h1 hU1)

-- example: Z is dense in the topology generated by [a,infty)



-- continuity
def continuous_at (TX: Set (Set X)) (TY: Set (Set Y)) (f: X → Y) (x: X): Prop :=
  ∀ N' ∈ Nbhds TY (f x), ∃ N ∈ Nbhds TX x, f '' N ⊆ N'

def continuous (TX: Set (Set X)) (TY: Set (Set Y)) (f: X → Y): Prop :=
  ∀ x, continuous_at TX TY f x

theorem continuous_iff_open_preimage_open (TX: Set (Set X)) (TY: Set (Set Y)) (f: X → Y)(hTX: IsTopology TX): continuous TX TY f ↔ ∀ V ∈ TY, Set.preimage f V ∈ TX := by
  constructor
  intro h V hV
  simp[continuous,continuous_at,Nbhds] at h
  rw [open_iff_neighborhood_of_all_points hTX (f ⁻¹' V)]
  intro x hx
  have hVn : neighborhood TY V (f x) := by exact open_neighborhood TY hx hV
  apply h at hVn
  obtain ⟨ N,hN⟩ := hVn
  rw[neighborhood]
  rw[neighborhood] at hN
  obtain ⟨ O,hO⟩ := hN.left
  use O
  constructor
  exact hO.left
  constructor
  exact hO.right.left
  intro x hx
  apply hO.right.right at hx
  apply hN.right
  exact hx
  intro h
  simp[continuous,continuous_at]
  intro x N hN
  simp[Nbhds,neighborhood] at hN
  obtain ⟨ U,hU⟩ := hN
  have hU1: f ⁻¹' U ∈ TX:= by
     apply h
     exact hU.left
  use f ⁻¹' U
  constructor
  apply open_neighborhood
  refine Set.mem_preimage.mpr ?_
  exact hU.right.left
  exact hU1
  refine Set.preimage_mono ?_
  exact hU.right.right




def continuous_iff_closed_preimage_closed (TX: Set (Set X)) (TY: Set (Set Y)) (f: X → Y): continuous TX TY f ↔ ∀ F ∈ closedsets TY, Set.preimage f F ∈ closedsets TX := by
  sorry

def continuous_iff_image_closure_subseteq_closure_image (TX: Set (Set X)) (TY: Set (Set Y)) (f: X → Y): continuous TX TY f ↔ ∀ A: Set X, Set.image f (closure TX A) ⊆ closure TY (Set.image f A) := by
  sorry





noncomputable def Function.Inverse {f: X → Y} (h: Function.Bijective f): Y → X :=
  Classical.choose (Function.bijective_iff_has_inverse.mp h)

-- homeomorphisms
structure homeomorphism (TX: Set (Set X)) (TY: Set (Set Y)) (f: X → Y): Prop where
  bijection: Function.Bijective f
  continuous_forward: continuous TX TY f
  continuous_inverse: continuous TY TX (Function.Inverse bijection)

def homeomorphic (TX: Set (Set X)) (TY: Set (Set Y)): Prop :=
  ∃ f, homeomorphism TX TY f

-- this definition doesn't care about underlying type of points
def homeomorphic_spaces (X Y: TopologicalSpace): Prop :=
  ∃ f: X.points → Y.points, homeomorphism X.topology.opensets Y.topology.opensets f

-- a property is called a topological property if it's preserved under homeomorphism
def topological_property (P: TopologicalSpace → Prop): Prop :=
  ∀ X Y: TopologicalSpace, homeomorphic_spaces X Y → P X → P Y

def connected (T: Set (Set X)): Prop :=
  ∀ U V: Set X, U ∈ T → V ∈ T → U.Nonempty → V.Nonempty → U ∪ V = Set.univ → (U ∩ V).Nonempty

def connected_space (X: TopologicalSpace): Prop :=
  connected X.topology.opensets

-- connectedness is a topological property
theorem connected_topological_property: topological_property connected_space := by
  intro X Y h hX U V hU1 hV1 hU2 hV2 hUV
  sorry



-- Binary product topology

def product_topology (TX: Set (Set X)) (TY: Set (Set Y)): Set (Set (X × Y)) :=
  sorry

theorem product_topology_is_topology {TX: Set (Set X)} {TY: Set (Set Y)} (hTX: IsTopology TX) (hTY: IsTopology TY):
  IsTopology (product_topology TX TY) :=
  sorry

-- Product of open sets is open

theorem product_topology_product_open {TX: Set (Set X)} {TY: Set (Set Y)} (hTX: IsTopology TX) (hTY: IsTopology TY)
  {U: Set X} (hU: U ∈ TX) {V: Set Y} (hV: V ∈ TY):
  {(x, y): X × Y | x ∈ U ∧ y ∈ V} ∈ product_topology TX TY :=
  sorry

-- Projections are open

theorem product_topology_left_projection_open {TX: Set (Set X)} {TY: Set (Set Y)} (hTX: IsTopology TX) (hTY: IsTopology TY)
  {U: Set (X × Y)} (hU: U ∈ product_topology TX TY):
  (fun x => x.1) '' U ∈ TX :=
  sorry

theorem product_topology_right_projection_open {TX: Set (Set X)} {TY: Set (Set Y)} (hTX: IsTopology TX) (hTY: IsTopology TY)
  {U: Set (X × Y)} (hU: U ∈ product_topology TX TY):
  (fun x => x.2) '' U ∈ TY :=
  sorry
