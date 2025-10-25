import basic_topology.Topology

variable {X: Type*}

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
theorem sierpiński_base: base (sierpiński_opensets) {{true}, {false, true}} := by
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
theorem unions_mem (ℬ: Set (Set X)) {U: Set X} (hU: U ∈ ℬ): U ∈ unions ℬ := by
  simp [unions]
  exists {U}
  constructor
  · exact Set.singleton_subset_iff.mpr hU
  · exact Eq.symm (Set.sUnion_singleton _)

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
theorem is_base_iff_unions_topology {ℬ: Set (Set X)}: is_base ℬ ↔ IsTopology (unions ℬ) := by
  apply Iff.intro
  · intro ⟨𝒯, h𝒯₁, h𝒯₂, h𝒯₃⟩
    have: 𝒯 = unions ℬ := by
      apply le_antisymm
      intro U hU
      obtain ⟨𝒰, h𝒰⟩ := h𝒯₃ U hU
      rw [h𝒰.2]
      simp [unions]
      exists 𝒰
      constructor
      exact h𝒰.1
      rfl
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
  B1: ⋃₀ ℬ = ⊤
  B2: ∀ B' ∈ ℬ, ∀ B'' ∈ ℬ, ∀ x ∈ B' ∩ B'', ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ B' ∩ B''

theorem is_base_iff_base_conditions {ℬ: Set (Set X)}: is_base ℬ ↔ base_conditions ℬ := by
  constructor
  · intro ⟨T, hT₁, hT₂⟩
    constructor
    · sorry
    · intro B'  hb' B'' hB'' x hx
      sorry
  · intro h
    sorry

-- TODO: suppose T is generated by B. Then U is open iff. forall x in U, exists B in B, x in B sub U.
