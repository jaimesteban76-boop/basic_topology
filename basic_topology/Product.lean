import basic_topology.Operations

variable {X Y: Type*}

-- Binary product topology
def product_topology_basis (TX: Set (Set X)) (TY: Set (Set Y)): Set (Set (X × Y)) :=
  {UV | ∃ U V, U ∈ TX ∧ V ∈ TY ∧ UV = Set.prod U V}

def product_topology (TX: Set (Set X)) (TY: Set (Set Y)): Set (Set (X × Y)) :=
  unions (product_topology_basis TX TY)

theorem product_topology_is_topology {TX: Set (Set X)} {TY: Set (Set Y)} (hTX: IsTopology TX) (hTY: IsTopology TY): IsTopology (product_topology TX TY) := by
  apply is_base_iff_unions_topology.mp
  apply is_base_iff_base_conditions.mpr
  constructor
  · ext
    constructor
    · intro; trivial
    · intro
      exists ⊤
      constructor
      · exists ⊤, ⊤
        repeat' constructor
        · exact univ_open hTX
        · exact univ_open hTY
        · simp [Set.prod]
      ·   assumption
  · intro _ hB₁ _ hB₂ _ _
    obtain ⟨U₁, V₁, hUV₁₁, hUV₁₂, _⟩ := hB₁
    obtain ⟨U₂, V₂, hUV₂₁, hUV₂₂, _⟩ := hB₂
    exists Set.prod (U₁ ∩ U₂) (V₁ ∩ V₂)
    constructor
    · exists U₁ ∩ U₂, V₁ ∩ V₂
      constructor
      · exact binary_inter_open hTX hUV₁₁ hUV₂₁
      · constructor
        · exact binary_inter_open hTY hUV₁₂ hUV₂₂
        · exact rfl
    · constructor
      repeat constructor
      repeat simp_all [Set.prod]

-- Product of open sets is open

theorem product_topology_product_open {TX: Set (Set X)} {TY: Set (Set Y)}
  {U: Set X} (hU: U ∈ TX) {V: Set Y} (hV: V ∈ TY) :
  Set.prod U V ∈ product_topology TX TY := by
  apply unions_mem
  exists U, V

-- Projections are open

theorem product_topology_left_projection_open {TX: Set (Set X)} {TY: Set (Set Y)} (hTX: IsTopology TX) (hTY: IsTopology TY)
  {U: Set (X × Y)} (hU: U ∈ product_topology TX TY) :
  (fun x => x.1) '' U ∈ TX :=
  sorry

theorem product_topology_right_projection_open {TX: Set (Set X)} {TY: Set (Set Y)} (hTX: IsTopology TX) (hTY: IsTopology TY)
  {U: Set (X × Y)} (hU: U ∈ product_topology TX TY) :
  (fun x => x.2) '' U ∈ TY :=
  sorry

theorem boxes_base_product_topology {TX: Set (Set X)} {TY: Set (Set Y)}: base (product_topology TX TY) (product_topology_basis TX TY) := by
  rw [base_iff_unions]
  constructor
  · rw [product_topology]
    exact unions_sub (product_topology_basis TX TY)
  · rfl

theorem box_equal_prod_projections {A: Set X}{B: Set Y}: A.prod B = (Set.image Prod.fst (A.prod B)).prod (Set.image Prod.snd (A.prod B)) := by
  refine Set.Subset.antisymm_iff.mpr ?_
  constructor
  · intro (x,y) hxy
    have hx: x∈(Set.image Prod.fst (A.prod B)) := by
      refine (Set.mem_image Prod.fst (A.prod B) x).mpr ?_
      use (x,y)
    have hy: y∈ (Set.image Prod.snd (A.prod B)) := by
      refine (Set.mem_image Prod.snd (A.prod B) y).mpr ?_
      use (x,y)
    exact ⟨hx, hy⟩
  · intro (x,y) hxy
    rcases hxy with ⟨hx, hy⟩
    rcases hx with ⟨p, hp_mem, hpx⟩
    rcases hy with ⟨q, hq_mem, hqy⟩
    simp at hpx
    simp at hqy
    have hA: x ∈ A := by
      rw [← hpx]
      exact hp_mem.1
    have hB: y∈ B := by
      rw[← hqy]
      exact hq_mem.2
    exact ⟨ hA,hB⟩

theorem boxes_subset_everywhere {TX: Set (Set X)} {TY: Set (Set Y)} (U: Set (X×Y))(hTX: IsTopology TX)(hTY: IsTopology TY)(hU: U ∈ product_topology TX TY): ∀x∈ U , ∃ A∈ product_topology_basis TX TY , x∈A ∧ A⊆ U := by
  intro x hx
  rw[open_iff_eq_interior] at hU
  · rw [hU] at hx
    rw [interior_iff_basis_element boxes_base_product_topology] at hx
    exact hx
  · exact product_topology_is_topology hTX hTY
