import basic_topology.Operations
import basic_topology.Continuity
import basic_topology.OpenMap


set_option linter.style.multiGoal false

variable {X Y: Type*}
--Helper Theorem--
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
-- Binary product topology
def product_topology_basis (TX: Family X) (TY: Family Y): Set (Set (X × Y)) :=
  {UV | ∃ U V, U ∈ TX ∧ V ∈ TY ∧ UV = Set.prod U V}

def product_topology (TX: Family X) (TY: Family Y): Family (X × Y) :=
  unions (product_topology_basis TX TY)

theorem product_topology_is_topology {TX: Family X} {TY: Family Y} (hTX: IsTopology TX) (hTY: IsTopology TY): IsTopology (product_topology TX TY) := by
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

theorem product_topology_product_open {TX: Family X} {TY: Family Y}
  {U: Set X} (hU: U ∈ TX) {V: Set Y} (hV: V ∈ TY) :
  Set.prod U V ∈ product_topology TX TY := by
  apply unions_mem
  exists U, V
--boxes product topology--
theorem boxes_base_product_topology {TX: Family X} {TY: Family Y}: base (product_topology TX TY) (product_topology_basis TX TY) := by
  rw [base_iff_unions]
  constructor
  · rw [product_topology]
    exact unions_sub (product_topology_basis TX TY)
  · rfl
theorem boxes_subset_everywhere {TX: Family X} {TY: Family Y} (U: Set (X×Y))(hTX: IsTopology TX)(hTY: IsTopology TY)(hU: Open (product_topology TX TY) U): ∀x∈ U , ∃ A∈ product_topology_basis TX TY , x∈A ∧ A⊆ U := by
  intro x hx
  rw[ open_iff_eq_interior] at hU
  · rw [hU] at hx
    rw [interior_iff_basis_element boxes_base_product_topology] at hx
    exact hx
  · exact product_topology_is_topology hTX hTY

-- Projections Definitions--
def proj₁ {X: Type u} {Y: Type v}: X × Y → X :=
  fun p => p.1
def proj₂ {X: Type u} {Y: Type v}: X × Y → Y :=
  fun p => p.2
--Projections are continous--
theorem continuous_pr₁ (TX: Family X) (TY: Family Y)(hTY: IsTopology TY) : Continuous (product_topology TX TY) (TX) (proj₁) := by
  unfold Continuous
  intro V hV
  have hpr: proj₁⁻¹'V= V.prod (@Set.univ Y) := by
    ext x
    simp
    rw[proj₁]
    constructor
    intro hx
    have hx2: x.2∈ @Set.univ Y:= by trivial
    exact ⟨ hx,hx2⟩
    intro hx
    exact hx.1
  rw[hpr]
  apply product_topology_product_open
  exact hV
  apply univ_open
  exact hTY


theorem continuous_pr₂ (TX: Family X) (TY: Family Y)(hTX: IsTopology TX) : Continuous (product_topology TX TY) (TY) (proj₂) := by
  unfold Continuous
  intro V hV
  have hpr: proj₂⁻¹'V= (@Set.univ X).prod V := by
    ext x
    simp
    rw[proj₂]
    constructor
    intro hx
    have : x.2∈ @Set.univ Y:= by trivial
    exact ⟨this , hx ⟩
    intro hx
    exact hx.2
  rw[hpr]
  apply product_topology_product_open
  apply univ_open
  exact hTX
  exact hV


--Projections are open maps--
theorem product_topology_left_projection_open {TX: Family X} {TY: Family Y} (hTX: IsTopology TX) (hTY: IsTopology TY): Open_map (product_topology TX TY) TX (proj₁)  := by
  rw [Open_map_iff_basis (product_topology_basis TX TY)]
  intro V hV
  simp [product_topology_basis] at hV
  obtain ⟨A,⟨hA,B,hB,hAB ⟩  ⟩:= hV
  rcases Set.eq_empty_or_nonempty B with h1 | h2
  have : V=∅ := by
    rw[hAB]
    by_contra h
    push_neg at h
    obtain ⟨x,hx ⟩:= h
    have : B.Nonempty := by
      refine Set.nonempty_def.mpr ?_
      use x.2
      exact hx.2
    rw [Set.nonempty_iff_ne_empty] at this
    exact this h1
  rw[this]
  simp
  exact empty_open hTX
  have : Set.image proj₁ V=A := by
    ext x
    simp
    constructor
    intro h
    obtain ⟨a,⟨ b,hab,hproj⟩  ⟩ := h
    simp [← hproj]
    rw[hAB] at hab
    exact hab.1
    intro hx
    obtain ⟨b,hb ⟩:= h2
    use x, b
    simp[proj₁]
    rw[hAB]
    exact ⟨hx,hb ⟩
  rw[this]
  exact hA
  exact product_topology_is_topology hTX hTY
  exact hTX
  exact boxes_base_product_topology

theorem product_topology_right_projection_open {TX: Family X} {TY: Family Y} (hTX: IsTopology TX) (hTY: IsTopology TY): Open_map (product_topology TX TY) TY (proj₂)  := by
  rw [Open_map_iff_basis (product_topology_basis TX TY)]
  intro V hV
  simp [product_topology_basis] at hV
  obtain ⟨A,⟨hA,B,hB,hAB ⟩  ⟩:= hV
  rcases Set.eq_empty_or_nonempty A with h1 | h2
  have : V=∅ := by
    rw[hAB]
    by_contra h
    push_neg at h
    obtain ⟨x,hx ⟩:= h
    have : A.Nonempty := by
      refine Set.nonempty_def.mpr ?_
      use x.1
      exact hx.1
    rw [Set.nonempty_iff_ne_empty] at this
    exact this h1
  rw[this]
  simp
  exact empty_open hTY
  have : Set.image proj₂ V=B := by
    ext x
    simp
    constructor
    intro h
    obtain ⟨a,⟨ b,hab,hproj⟩  ⟩ := h
    simp [← hproj]
    rw[hAB] at hab
    exact hab.2
    intro hx
    obtain ⟨b,hb ⟩:= h2
    use b, x
    simp[proj₂]
    rw[hAB]
    exact ⟨hb, hx ⟩
  rw[this]
  exact hB
  exact product_topology_is_topology hTX hTY
  exact hTY
  exact boxes_base_product_topology
