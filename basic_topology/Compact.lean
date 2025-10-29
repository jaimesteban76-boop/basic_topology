import basic_topology.Subspace
import basic_topology.Sequence

set_option linter.style.multiGoal false

variable {X: Type*} {T: Family X}

-- define compact space and sset
def compact (T: Family X): Prop :=
  ∀ C ⊆ T, ⋃₀ C = ⊤ → ∃ C₀, C₀ ⊆ C ∧ Finite C₀ ∧ ⋃₀ C₀ = ⊤

def compactset (T: Family X) (A: Set X): Prop :=
  ∀ C ⊆ T, A ⊆ ⋃₀ C → ∃ C₀, C₀ ⊆ C ∧ Finite C₀ ∧ A ⊆ ⋃₀ C₀

theorem compactset_iff_compact_subspace (T: Family X) (A: Set X) :
  compactset T A ↔ compact (subspace T A) := by
  constructor
  · intro h C h1 h2
    obtain ⟨C₀, h3, h4, h5⟩ := h (supspace C) sorry sorry
    exists subspace C₀ A
    repeat' (apply And.intro)
    · sorry
    · sorry
    · sorry
  · intro h C h1 h2
    obtain ⟨C₀, h3, h4, h5⟩ := h (subspace_down A '' C) sorry sorry
    exists supspace C₀
    repeat' (apply And.intro)
    · sorry
    · sorry
    · sorry

theorem compact_closed_subset (hT1:IsTopology T)(hT2: hausdorff T) {K: Set X} (hK: compactset T K): Closed T K := by
  rw[compactset] at hK
  rw[Closed, open_iff_eq_interior,]
  ext x
  rw[interior_iff_basis_element (base_self T)]
  constructor
  intro hx
  rw[hausdorff_iff_open_separable,] at hT2
  simp[OpenSeparable] at hT2
  rw [Set.mem_compl_iff] at hx
  have h_ne : ∀ y ∈ K, x ≠ y := by
    intro y hyK h_eq
    rw [h_eq] at hx
    exact hx hyK
  have hy1 : ∀y∈ K,  ∃ U V, Open T U ∧ Open T V ∧ Disjoint U V ∧ {x} ⊆ U ∧ {y} ⊆ V:= by
    intro y hy
    apply h_ne at hy
    apply hT2 at hy
    obtain ⟨A,⟨hA,B,hB,hAB,hxA,hyB ⟩  ⟩:= hy
    use A, B
    repeat' (apply And.intro)
    exact hA
    exact hB
    exact hAB
    exact Set.singleton_subset_iff.mpr hxA
    exact Set.singleton_subset_iff.mpr hyB
  choose! U V hU_open hV_open h_disjoint hx_in_U hy_in_V using hy1
  let C := { s | ∃ y ∈ K, s = V y }
  have hC_open: C⊆ T:= by
    intro c hc
    have : ∃y∈ K , c= V y := by exact hc
    obtain ⟨ m,⟨hm1,hm2 ⟩ ⟩ := this
    rw[hm2]
    exact hV_open m hm1
  have hC_cover: K ⊆ ⋃₀ C:= by
    intro y hyK
    simp
    use V y
    constructor
    refine Set.mem_setOf.mpr ?_
    use y
    exact hy_in_V y hyK rfl
  apply hK at hC_open
  apply hC_open at hC_cover
  obtain ⟨C₀,⟨ hC₀1,hC₀2,hC₀3⟩ ⟩:= hC_cover
  have hvc: ∀C∈ C₀, ∃ V∈ T, x∈ V ∧ Disjoint C V := by
    intro c hc
    have : ∃y∈ K , c= V y := by
      apply hC₀1 at hc
      exact hc
    obtain ⟨ m,⟨hm1,hm2 ⟩ ⟩ := this
    use U m
    repeat' (apply And.intro)
    exact hU_open m hm1
    exact hx_in_U m hm1 rfl
    rw[hm2]
    exact Disjoint.symm (Set.disjoint_of_subset_left (fun ⦃a⦄ a ↦ a) (h_disjoint m hm1))
  choose! M hV1 hV2 hV3 using hvc
  let B:= {s| ∃C∈ C₀ , s= M C}
  use ⋂₀ B
  repeat' (apply And.intro)
  apply hT1.2
  intro b hB
  have : ∃ C∈ C₀ , b=M C:= by exact hB
  obtain ⟨c,hc ⟩:= this
  rw[hc.2]
  apply hV1
  exact hc.1
  have hB_eq_image : B = M '' C₀ := by
    unfold B
    ext s
    simp only [Set.mem_image, Set.mem_setOf_eq]
    simp_all only [ne_eq, Set.singleton_subset_iff, C]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      subst right
      apply Exists.intro
      · apply And.intro
        on_goal 2 => { rfl
        }
        · simp_all only
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      subst right
      apply Exists.intro
      · apply And.intro
        on_goal 2 => { rfl
        }
        · simp_all only
  rw [hB_eq_image]
  exact Set.Finite.image M hC₀2
  simp
  intro b hb
  have : ∃ C∈ C₀ , b=M C:= by exact hb
  obtain ⟨c,hc ⟩:= this
  rw[hc.2]
  apply hV2
  exact hc.1
  refine Set.subset_compl_comm.mp ?_
  intro a ha
  apply hC₀3 at ha
  simp
  simp at ha
  obtain ⟨ t,⟨ ht1,ht2⟩ ⟩ := ha
  use M t
  constructor
  simp_all only [ne_eq, Set.singleton_subset_iff, Set.mem_setOf_eq, C, B]
  apply Exists.intro
  · apply And.intro
    on_goal 2 => { rfl
    }
    · simp_all only
  exact Disjoint.notMem_of_mem_left (hV3 t ht1) ht2
  intro hx
  obtain ⟨B,hB ⟩:= hx
  apply hB.2.2
  exact hB.2.1
  exact hT1
