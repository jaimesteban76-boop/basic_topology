import basic_topology.Subspace
import basic_topology.Sequence

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

theorem compact_closed_subset (hT: hausdorff T) {K: Set X} (hK: compactset T K): Closed T K := by
  sorry

def Family.image (f: X → Y) (F: Family X): Family Y :=
  {f '' U | U ∈ F}

def Family.preimage (f: X → Y) (F: Family Y): Family X :=
  {f ⁻¹' V | V ∈ F}

theorem continuous_image_compact (hT₁: compact T₁) (f: X → Y)
  (hf₁: Continuous T₁ T₂ f) (hf₂: Function.Surjective f): compact T₂ := by
  intro 𝒱 h𝒱₁ h𝒱₂
  let 𝒰 := Family.preimage f 𝒱
  have: ⋃₀ 𝒰 = ⊤ := by sorry
  have := hT₁ 𝒰 sorry this
  obtain ⟨C₀, hC₀⟩ := this
  exists Family.image f C₀
  constructor
  sorry
  constructor
  sorry
  sorry
