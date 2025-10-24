
import basic_topology.T0_topology
import basic_topology.T3_sequences

set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.dupNamespace false
set_option linter.style.multiGoal false

universe u v

variable {X Y : Type*}

-- define compact space and sset
def compact (T: Set (Set X)): Prop :=
  ∀ C ⊆ T, ⋃₀ C = ⊤ → ∃ C₀, C₀ ⊆ C ∧ Finite C₀ ∧ ⋃₀ C₀ = ⊤

def compactset (T: Set (Set X)) (A: Set X): Prop :=
  ∀ C ⊆ T, A ⊆ ⋃₀ C → ∃ C₀, C₀ ⊆ C ∧ Finite C₀ ∧ A ⊆ ⋃₀ C₀

theorem compactset_iff_compact_subspace (T: Set (Set X)) (A: Set X):
  compactset T A ↔ compact (subspace T A) := by
  constructor
  intro h C h1 h2
  obtain ⟨C₀, h3, h4, h5⟩ := h (supspace C) sorry sorry
  exists subspace C₀ A
  repeat' (apply And.intro)
  sorry
  sorry
  sorry
  intro h C h1 h2
  obtain ⟨C₀, h3, h4, h5⟩ := h (subspace_down A '' C) sorry sorry
  exists supspace C₀
  repeat' (apply And.intro)
  sorry
  sorry
  sorry

theorem compact_closed_subset {T: Set (Set X)} (hT: hausdorff T) {K: Set X} (hK: compactset T K): closedset T K := by
  sorry
