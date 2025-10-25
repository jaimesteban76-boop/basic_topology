/-

Defines continuity in a topological space and in a metric space.

-/

import basic_topology.Operations

set_option linter.style.multiGoal false

variable {X Y Z: Type*}

def Continuous (T₁: Family X) (T₂: Family Y) (f: X → Y): Prop :=
  ∀ V, Open T₂ V → Open T₁ (f ⁻¹' V)

def ContinuousAt (T₁: Family X) (T₂: Family Y) (f: X → Y) (x: X): Prop :=
  ∀ V, f x ∈ V → Open T₂ V → x ∈ f⁻¹' V ∧ Open T₁ (f ⁻¹' V)

theorem continuous_iff_continuous_all_points (T₁: Family X) (T₂: Family Y) (f: X → Y):
  Continuous T₁ T₂ f ↔ ∀ x, ContinuousAt T₁ T₂ f x := by
  constructor
  intro h x V hV₁ hV₂
  constructor
  exact hV₁
  exact h V hV₂
  intro h V hV
  sorry

def continuous_at (T₁: Family X) (T₂: Family Y) (f: X → Y) (x: X): Prop :=
  ∀ N₂ ∈ Nbhds T₂ (f x), ∃ N₁ ∈ Nbhds T₁ x, f '' N₁ ⊆ N₂

def continuous (T₁: Family X) (T₂: Family Y) (f: X → Y): Prop :=
  ∀ x, continuous_at T₁ T₂ f x

def Function.id {X: Type u}: X → X :=
  fun x => x

theorem continuous.id (T: Family X): continuous T T Function.id := by
  intro x N hN
  exists N
  constructor
  exact hN
  exact Set.image_subset_iff.mpr fun _ h ↦ h

theorem continuous.comp (T₁: Family X) (T₂: Family Y) (T₃: Family Z)
  (f: X → Y) (g: Y → Z)
  (h₁: continuous T₁ T₂ f) (h₂: continuous T₂ T₃ g):
  continuous T₁ T₃ (g ∘ f) := by
  intro x N₃ hN₃
  obtain ⟨N₂, hN₂⟩ := hN₃
  sorry

theorem Continuous.id (T: Family X): Continuous T T Function.id := by
  exact fun _ h => h

theorem Continuous.comp {T₁: Family X} {T₂: Family Y} {T₃: Family Z} {f: X → Y} {g: Y → Z} (hf: Continuous T₁ T₂ f) (hg: Continuous T₂ T₃ g):
  Continuous T₁ T₃ (g ∘ f) := by
  intro _ hW
  rw [Set.preimage_comp]
  apply hf
  exact hg _ hW

theorem continuous_iff_open_preimage_open (T₁: Family X) (T₂: Family Y) (f: X → Y) (hT₁: IsTopology T₁): continuous T₁ T₂ f ↔ ∀ V, Open T₂ V → Open T₁ (f ⁻¹' V) := by
  constructor
  intro h V hV
  simp[continuous,continuous_at,Nbhds] at h
  rw [open_iff_neighborhood_of_all_points hT₁ (f ⁻¹' V)]
  intro x hx
  have hVn: neighborhood T₂ V (f x) := by exact open_neighborhood hx hV
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
  have hU1: f ⁻¹' U ∈ T₁ := by
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

def continuous_iff_closed_preimage_closed (T₁: Family X) (T₂: Family Y) (f: X → Y): continuous T₁ T₂ f ↔ ∀ F, Closed T₂ F → Closed T₁ (f ⁻¹' F) := by
  sorry

def continuous_iff_image_closure_subseteq_closure_image (T₁: Family X) (T₂: Family Y) (f: X → Y): continuous T₁ T₂ f ↔ ∀ A, f '' (closure T₁ A) ⊆ closure T₂ (f '' A) := by
  sorry
