/-

Defines continuity in a topological space and in a metric space.

-/

import basic_topology.Operations

set_option linter.style.multiGoal false

variable {X Y: Type*}

def continuous_at (TX: Family X) (TY: Set (Set Y)) (f: X → Y) (x: X): Prop :=
  ∀ N' ∈ Nbhds TY (f x), ∃ N ∈ Nbhds TX x, f '' N ⊆ N'

def continuous (TX: Family X) (TY: Set (Set Y)) (f: X → Y): Prop :=
  ∀ x, continuous_at TX TY f x

theorem continuous_iff_open_preimage_open (TX: Family X) (TY: Set (Set Y)) (f: X → Y)(hTX: IsTopology TX): continuous TX TY f ↔ ∀ V ∈ TY, Set.preimage f V ∈ TX := by
  constructor
  intro h V hV
  simp[continuous,continuous_at,Nbhds] at h
  rw [open_iff_neighborhood_of_all_points hTX (f ⁻¹' V)]
  intro x hx
  have hVn: neighborhood TY V (f x) := by exact open_neighborhood TY hx hV
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
  have hU1: f ⁻¹' U ∈ TX := by
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

def continuous_iff_closed_preimage_closed (TX: Family X) (TY: Set (Set Y)) (f: X → Y): continuous TX TY f ↔ ∀ F ∈ closedsets TY, Set.preimage f F ∈ closedsets TX := by
  sorry

def continuous_iff_image_closure_subseteq_closure_image (TX: Family X) (TY: Set (Set Y)) (f: X → Y): continuous TX TY f ↔ ∀ A: Set X, Set.image f (closure TX A) ⊆ closure TY (Set.image f A) := by
  sorry
