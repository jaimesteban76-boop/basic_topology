import basic_topology.Topology
import basic_topology.Continuity
import basic_topology.Operations

set_option linter.style.multiGoal false

variable {X Y Z: Type*} {T₁: Family X} {T₂: Family Y} {T₃: Family Z}

def Open_map (T₁: Family X) (T₂: Family Y) (f: X → Y): Prop :=
  ∀V, Open T₁ V → Open T₂ (Set.image f V)

theorem Open_map_iff_basis(ℬ T₁: Family X) (T₂: Family Y)(hT₁: IsTopology T₁)(hT₂: IsTopology T₂) (f:X→ Y)(hB: base T₁ ℬ ): Open_map T₁ T₂ f ↔ ∀B∈ℬ, Open T₂ (Set.image f B)  := by
  constructor
  intro h B hb
  apply hB.1 at hb
  apply h at hb
  exact hb
  rw[Open_map]
  intro hb V hV
  rw[open_iff_eq_interior]
  ext y
  constructor
  intro hx
  rw[interior_iff_basis_element (base_self T₂)]
  simp at hx
  obtain ⟨x,⟨hxV, hf ⟩ ⟩ :=hx
  have : ∃B∈ ℬ , x∈ B ∧ B⊆ V := by
    rw[open_iff_eq_interior,] at hV
    rw[hV,interior_iff_basis_element hB] at hxV
    exact hxV
    exact hT₁
  obtain ⟨B,⟨_,_,_ ⟩  ⟩ := this
  use Set.image f B
  repeat' (apply And.intro)
  (expose_names; exact hb B left)
  simp
  use x
  (expose_names; exact Set.image_mono right)
  exact fun a ↦ neighborhood_mem a
  exact hT₂
