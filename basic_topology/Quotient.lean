import basic_topology.Topology

set_option linter.style.commandStart false

variable {X Y: Type*} {T: Family X}

-- Show that the quotient by an equivalence relation is a topology.

example {X: Type u} (r: X → X → Prop) (hr: Equivalence r): Type u :=
  Quotient ⟨r, hr⟩

-- Lift a family to the quotient.
def quotient_family (T: Family X) (r: X → X → Prop) (hr: Equivalence r): Family (Quotient ⟨r, hr⟩) :=
  {A | A ∘ Quotient.mk ⟨r, hr⟩ ∈ T}

theorem quotient_is_topology (hT: IsTopology T) {r: X → X → Prop} (hr: Equivalence r): IsTopology T := {
  sUnion := by
    intro 𝒰 h𝒰
    sorry
  finite_sInter := by
    intro 𝒰 h𝒰₁ h𝒰₂
    sorry
}
