/-

Defines continuity in a topological space and in a metric space.

-/

import basic_topology.Relation
import basic_topology.Operations

set_option linter.style.multiGoal false

variable {X Y Z: Type*} {T₁: Family X} {T₂: Family Y} {T₃: Family Z}

def Continuous (T₁: Family X) (T₂: Family Y) (f: X → Y): Prop :=
  ∀ V, Open T₂ V → Open T₁ (f ⁻¹' V)

theorem Continuous.id (T: Family X): Continuous T T (fun x => x) := by
  exact fun _ h => h

theorem Continuous.comp {f: X → Y} {g: Y → Z} (hf: Continuous T₁ T₂ f) (hg: Continuous T₂ T₃ g): Continuous T₁ T₃ (g ∘ f) := by
  intro _ hW
  rw [Set.preimage_comp]
  apply hf
  exact hg _ hW

theorem Continuous.const (hT₁: IsTopology T₁) (y₀: Y): Continuous T₁ T₂ (fun _ => y₀) := by
  intro V _
  by_cases hy₀: y₀ ∈ V <;> simp_all
  exact univ_open hT₁
  exact empty_open hT₁

def ContinuousAt (T₁: Family X) (T₂: Family Y) (f: X → Y) (x: X): Prop :=
  ∀ N₂ ∈ Nbhds T₂ (f x), ∃ N₁ ∈ Nbhds T₁ x, f '' N₁ ⊆ N₂

theorem continuous_iff_continuous_at_all_points (T₁: Family X) (T₂: Family Y) (f: X → Y):
  Continuous T₁ T₂ f ↔ ∀ x, ContinuousAt T₁ T₂ f x := by
  constructor
  intro h x N ⟨U, hU₁, hU₂, hU₃⟩
  exists f ⁻¹' U
  constructor
  exists f ⁻¹' U
  repeat' constructor
  exact h U hU₁
  exact hU₂
  exact fun ⦃a⦄ a ↦ a
  sorry
  intro h V hV
  sorry

def continuous_at (T₁: Family X) (T₂: Family Y) (f: X → Y) (x: X): Prop :=
  ∀ N₂ ∈ Nbhds T₂ (f x), ∃ N₁ ∈ Nbhds T₁ x, f '' N₁ ⊆ N₂

def continuous (T₁: Family X) (T₂: Family Y) (f: X → Y): Prop :=
  ∀ x, continuous_at T₁ T₂ f x


theorem continuous.id (T: Family X): continuous T T (fun x => x) := by
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


-- Homeomorphisms
structure Homeomorphism (T₁: Family X) (T₂: Family Y) where
  map: X → Y
  inv: Y → X
  map_continuous: continuous T₁ T₂ map
  inv_continuous: continuous T₂ T₁ inv
  id_left: inv ∘ map = id
  id_right: map ∘ inv = id

def Homeomorphism.id (T: Family X): Homeomorphism  T T := {
  map := fun x => x
  inv := fun x => x
  map_continuous := continuous.id T
  inv_continuous := continuous.id T
  id_left := rfl
  id_right := rfl
}

def Homeomorphism.inverse (f: Homeomorphism T₁ T₂): Homeomorphism T₂ T₁ := {
  map := f.inv
  inv := f.map
  map_continuous := f.inv_continuous
  inv_continuous := f.map_continuous
  id_left := f.id_right
  id_right := f.id_left
}

def Homeomorphism.comp (f: Homeomorphism T₁ T₂) (g: Homeomorphism T₂ T₃): Homeomorphism T₁ T₃ :=
  sorry

def Homeomorphic (T₁: Family X) (T₂: Family Y): Prop :=
  Nonempty (Homeomorphism T₁ T₂)

def Homeomorphic.relation: Endorelation TopologicalSpace :=
  fun X Y => Homeomorphic X.topology.Open Y.topology.Open

theorem Homeomorphic.reflexive: reflexive Homeomorphic.relation := by
  intro X
  exact Nonempty.intro (Homeomorphism.id _)

theorem Homeomorphic.symm: symmetric Homeomorphic.relation := by
  intro X Y h
  exact Nonempty.intro (Homeomorphism.inverse (Classical.choice h))

theorem Homeomorphic.trans: transitive Homeomorphic.relation := by
  intro X Y Z h1 h2
  let f := Classical.choice h1
  let g := Classical.choice h2
  exact Nonempty.intro (Homeomorphism.comp f g)


-- a property is called a topological property if it's preserved under homeomorphism
def topological_property (P: TopologicalSpace → Prop): Prop :=
  ∀ X Y: TopologicalSpace, Homeomorphic.relation X Y → P X → P Y
