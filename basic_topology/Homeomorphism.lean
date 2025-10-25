import basic_topology.Relation
import basic_topology.Continuity

variable {X Y Z: Type*}


noncomputable def Function.Inverse {f: X → Y} (h: Function.Bijective f): Y → X :=
  Classical.choose (Function.bijective_iff_has_inverse.mp h)

-- homeomorphisms
structure homeomorphism (T₁: Family X) (T₂: Family Y) where
  map: X → Y
  inv: Y → X
  map_continuous: continuous T₁ T₂ map
  inv_continuous: continuous T₂ T₁ inv
  id_left: inv ∘ map = id
  id_right: map ∘ inv = id

def homeo.id (T: Family X): homeomorphism  T T := {
  map := Function.id
  inv := Function.id
  map_continuous := continuous.id T
  inv_continuous := continuous.id T
  id_left := rfl
  id_right := rfl
}

def homeo.inv {T₁: Family X} {T₂: Family Y} (f: homeomorphism T₁ T₂): homeomorphism T₂ T₁ := {
  map := f.inv
  inv := f.map
  map_continuous := f.inv_continuous
  inv_continuous := f.map_continuous
  id_left := f.id_right
  id_right := f.id_left
}

def homeo.comp {T₁: Family X} {T₂: Family Y} {T₃: Family Z} (f: homeomorphism T₁ T₂) (g: homeomorphism T₂ T₃): homeomorphism T₁ T₃ :=
  sorry

def homeomorphic (T₁: Family X) (T₂: Family Y): Prop :=
  Nonempty (homeomorphism T₁ T₂)


def homeomorphic.relation: Endorelation TopologicalSpace :=
  fun X Y => homeomorphic X.topology.Open Y.topology.Open

theorem homeomorphic.reflexive: reflexive homeomorphic.relation := by
  intro X
  exact Nonempty.intro (homeo.id _)

theorem homeomorphic.symm: symmetric homeomorphic.relation := by
  intro X Y h
  exact Nonempty.intro (homeo.inv (Classical.choice h))

theorem homeomorphic.trans: transitive homeomorphic.relation := by
  intro X Y Z h1 h2
  let f := Classical.choice h1
  let g := Classical.choice h2
  exact Nonempty.intro (homeo.comp f g)


-- a property is called a topological property if it's preserved under homeomorphism
def topological_property (P: TopologicalSpace → Prop): Prop :=
  ∀ X Y: TopologicalSpace, homeomorphic.relation X Y → P X → P Y
