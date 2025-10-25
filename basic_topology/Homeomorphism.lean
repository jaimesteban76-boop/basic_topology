import basic_topology.Relation
import basic_topology.Continuity

variable {X Y: Type*}


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

def homeomorphic (T₁: Family X) (T₂: Family Y): Prop :=
  Nonempty (homeomorphism T₁ T₂)


def homeomorphic.relation: Endorelation TopologicalSpace :=
  fun X Y => homeomorphic X.topology.opensets Y.topology.opensets


-- a property is called a topological property if it's preserved under homeomorphism
def topological_property (P: TopologicalSpace → Prop): Prop :=
  ∀ X Y: TopologicalSpace, homeomorphic.relation X Y → P X → P Y
