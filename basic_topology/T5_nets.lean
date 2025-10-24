import basic_topology.T0_topology

set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.dupNamespace false
set_option linter.style.multiGoal false

universe u v

variable {X Y : Type*}

/-- A relation between `X` and `Y` is a binary predicate `X → Y → Prop`. -/
def Relation (X : Type u) (Y : Type v) : Type (max u v) :=
  X → Y → Prop

/-- An endorelation is a relation on a single set. -/
def Endorelation (X : Type u) : Type u :=
  Relation X X

/-- A preorder is a reflexive and transitive relation. -/
structure preorder {X : Type u} (R : Relation X X) : Prop where
  reflexive : ∀ x, R x x
  transitive : ∀ x y z, (R x y ∧ R y z) → R x z

/-- A directed set is a preorder where any two elements have an upper bound. -/
structure directed_set {X : Type u} (R : Relation X X) : Prop extends preorder R where
  upperbound : ∀ x y, ∃ z, R x z ∧ R y z


def net_converges {X : Type u} {D : Type v} (T: Set (Set X)) (R: Relation D D) (a: D -> X) (x: X) : Prop :=
  ∀ U ∈ Nbhds T x, ∃ i₀, ∀ j, R i₀ j → a j ∈ U

def neighborhood_direction (T: Set (Set X)) (x: X): Endorelation (Nbhds T x) :=
  fun N1 N2 => N2.1 ⊆ N1.1

theorem neighborhood_direction_directed_set (T: Set (Set X)) (x: X) (hT: IsTopology T) : (directed_set (neighborhood_direction T x)) := by
  repeat constructor
  intro Nx
  exact fun ⦃a⦄ a ↦ a
  simp [neighborhood_direction]
  intro N1 hN1 N2 hN2 N3 hN3
  exact fun a a_1 ⦃a_2⦄ a_3 ↦ a (a_1 a_3)
  intro ⟨N1,hN1⟩ ⟨N2,hN2⟩
  simp [neighborhood_direction]
  use N1∩N2
  repeat constructor
  exact Set.inter_subset_left
  constructor
  exact neighborhood_binary_inter x N1 hT N2 hN1 hN2
  exact Set.inter_subset_right

theorem continuous_at_iff_all_nets_converge {X: Type u} {TX: Set ( Set X)} {TY: Set (Set Y )} (hTX: IsTopology TX ) (f:X→ Y) (x0:X):
  continuous_at TX TY f x0 ↔ ∀D : Type u , ∀ R: Endorelation D , directed_set R → ∀ x: D → X , net_converges TX R x x0 → net_converges TY R (f∘ x) (f x0):= by
    constructor
    simp[net_converges]
    intro h_con D  R  d  hR hnx
    rw[continuous_at] at h_con
    intro U hU
    apply h_con at hU
    obtain ⟨ N, ⟨ hN1,hN2⟩ ⟩ := hU
    apply hnx at hN1
    obtain ⟨ i,hi⟩ := hN1
    use i
    intro j hrij
    apply hN2
    exact Set.mem_image_of_mem f (hi j hrij)
    contrapose
    rw[continuous_at]
    push_neg
    intro h_con
    obtain ⟨ N,⟨ h1,h2⟩ ⟩ := h_con
    simp[Set.not_subset] at h2
    let D:= { N : Set X // N ∈ Nbhds TX x0 }
    let R: Endorelation D := fun N1 N2 => N2.1 ⊆ N1.1
    use D, R
    constructor
    apply neighborhood_direction_directed_set
    exact hTX
    let x (d : D) : X := Classical.choose (h2 d.1 d.2)
    have x_prop (d : D) : x d ∈ d.1 ∧ f (x d) ∉ N := Classical.choose_spec (h2 d.1 d.2)
    use x
    rw[net_converges]
    constructor
    intro U hU
    use ⟨U, hU⟩
    intro j hrij
    exact hrij (x_prop j).1
    rw[net_converges]
    push_neg
    use N
    constructor
    exact h1
    intro i
    use i
    exact And.imp_left (fun a ⦃a⦄ a ↦ a) (x_prop i)
