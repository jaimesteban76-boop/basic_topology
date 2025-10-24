import basic_topology.T0_topology
import basic_topology.T3_sequences

set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.dupNamespace false
set_option linter.style.multiGoal false

universe u v

variable {X Y D: Type*}


/-- A relation between `X` and `Y` is a binary predicate `X → Y → Prop`. -/
def Relation (X : Type u) (Y : Type v) : Type (max u v) :=
  X → Y → Prop

/-- An endorelation is a relation on a single set. -/
def Endorelation (X : Type u) : Type u :=
  Relation X X

/-- A preorder is a reflexive and transitive relation. -/
structure preorder (R : Endorelation X) : Prop where
  reflexive : ∀ x, R x x
  transitive : ∀ x y z, R x y → R y z → R x z

/-- A directed set is a preorder where any two elements have an upper bound. -/
structure directed (R : Relation X X) : Prop extends preorder R where
  upperbound : ∀ x y, ∃ z, R x z ∧ R y z

/-- A net `n` converges to `x` with respect to the topology `𝒯`
iff every open neighborhood of `x` eventually contains all later terms of the net. -/
def net_converges {X : Type u} (T: Set (Set X)) (R: Endorelation D)
  (n: D → X) (x : X) : Prop :=
  ∀ U : Set X, (U ∈ T) → (x ∈ U) →
    ∃ i₀, ∀ i, R i₀ i → n i ∈ U

/--
The neighborhood net of a point `x` is a net constructed from the directed set of
neighborhoods of `x`, where the direction is given by reverse subset inclusion.
For each neighborhood `V`, a point `a(V)` is chosen from `V` using the axiom of choice.
-/

def neighborhood_net (T: Set (Set X)) (x: X): Endorelation (Nbhds T x) :=
  fun ⟨U, _⟩ ⟨V, _⟩ => V ⊆ U

theorem neighborhood_net_directed (T: Set (Set X))
  (hT : IsTopology T) (x : X) :
  directed (neighborhood_net T x) := {
  reflexive := fun U => Set.Subset.refl U.1,
  transitive := by exact fun _ _ _ h1 h2 _ h3 ↦ h1 (h2 h3)
  upperbound := fun U V => by
    have h_inter_nhds : U.1 ∩ V.1 ∈ Nbhds T x := by
      obtain ⟨O_U, hO_U_open, hx_in_OU, hOU_sub_U⟩ := U.2
      obtain ⟨O_V, hO_V_open, hx_in_OV, hOV_sub_V⟩ := V.2
      use O_U ∩ O_V
      exact ⟨binary_inter_open hT hO_U_open hO_V_open, ⟨hx_in_OU, hx_in_OV⟩, Set.inter_subset_inter hOU_sub_U hOV_sub_V⟩
    use ⟨U.1 ∩ V.1, h_inter_nhds⟩
    exact ⟨Set.inter_subset_left, Set.inter_subset_right⟩
}

theorem neighborhood_net_converges {T: Set (Set X)}
  (hT : IsTopology T) (x : X) :
  net_converges TX (neighborhood_net TX hTX x) x := by
  rw [net_converges]
  intro U hU_open hx_in_U
  use ⟨U, open_neighborhood TX hx_in_U hU_open⟩
  rintro ⟨A, hA⟩ hA_sub_U
  have point_in_A := Classical.choose_spec (Set.nonempty_of_mem (neighborhood_mem hA))
  exact hA_sub_U point_in_A




theorem continuous_at_iff_f_net_converges
  {X Y : Type*} (TX: Set (Set X))(TY: Set (Set Y))
  (hTX : IsTopology TX) (hTY : IsTopology TY)
  (f : X → Y) (x0 : X) :
  continuous_at TX TY f x0 ↔
    ∀ n : net X, net_converges TX n x0 → f_net_converges TY f n (f x0):= by
    constructor
    intro h n hn
    rw[continuous_at] at h
    simp[f_net_converges,net_converges]
    intro U hU hf
    have h1 : U∈ Nbhds TY (f x0) := by
      simp [Nbhds]
      exact open_neighborhood TY hf hU
    apply h at h1
    obtain ⟨ N,hN⟩ := h1
    simp [f_net]
    simp[net_converges] at hn
    simp [Nbhds,neighborhood] at hN
    obtain ⟨ O,hO⟩ := hN.left
    let h3:= hO.left
    apply hn at h3
    have h4: x0∈ O:= by exact hO.right.left
    apply h3 at h4
    obtain ⟨ i,hi⟩ := h4
    use i
    intro j hj
    exact hN.2 (hO.2.2 (hi j hj))
    intro hn N hN
    sorry
