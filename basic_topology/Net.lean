import basic_topology.Relation
import basic_topology.Neighborhood
import basic_topology.Continuity

set_option linter.style.multiGoal false

universe u v

variable {X: Type u} {Y: Type v} {Δ: Type u}


/-- A directed set is a preorder where any two elements have an upper bound. -/


def upperbounded (R: Relation X Y): Prop :=
  ∀ x₁ x₂, ∃ y, R x₁ y ∧ R x₂ y

structure directed (R: Endorelation X): Prop extends Preorder' R where
  upperbounded: upperbounded R

def net_converges {X: Type u} {Δ: Type v} (T: Family X) (R: Relation Δ Δ) (a: Δ → X) (x: X): Prop :=
  ∀ U ∈ Nbhds T x, ∃ i₀, ∀ j, R i₀ j → a j ∈ U

def neighborhood_direction (T: Family X) (x: X): Endorelation (Nbhds T x) :=
  fun N₁ N₂ => N₂.val ⊆ N₁.val

theorem neighborhood_direction_directed_set (T: Family X) (x: X) (hT: IsTopology T): directed (neighborhood_direction T x) := by
  repeat constructor
  · intro Nx
    exact fun ⦃a⦄ a ↦ a
  · intro N1 hN1 N2 hN2 N3 hN3
    exact fun a ↦ hN2 (N3 a)
  · intro ⟨N1,hN1⟩ ⟨N2,hN2⟩
    simp [neighborhood_direction]
    use N1∩N2
    repeat constructor
    · exact Set.inter_subset_left
    · constructor
      · simp_all [Nbhds]
        exact neighborhood_binary_inter hT hN1 hN2
      · exact Set.inter_subset_right

theorem continuous_at_iff_all_nets_converge {X: Type u} {T: Family X} {T': Family Y} (hT: IsTopology T) (f: X → Y) (x₀: X) :
  continuous_at T T' f x₀ ↔ ∀ Δ: Type u, ∀ R, directed R → ∀ x: Δ → X , net_converges T R x x₀ → net_converges T' R (f ∘ x) (f x₀) := by
    constructor
    simp[net_converges]
    intro h_con Δ  R  d  hR hnx
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
    let Δ := { N: Set X // N ∈ Nbhds T x₀}
    let R: Endorelation Δ := fun N1 N2 => N2.1 ⊆ N1.1
    use Δ, R
    constructor
    apply neighborhood_direction_directed_set
    exact hT
    let x (d: Δ): X := Classical.choose (h2 d.1 d.2)
    have x_prop (d: Δ): x d ∈ d.1 ∧ f (x d) ∉ N := Classical.choose_spec (h2 d.1 d.2)
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

-- The predicate `adherent T R x a` says a is an adherent value of the net x
-- with respect to the topology T and the ordering R.

def upperset (R: Endorelation Δ) (δ₀: Δ): Set Δ :=
  {δ | R δ₀ δ}

def Net.upper_subnet (R: Endorelation Δ) (x: Δ → X) (δ₀: Δ): upperset R δ₀ → X :=
  x ∘ Subtype.val

def Net.tail (R: Endorelation Δ) (x: Δ → X) (δ₀: Δ): Set X :=
  Set.range (Net.upper_subnet R x δ₀)

def Net.adherent (T: Family X) (R: Endorelation Δ) (x: Δ → X) (a: X): Prop :=
  ∀ N ∈ Nbhds T a, ∀ δ₀, ∃ δ, R δ₀ δ ∧ x δ ∈ N

-- def Net.adherent' (T: Family X) (R: Endorelation Δ) (x: Δ → X) (a: X): Prop :=
--   ∀ N ∈ Nbhds T a, ∀ δ₀, (Set.range (Net.tail R x δ₀) ∩ N).Nonempty

theorem Net.adherent_iff (T: Family X) (R: Endorelation Δ) (x: Δ → X) (a: X): adherent T R x a ↔ a ∈ ⋂ δ, closure T (Net.tail R x δ) := by
  sorry

theorem Net.closure_mem_iff (T: Family X) (A: Set X) (x: X) :
  x ∈ closure T A ↔ ∃ Δ: Type u, ∃ R, directed R ∧ ∃ a: Δ → A, net_converges T R (Subtype.val ∘ a) x := by
  sorry

-- TODO: a is an adherent of image(x) iff. ∃ subnet y of x s.t. y → a.
