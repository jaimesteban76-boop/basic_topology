import basic_topology.T0_topology

set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.dupNamespace false
set_option linter.style.multiGoal false

universe u v

variable {X: Type u} {Y: Type v} {Δ: Type u}


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
structure directed_set {X : Type u} (R : Relation X X) : Prop extends preorder R where
  upperbound : ∀ x y, ∃ z, R x z ∧ R y z

def net_converges {X : Type u} {Δ : Type v} (T: Set (Set X)) (R: Relation Δ Δ) (a: Δ → X) (x: X) : Prop :=
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
  simp_all [Nbhds]
  exact neighborhood_binary_inter hT hN1 hN2
  exact Set.inter_subset_right

theorem continuous_at_iff_all_nets_converge {X: Type u} {TX: Set ( Set X)} {TY: Set (Set Y )} (hTX: IsTopology TX ) (f:X→ Y) (x0:X):
  continuous_at TX TY f x0 ↔ ∀Δ : Type u , ∀ R: Endorelation Δ , directed_set R → ∀ x: Δ → X , net_converges TX R x x0 → net_converges TY R (f∘ x) (f x0):= by
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
    let Δ:= { N : Set X // N ∈ Nbhds TX x0 }
    let R: Endorelation Δ := fun N1 N2 => N2.1 ⊆ N1.1
    use Δ, R
    constructor
    apply neighborhood_direction_directed_set
    exact hTX
    let x (d : Δ) : X := Classical.choose (h2 d.1 d.2)
    have x_prop (d : Δ) : x d ∈ d.1 ∧ f (x d) ∉ N := Classical.choose_spec (h2 d.1 d.2)
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

def Net.adherent (T: Set (Set X)) (R: Endorelation Δ) (x: Δ → X) (a: X): Prop :=
  ∀ N ∈ Nbhds T a, ∀ δ₀, ∃ δ, R δ₀ δ ∧ x δ ∈ N

-- def Net.adherent' (T: Set (Set X)) (R: Endorelation Δ) (x: Δ → X) (a: X): Prop :=
--   ∀ N ∈ Nbhds T a, ∀ δ₀, (Set.range (Net.tail R x δ₀) ∩ N).Nonempty

theorem Net.adherent_iff (T: Set (Set X)) (R: Endorelation Δ) (x: Δ → X) (a: X): adherent T R x a ↔ a ∈ ⋂ δ, closure T (Net.tail R x δ) := by
  sorry

theorem Net.closure_mem_iff (T: Set (Set X)) (A: Set X) (x: X):
  x ∈ closure T A ↔ ∃ Δ: Type u, ∃ R, directed_set R ∧ ∃ a: Δ → A, net_converges T R (Subtype.val ∘ a) x := by
  sorry

-- TODO: a is an adherent of image(x) iff. ∃ subnet y of x s.t. y → a.
#check Subsingleton.allEq
