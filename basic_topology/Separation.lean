import basic_topology.Net
import basic_topology.Product
import basic_topology.Metric
import basic_topology.Dense

variable {X Y D: Type*}

set_option linter.style.multiGoal false

def OpenSeparable (T: Family X): Endorelation (Set X) :=
  fun A B => ∃ U V, Open T U ∧ Open T V ∧ Disjoint U V ∧ A ⊆ U ∧ B ⊆ V

-- Separability by continuous function with respect to a target space I (which is normally the unit interval) with distinguished points 0, 1.

variable {I: Type*} [Zero I] [One I]

def FunctionSeparable (T: Family X) (TI: Family I): Endorelation (Set X) :=
  fun A B => ∃ f, Continuous T TI f ∧ (∀ a ∈ A, f a = 0) ∧ (∀ b ∈ B, f b = 1)

-- Assuming 0, 1 are distinguishable by open sets in the target space, then separability by continuous function implies separability by open sets.

variable {T: Family X} {TI: Family I}

theorem FunctionSeparable_implies_OpenSeparable {A B: Set X} (h₀: OpenSeparable TI {0} {1}) (h: FunctionSeparable T TI A B): OpenSeparable T A B := by
  obtain ⟨U, V, h₁, h₂, h₃, h₄, h₅⟩ := h₀
  obtain ⟨f, h₆, h₇, h₈⟩ := h
  exists f ⁻¹' U, f ⁻¹' V
  repeat' constructor
  · exact h₆ U h₁
  · exact h₆ V h₂
  · exact Disjoint.preimage f h₃
  · exact fun a ha ↦ h₄ (h₇ a ha)
  · exact fun b hb ↦ h₅ (h₈ b hb)

-- fréchet and hausdorff spaces
def fréchet (𝒯: Family X): Prop :=
  ∀ x y, x ≠ y → ∃ U V, U ∈ Nbhds 𝒯 x ∧ V ∈ Nbhds 𝒯 y ∧ x ∉ V ∧ y ∉ U

-- a family 𝒯 is hausdorff (aka T2) if every pair of distinct points have disjoint neighborhoods.
def hausdorff (𝒯: Family X): Prop :=
  ∀ x y, x ≠ y → ∃ U V, U ∈ Nbhds 𝒯 x ∧ V ∈ Nbhds 𝒯 y ∧ Disjoint U V

-- Alternative (preferable?) Hausdorff definition not referencing neighborhoods.
def Hausdorff (𝒯: Family X): Prop :=
  ∀ x y, x ≠ y → OpenSeparable 𝒯 {x} {y}

def regular (T: Family X): Prop :=
  ∀ x A, x ∉ A → Closed T A → OpenSeparable T A {x}

def regular_hausdorff (T: Family X): Prop :=
  hausdorff T ∧ regular T

def completely_regular (T: Family X) (TI: Family I): Prop :=
  ∀ A x, x ∉ A → Closed T A → FunctionSeparable T TI A {x}

def tychonoff (T: Family X) (TI: Family I): Prop :=
  hausdorff T ∧ completely_regular T TI

def normal (T: Family X): Prop :=
  ∀ A B , Closed T A → Closed T B → Disjoint A B → OpenSeparable T A B

def normal_hausdorff (T :Family X): Prop :=
  hausdorff T ∧ normal T

-- We will construct the nontrivial implications down the chain.

theorem hausdorff_implies_fréchet (𝒯: Family X): hausdorff 𝒯 → fréchet 𝒯 := by
  intro h x y h1
  obtain ⟨U, V, hU1, hV1, h2⟩ := h x y h1
  exists U, V
  repeat' (apply And.intro)
  · exact hU1
  · exact hV1
  · exact Disjoint.notMem_of_mem_left h2 (neighborhood_mem hU1)
  · exact Disjoint.notMem_of_mem_left (Disjoint.symm h2) (neighborhood_mem hV1)

theorem completely_regular_implies_regular (h₀: OpenSeparable TI {0} {1}) (h: completely_regular T TI): regular T := by
  intro x A h₁ h₂
  exact FunctionSeparable_implies_OpenSeparable h₀ (h A x h₁ h₂)

theorem normal_implies_completely_regular (h₀: OpenSeparable TI {0} {1}) (h: normal T): completely_regular T TI := by
  intro A B h₁ h₂
  sorry

-- the discrete topology is hausdorff
theorem discrete_hausdorff (X: Type*): hausdorff (@Set.univ (Set X)) := by
  intro x y h
  exists {x}, {y}
  repeat' (apply And.intro)
  · exact (discrete_neighborhood_iff {x} x).mpr rfl
  · exact (discrete_neighborhood_iff {y} y).mpr rfl
  · exact Set.disjoint_singleton.mpr h

-- If X has more than 1 point, the indiscrete topology is nonhausdorff
theorem indiscrete_nonhausdorff {X: Type*} {x y: X} (h: x ≠ y): ¬ hausdorff {∅, @Set.univ X} := by
  simp [hausdorff]
  exists x, y
  constructor
  · exact h
  · intro U hU
    simp_all [Nbhds, neighborhood]
    exact Nonempty.intro x

-- the indiscrete space is hausdorff iff. X has one point
theorem indiscrete_nonhausdorff_iff (X: Type*): hausdorff {∅, @Set.univ X} ↔ ∀ x y: X, x = y := by
  sorry

-- Sierpiński space is non-hausdorff
theorem sierpiński_nonhausdorff: ¬hausdorff (sierpiński_topology.Open) := by
  apply not_forall.mpr
  exists true
  apply not_forall.mpr
  exists false
  simp
  intro _ ht _ hf
  obtain ⟨U, hU1, _, hU3⟩ := hf
  simp [Disjoint]
  exists {true}
  simp
  repeat' constructor
  · exact neighborhood_mem ht
  · have: U = {false, true} := by
      rcases hU1 with _ | _ | _
      repeat simp_all
    apply hU3
    simp_all

-- simple lemma: if balls are too far apart, their intersection is empty.
lemma separated_balls [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) {x1 x2: X} {r1 r2: D} (h: r1 + r2 ≤ d x1 x2): Disjoint (openball d x1 r1) (openball d x2 r2) := by
  apply Set.disjoint_iff.mpr
  intro x ⟨hx1, hx2⟩
  apply not_lt_of_ge h
  calc
    d x1 x2 ≤ d x1 x + d x x2 := by exact hd.triangle x1 x x2
          _ = d x1 x + d x2 x := by rw [hd.symmetric x x2]
          _ < r1 + r2 := by sorry -- exact? -- add_lt_add hx1 hx2

/-
-- Every metric space is hausdorff.
-- Proof: given two distinct points x, y, let r = d(x, y) / 2. Then B(x, r) and B(y, r) are disjoint neighborhoods.
theorem metric_space_hausdorff {d: X → X → ENNReal} (hd: IsMetric d): hausdorff (metric_Opens d) := by
  intro x y neq
  let r := d x y / 2
  have: d x y ≠ 0 := (dist_nonzero_iff hd).mpr neq
  have r_pos: 0 < r := ENNReal.half_pos this
  exists openball d x r, openball d y r
  repeat' (apply And.intro)
  · exact openball_neighborhood hd x r_pos
  · exact openball_neighborhood hd y r_pos
  · simp [separated_balls hd, r]

-- If a space is not hausdorff, it is not metrizable
theorem nonhausdorff_nonmetrizable {𝒯: Topology X} (h: ¬ hausdorff 𝒯.Opens): ¬ metrizable 𝒯 ENNReal := by
  intro ⟨d, hd⟩
  rw [←hd] at h
  exact h (metric_space_hausdorff d.is_metric)

-- corollary: sierpiński space is nonmetrizable!
theorem sierpiński_nonmetrizable: ¬ metrizable sierpiński_topology ENNReal := by
  exact nonhausdorff_nonmetrizable sierpiński_nonhausdorff
-/

-- TODO
-- show the cofinite topology is Frechet but not Hausdorff
-- the antidiscrete space is not frechte
-- Let O1, O2 be topologies. If O1 ⊆ O2 then O1 (Hausdorff/Frechet) implies O2 (Hausdorff/Frechet)

theorem frechet_iff (𝒯: Family X)(hT: IsTopology 𝒯): fréchet 𝒯 ↔ ∀ x, Closed 𝒯 {x} := by
  constructor
  intro hF x
  rw[closed_iff_eq_closure]
  simp [closure,adherent ]
  ext y
  constructor
  intro hy
  simp at hy
  simp
  rw[hy]
  exact fun N a ↦ neighborhood_mem a
  intro hy
  simp at hy
  simp
  rw[fréchet] at hF
  by_contra h1
  push_neg at h1
  apply hF at h1
  obtain ⟨U,⟨ V,hU,hV, hyV, hxU⟩  ⟩:= h1
  apply hy at hU
  tauto
  exact hT
  rw[fréchet]
  intro h x y hxy
  use {y}ᶜ , {x}ᶜ
  constructor
  apply open_neighborhood
  exact hxy
  exact h y
  constructor
  apply open_neighborhood
  exact id (Ne.symm hxy)
  exact h x
  exact ⟨fun a ↦ a rfl, fun a ↦ a rfl⟩





-- show topology generated by [a, infty) is Frechet but not Hausdorff
-- we can call this the LCRI topology (left closed right infinite) or maybe just OI

/-
def LCRI_base: Set (Set ENNReal) :=
  ⋃ (a: ENNReal), {Set.Ici a}

theorem LCRI_base_is_base: is_base LCRI_base := by
  sorry
-/

theorem frechet_iff' (T: Family X)(hT: IsTopology T): fréchet T ↔ ∀ x, {x} = Set.sInter (Nbhds T x) := by
  rw[frechet_iff]
  constructor
  intro h x
  ext y
  constructor
  intro hy
  simp at hy
  rw[hy]
  exact @neighborhood_mem X T x
  intro hy
  have : Closed T {y}:= by exact h y
  rw[closed_iff_eq_closure] at this
  simp_all
  simp [closure,adherent] at this
  have h1: ∀ N∈ Nbhds T x, y ∈ N:= by exact fun N a ↦ hy N a
  by_contra h2
  push_neg at h2
  have h3: {y}ᶜ ∈ Nbhds T x := by
    apply open_neighborhood
    exact id (Ne.symm h2)
    exact h y
  apply h1 at h3
  tauto
  exact hT

  intro h x
  rw [closed_iff_eq_closure, closure]
  simp [adherent]
  ext y
  constructor
  intro hy
  simp
  simp at hy
  rw[hy]
  exact fun N a ↦ neighborhood_mem a
  intro hy
  simp at hy
  let hy1 := h y
  have : x∈ ⋂₀ Nbhds T y:= by exact hy
  rw[← hy1] at this
  simp
  simp at this
  rw[this]
  exact hT
  exact hT



















-- basis of a subspace

-- properties of topologies of metric spaces

-- product topology

-- equivalence of metrics

theorem hausdorff_iff_diagonal_closed {T: Family X} (hT: IsTopology T): hausdorff T ↔ Closed (product_topology T T) (Set.diagonal X) := by
  constructor
  intro h
  rw [Closed]
  rw [open_iff_neighborhood_of_all_points]
  intro (x1, x2) hx
  obtain ⟨N1, N2, hN1, hN2, hN⟩ := h x1 x2 hx
  obtain ⟨U1, hU1⟩ := hN1
  obtain ⟨U2, hU2⟩ := hN2
  exists {(x1, x2): X × X | x1 ∈ U1 ∧ x2 ∈ U2}
  repeat' (apply And.intro)
  simp
  simp[product_topology,unions,product_topology_basis]
  use { Set.prod U1 U2 }
  simp [Set.sUnion_singleton]
  constructor
  use U1
  constructor
  exact hU1.1
  use U2
  constructor
  exact hU2.1
  exact rfl
  exact rfl
  exact hU1.2.1
  exact hU2.2.1
  intro (y1,y2) hy
  simp
  push_neg
  by_contra h2
  simp at hy
  have hny: ¬ (Disjoint N1 N2) := by
    refine Set.not_disjoint_iff.mpr ?_
    use y1
    constructor
    apply hU1.2.2
    exact hy.1
    apply hU2.2.2
    rw[h2]
    exact hy.2
  simp_all
  exact product_topology_is_topology hT hT
  rw[Closed,hausdorff,Set.diagonal]
  intro hc x y hxy
  let xy := (x,y)
  have h1: xy∈ {p | p.1 = p.2}ᶜ := by exact hxy
  rw[open_iff_neighborhood_of_all_points] at hc
  apply hc at h1
  simp[neighborhood,product_topology] at h1
  obtain ⟨U,⟨ hU1,hU2,hU3⟩⟩  := h1
  have: ∃ A∈ product_topology_basis T T, A⊆ U∧ xy ∈ A := by
    apply boxes_subset_everywhere at hU1
    apply hU1 at hU2
    obtain ⟨ A,hA⟩ := hU2
    use A
    constructor
    exact hA.1
    constructor
    exact hA.2.2
    exact hA.2.1
    exact hT
    exact hT
  obtain ⟨ A,⟨ha1,ha2,ha3⟩ ⟩ := this
  rw[product_topology_basis] at ha1
  simp at ha1
  obtain ⟨ A1,⟨ hpa1,hpa2 ⟩ ⟩ := ha1
  obtain ⟨ A2,⟨hpa3,hpa4⟩⟩ := hpa2
  have hP: A1.prod A2 = (Set.image Prod.fst A).prod (Set.image Prod.snd A) := by
    rw[hpa4]
    exact box_equal_prod_projections
  use A1, A2
  rw[hpa4] at ha3
  constructor
  apply open_neighborhood
  exact ha3.1
  exact hpa1
  constructor
  apply open_neighborhood
  exact ha3.2
  exact hpa3
  by_contra h
  have: ∃ x, x∈ A1 ∧ x∈ A2 := by exact Set.not_disjoint_iff.mp h
  obtain ⟨ a,ha⟩ := this
  let aa := (a,a)
  have: aa∈ A1.prod A2 := by exact ha
  rw[← hpa4] at this
  apply ha2 at this
  apply hU3 at this
  tauto
  exact product_topology_is_topology hT hT

theorem hausdorff_iff_open_separable {T: Family X}: hausdorff T ↔ ∀ x y , x≠y → OpenSeparable T {x} {y} := by
  rw[hausdorff]
  constructor
  intro hT x y hxy
  rw[OpenSeparable]
  apply hT at hxy
  simp[Nbhds] at hxy
  obtain ⟨A,⟨hA,B,hB,hAB ⟩  ⟩:= hxy
  simp_all[neighborhood]
  obtain⟨ U,hU⟩ := hA
  obtain⟨ V,hV⟩ := hB
  use U
  constructor
  exact hU.1
  use V
  constructor
  exact hV.1
  constructor
  by_contra h
  rw[Set.not_disjoint_iff] at h
  obtain ⟨ x,⟨hxU,hxV ⟩ ⟩ := h
  apply hU.2.2 at hxU
  apply hV.2.2 at hxV
  have hc: ¬ (Disjoint A B):= by
    rw[Set.not_disjoint_iff]
    use x
  exact hc hAB
  constructor
  exact hU.2.1
  exact hV.2.1
  intro h x y hxy
  apply h at hxy
  rw[OpenSeparable] at hxy
  obtain ⟨U,⟨V,hU1,hV1,hUV,hxU,hyV ⟩ ⟩:= hxy
  use U, V
  simp [Nbhds]
  repeat' (apply And.intro)
  apply open_neighborhood
  exact hxU rfl
  exact hU1
  apply open_neighborhood
  exact hyV rfl
  exact hV1
  exact hUV





/-

the space X is hausdorff if for every x ≠ y
there exist disjoint neighborhoods U of x and V of y

Every metric space is hausdorff
let x ≠ y

um .. i mean pick some distance and neighborhood is any point within that dist

idk :3
i guess you can have radius = dist(x, y) / 2 ?

Suppose by contradiction exists x, f(x) ≠ g(x)

oh then is like um disjoint neighborhoods

so I get open nbhds U of f(x) and V of g(x) which are disjoint

but by density exist z1 in U ∩ D such that f(z1) = g(z1)

-/

theorem Disjoint.notMem_inter {A B: Set X} (h: Disjoint A B) (hx: x ∈ A ∩ B): False := by
  have: x ∈ A := by exact Set.mem_of_mem_inter_left hx
  have := Disjoint.notMem_of_mem_left h this
  have: x ∈ B := by exact Set.mem_of_mem_inter_right hx
  (expose_names; exact this_2 this)

theorem continuous_eq_dense_eq (T₁: Family X) (T₂: Family Y)
  (hT₁: IsTopology T₁)
  (f g: X → Y) (D: Set X) (hD: dense T₁ D)
  (hf: Continuous T₁ T₂ f)
  (hg: Continuous T₁ T₂ g)
  (h: ∀ x ∈ D, f x = g x) (h2: Hausdorff T₂): f = g := by
  ext x
  by_contra h'
  obtain ⟨U, V, h3, h4, h5, h6, h7⟩ := h2 (f x) (g x) h'
  simp_all
  have U_pre := hf U h3
  have V_pre := hg V h4
  let W := (f ⁻¹' U) ∩ (g ⁻¹' V)
  have: Open T₁ W := binary_inter_open hT₁ U_pre V_pre
  have W_nonempty: W.Nonempty := by exists x
  have: (D ∩ W).Nonempty := by exact hD W this W_nonempty
  obtain ⟨z, hz⟩ := this
  have fz_eq_gz: f z = g z := by
    apply h
    exact Set.mem_of_mem_inter_left hz
  have fz_in_U: f z ∈ U := by simp_all [W]
  have gz_in_V: g z ∈ V := by simp_all [W]
  have fz_in_V: f z ∈ V := by exact Set.mem_of_eq_of_mem fz_eq_gz gz_in_V
  have: f z ∈ U ∩ V := by exact Set.mem_inter fz_in_U fz_in_V
  exact Disjoint.notMem_inter h5 this
