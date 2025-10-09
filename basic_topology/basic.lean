/-

Formalization of basic point-set topology.

- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
- Loogle: https://loogle.lean-lang.org/
- editor shortcuts:
  - mathcal characters e.g. ℬ, 𝒩, 𝒪, 𝒯, 𝒰 are \McB, \McN, \McU, \McT, \McU
  - type subscripts (₁, ₂, ₃) in the editor via \1, \2, \3
  - type sUnion (⋃₀) and sInter (⋂₀) via \sU and \sI

-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv

set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.dupNamespace false

variable {X Y D: Type*}





/-

"Distance spaces" so that we can work in a generalized metric space.

- `DistanceSpaceStruct` is a class carrying just enough data to define a metric space, namely ≤ and + and ⊥ (the bottom element i.e. zero)

- `DistanceSpace` gives a linear order on ≤ and commutative monoid structure on +, along with compatibility that ⊥ = 0.
  - This generalized non-negative reals.

- `CompleteDistanceSpace` adds a top element ⊤ which is infinity for the extended reals.
  - It is compatible with the additive monoid by being absorbing, i.e. r + ⊤ = ⊤

-/

class DistanceSpaceStruct (D: Type*) extends LE D, LT D, Bot D, Add D

class DistanceSpace (D: Type*) extends AddCommMonoid D, LinearOrder D, CanonicallyOrderedAdd D, OrderBot D

class CompleteDistanceSpace (D: Type*) extends DistanceSpace D, CompleteLattice D

instance [DistanceSpace D]: DistanceSpaceStruct D := {}

instance [CompleteDistanceSpace D]: DistanceSpace D := {}

noncomputable instance: DistanceSpace NNReal := {}

noncomputable instance: CompleteDistanceSpace ENNReal := {}





/-

Three version of a metric space:

1. Given a function d: X → X → D, `IsMetric d` is the proposition that d is a metric.
  It is a structured proposition that comes with 4 fields, the axioms.

2. `Metric X D` is the type of all metrics on X with distance values in D.
  If `d: Metric X D` then d has two fields, `d.dist` for the distance function and `d.is_metric` for the axioms.

3. `MetricSpace D` is the type of all metric spaces valued in D.
  If `X: MetricSpace D` then `X.points` is the type of points and `X.metric` is the metric.

For the most part we can just use `IsMetric` to avoid complexity, but `Metric` is sometimes useful.

-/

structure IsMetric [DistanceSpaceStruct D] (d: X → X → D): Prop where
  dist_self_bot: ∀ x, d x x = ⊥
  dist_bot_eq: ∀ x y, d x y = ⊥ → x = y
  symmetric: ∀ x y, d x y = d y x
  triangle: ∀ x y z, d x z ≤ d x y + d y z

structure Metric (X D: Type*) [DistanceSpaceStruct D] where
  distance: X → X → D
  is_metric: IsMetric distance

structure MetricSpace (D: Type*) [DistanceSpaceStruct D] where
  points: Type*
  distance: points → points → D
  is_metric: IsMetric distance

theorem dist_zero_iff [DistanceSpace D] {d: X → X → D} (h: IsMetric d) {x y: X}: d x y = 0 ↔ x = y := by
  rw [←bot_eq_zero]
  constructor
  · apply h.dist_bot_eq
  · intro h1
    rw [h1, h.dist_self_bot]

theorem dist_nonzero_iff [DistanceSpace D] {d: X → X → D} (h: IsMetric d) {x y: X}: d x y ≠ 0 ↔ x ≠ y := by
  exact not_congr (dist_zero_iff h)

-- two points are unequal iff. their distance is positive
theorem neq_dist_pos [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x y: X): x ≠ y ↔ ⊥ < d x y := by
  constructor
  · intro h
    have := hd.dist_bot_eq x y
    have := this.mt h
    have: d x y ≠ ⊥ := by exact this
    have := bot_lt_iff_ne_bot.mpr this
    exact this
  · intro h1
    have := LT.lt.ne_bot h1
    intro h2
    have: d x y = ⊥ := by rw [h2, hd.dist_self_bot]
    contradiction





-- the discrete metric on an arbitrary type
def discrete_metric (X D: Type*) [DecidableEq X] [CompleteDistanceSpace D]: X → X → D :=
  fun x y => if x = y then ⊥ else ⊤

theorem discrete_metric_is_metric (X: Type*) [DecidableEq X] [Nontrivial D] [CompleteDistanceSpace D]: IsMetric (discrete_metric X D) := {
  dist_self_bot := by
    intro x
    simp [discrete_metric]
  dist_bot_eq := by
    intro x y
    simp_all [discrete_metric]
    intro h
    have: ⊥ = (0: D) := by exact bot_eq_zero
    have: ⊥ ≠ (⊤: D) := by exact bot_ne_top
    have: ⊤ ≠ (0: D) := by (expose_names; exact Ne.symm (ne_of_eq_of_ne (id (Eq.symm this_1)) this))
    have := h.mt this
    simp_all
  symmetric := by
    intro x y
    simp [discrete_metric]
    by_cases x = y <;> simp_all
    intro
    simp_all
  triangle := by
    intro x y z
    by_cases x = y <;> -- tactic combinator
    by_cases x = z <;>
    by_cases y = z
    repeat simp_all [discrete_metric]
}



-- Taxicab metric: given two metrics, their sum is a metric on the product space.
noncomputable def taxicab_metric [Add D] (dX: X → X → D) (dY: Y → Y → D): X × Y → X × Y → D :=
  fun (x1, y1) (x2, y2) => dX x1 x2 + dY y1 y2

theorem taxicab_is_metric [DistanceSpace D] {dX: X → X → D} {dY: Y → Y → D} (hX: IsMetric dX) (hY: IsMetric dY): IsMetric (taxicab_metric dX dY) := {
  dist_self_bot := by
    intro (x, y)
    simp [taxicab_metric, hX.dist_self_bot x, hY.dist_self_bot y]
  dist_bot_eq := by
    intro (x1, y1) (x2, y2) h
    simp_all [taxicab_metric]
    constructor
    · exact (dist_zero_iff hX).mp h.1
    · exact (dist_zero_iff hY).mp h.2
  symmetric := by
    intro _ _
    simp [taxicab_metric]
    rw [hX.symmetric, hY.symmetric]
  triangle := sorry
}



-- product metric
-- Taxicab metric: given two metrics, their sum is a metric on the product space.
noncomputable def product_metric [Max D] (dX: X → X → D) (dY: Y → Y → D): X × Y → X × Y → D :=
  fun (x1, y1) (x2, y2) => max (dX x1 x2) (dY y1 y2)

theorem product_is_metric [DistanceSpace D] {dX: X → X → D} {dY: Y → Y → D} (hX: IsMetric dX) (hY: IsMetric dY): IsMetric (product_metric dX dY) := {
  dist_self_bot := by
    intro (x, y)
    simp [product_metric, hX.dist_self_bot x, hY.dist_self_bot y]
  dist_bot_eq := by
    intro (x1, y1) (x2, y2) h
    have := max_eq_bot.mp h
    simp
    constructor
    · apply hX.dist_bot_eq
      exact this.left
    · apply hY.dist_bot_eq
      exact this.right
  symmetric := by
    intro _ _
    simp [product_metric]
    rw [hX.symmetric, hY.symmetric]
  triangle := by
    sorry
}





def isometry (dX: X → X → D) (dY: Y → Y → D) (f: X → Y): Prop :=
  ∀ x1 x2, dX x1 x2 = dY (f x1) (f x2)

theorem isometry_id (d: X → X → D): isometry d d id := by
  intro _ _; rfl

theorem isometry_is_injective [DistanceSpaceStruct D] {dX: X → X → D} {dY: Y → Y → D} (hX: IsMetric dX) (hY: IsMetric dY) (f: X → Y) (hf: isometry dX dY f): Function.Injective f := by
  intro _ _ h
  apply hX.dist_bot_eq
  rw [hf, ←h]
  apply hY.dist_self_bot





def openball [DistanceSpaceStruct D] (d: X → X → D) (x: X) (r: D): Set X :=
 {z | d x z < r}

def closedball [DistanceSpaceStruct D] (d: X → X → D) (x: X) (r: D): Set X :=
 {z | d x z ≤ r}

def sphere [DistanceSpaceStruct D] (d: X → X → D) (x: X) (r: D): Set X :=
 {z | d x z = r}

-- The open ball of radius zero is empty
theorem openball_zero_empty [DistanceSpace D] {d: X → X → D} (x: X): openball d x ⊥ = ∅ := by
  rw [openball]
  ext z
  constructor
  · intro h
    apply not_le_of_gt h
    apply bot_le
  · exact False.elim

-- x ∈ B(x, r) iff. r > ⊥
theorem openball_mem_iff [DistanceSpaceStruct D] {d: X → X → D} (hd: IsMetric d) (x: X) (r: D): x ∈ openball d x r ↔ ⊥ < r := by
  constructor
  · intro h
    simp [openball] at h
    rw [hd.dist_self_bot] at h
    exact h
  · intro h
    simp [openball]
    rw [hd.dist_self_bot]
    exact h

-- The closed ball of radius zero is a singleton
theorem closedball_zero_singleton [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x: X): closedball d x ⊥ = {x} := by
  ext z
  simp [closedball]
  constructor
  · intro h
    apply Eq.symm
    exact (dist_zero_iff hd).mp h
  · intro h
    rw [h, ←bot_eq_zero]
    apply hd.dist_self_bot

-- In the discrete metric, if 0 < r ≤ ⊤ then B(x, r) = {x}
theorem discrete_openball_singleton [DecidableEq X] [CompleteDistanceSpace D] (x: X) {r: D} (h1: ⊥ < r): openball (discrete_metric X D) x r = {x} := by
  ext z
  simp_all [openball]
  constructor
  · intro h
    have := LT.lt.ne_top h
    simp_all [discrete_metric]
  · intro h
    simp_all [discrete_metric]

-- If s = r - d(x, x0) then B(x0, s) ⊆ B(x, r)
theorem openball_mem_smaller_ball [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) {x x0: X} {r: D}: openball d x0 r ⊆ openball d x (r + d x x0) := by
  intro z hz
  sorry
  -- calc
  --   d x z ≤ d x x0 + d x0 z       := by exact hd.triangle x x0 z
  --       _ < d x x0 + (r - d x x0) := by sorry
  --       _ = r                     := by sorry

-- If x0 ∈ C(x, r)ᶜ and s = r - d(x, x0) then B(x0, s) ⊆ C(x, r)ᶜ
theorem closedball_compl_mem [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) {x x0: X} {r: D} (hx0: x0 ∈ (closedball d x r)ᶜ): openball d x0 r ⊆ (closedball d x (r + d x x0))ᶜ := by
  sorry

-- definition of an open set in a metric space
-- we will give them the prefix `metric_` since we need these names later
-- note its important that 0 < r in the definition of open set, even though this isnt required to be an open ball.
-- (otherwise every set is trivially open by taking r=0 at every point.)
def metric_openset [DistanceSpaceStruct D] (d: X → X → D) (A: Set X): Prop :=
  ∀ x ∈ A, ∃ r, ⊥ < r ∧ openball d x r ⊆ A

def metric_closedset [DistanceSpaceStruct D] (d: X → X → D) (A: Set X): Prop :=
  metric_openset d Aᶜ

def metric_clopenset [DistanceSpaceStruct D] (d: X → X → D) (A: Set X): Prop :=
  metric_openset d A ∧ metric_closedset d A

-- The empty set is clopen
theorem metric_empty_clopen [DistanceSpace D] [Nontrivial D] (d: X → X → D): metric_clopenset d ∅ := by
  constructor
  · intro _ _
    exists ⊥
  · intro _ hx
    obtain ⟨r, hr⟩ := exists_ne (⊥: D)
    exists r
    constructor
    · simp_all
      exact pos_of_ne_zero hr
    · exact fun _ _ => hx

-- If A is clopen then Aᶜ is clopen
theorem clopen_implies_compl_clopen [DistanceSpaceStruct D] (d: X → X → D) {A: Set X} (h: metric_clopenset d A): metric_clopenset d Aᶜ := by
  constructor
  · exact h.right
  · simp [metric_closedset]
    exact h.left

-- A is clopen iff. Aᶜ is clopen
theorem clopen_iff_compl_clopen [DistanceSpaceStruct D] (d: X → X → D) (A: Set X): metric_clopenset d A ↔ metric_clopenset d Aᶜ := by
  constructor
  · exact clopen_implies_compl_clopen d
  · intro h
    rw [←compl_compl A]
    exact clopen_implies_compl_clopen d h

-- The whole space is clopen
theorem metric_univ_clopen [DistanceSpace D] [Nontrivial D] (d: X → X → D): metric_clopenset d Set.univ := by
  rw [←Set.compl_empty]
  exact (clopen_iff_compl_clopen d ∅).mp (metric_empty_clopen d)

-- Open ball is open
-- TODO this needs work since we can't subtract..
theorem openball_open [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x: X) (r: D): metric_openset d (openball d x r) := by
  intro z hz
  sorry
  -- exists r - d x z
  -- constructor
  -- · exact tsub_pos_of_lt hz
  -- · exact openball_mem_smaller_ball hd

-- Closed ball is closed
theorem closedball_closed [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x: X) (r: D): metric_closedset d (closedball d x r) := by
  intro x0 hx0
  sorry
  -- exists d x x0 - r
  -- constructor
  -- · simp_all [closedball]
  -- · exact closedball_compl_mem hd hx0

-- the set of open balls in a metric space
def openballs [DistanceSpaceStruct D] (d: X → X → D): Set (Set X) :=
  ⋃ (x: X), ⋃ (r: D), {openball d x r}

theorem open_iff_sUnion_of_balls [DistanceSpace D] (d: X → X → D) (hd: IsMetric d) (A: Set X): metric_openset d A ↔ ∃ 𝒰 ⊆ openballs d, A = ⋃₀ 𝒰 := by
  apply Iff.intro
  · intro h
    exists fun U => U ⊆ A ∧ U ∈ openballs d
    constructor
    · intro U ⟨_, hU2⟩
      exact hU2
    · ext z
      constructor
      · intro hz
        obtain ⟨r, hr1, hr2⟩ := h z hz
        exists openball d z r
        sorry
        -- repeat' constructor
        -- · exact hr2
        -- · exact z
      · intro ⟨U, ⟨hU1, _⟩, hU3⟩
        exact hU1 hU3
  · intro ⟨𝒰, h𝒰1, h𝒰2⟩
    rw [h𝒰2]
    intro z ⟨U, hU1, hU2⟩
    have := h𝒰1 hU1
    simp_all [openballs]
    obtain ⟨x, r, hx⟩ := this
    sorry
    -- exists r - d x z
    -- constructor
    -- · rw [←hx] at hU2
    --   simp_all [openball]
    -- · calc
    --     openball d z (r - d x z)
    --     _ ⊆ openball d x r := openball_mem_smaller_ball hd
    --     _ = U              := hx
    --     _ ⊆ ⋃₀ 𝒰          := Set.subset_sUnion_of_subset 𝒰 U (fun ⦃a⦄ a ↦ a) hU1

-- the set of all open sets in a metric space
def metric_opensets [DistanceSpace D] (d: X → X → D): Set (Set X) :=
 {A | metric_openset d A}

theorem openballs_sub_opensets [DistanceSpace D] {d: X → X → D} (hd: IsMetric d): openballs d ⊆ metric_opensets d := by
  intro _ hU
  simp_all [openballs]
  obtain ⟨x, r, hU⟩ := hU
  rw [←hU]
  exact openball_open hd x r

-- Every set is open in the topology generated by the discrete metric.
theorem discrete_opensets (X D: Type*) [CompleteDistanceSpace D] [Nontrivial D] [DecidableEq X]: metric_opensets (discrete_metric X D) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  intro A hA x hx
  exists ⊤
  constructor
  · exact bot_lt_top
  · sorry -- simp [discrete_openball_singleton x bot_lt_top]

-- in a metric space, arbitrary unions of open sets are open (doesnt actually depend on d being a metric)
theorem metric_open_sUnion [DistanceSpace D] {d: X → X → D} {C: Set (Set X)} (h: C ⊆ metric_opensets d): ⋃₀ C ∈ metric_opensets d := by
  intro z ⟨U, hU1, hU2⟩
  obtain ⟨r, hr1, hr2⟩ := h hU1 z hU2
  exists r
  constructor
  · exact hr1
  · exact Set.subset_sUnion_of_subset C U hr2 hU1

-- in a metric space, finite intersections of open sets are open
theorem metric_open_finite_sInter [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) {C: Set (Set X)} (h1: C ⊆ metric_opensets d) (h2: Finite C): ⋂₀ C ∈ metric_opensets d := by
  intro z hz
  simp at hz

  -- should be able to get a finite set of radii
  sorry





/-

Definition of topological space. Like for metric spaces:
- Given a type X and a collection of subsets 𝒯, `IsTopology 𝒯` is the statement that 𝒯 forms a topology.
- `Topology X` is the type of all topologies on `X`.
- `TopologicalSpace` is the type of all topological spaces.

For simplicity I guess we will work with `IsTopology` mostly.

-/

structure IsTopology (𝒯: Set (Set X)): Prop where
  sUnion: ∀ 𝒰 ⊆ 𝒯, ⋃₀ 𝒰 ∈ 𝒯
  finite_sInter: ∀ 𝒰 ⊆ 𝒯, Finite 𝒰 → ⋂₀ 𝒰 ∈ 𝒯

structure Topology (X: Type*) where
  opensets: Set (Set X)
  is_topology: IsTopology opensets

structure TopologicalSpace where
  points: Type*
  topology: Topology points

theorem empty_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): ∅ ∈ 𝒯 := by
  have: (∅: Set X) = ⋃₀ ∅ := by ext; simp
  rw [this]
  apply h𝒯.sUnion
  exact Set.empty_subset 𝒯

theorem univ_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): Set.univ ∈ 𝒯 := by
  have: (@Set.univ X) = ⋂₀ ∅ := by ext; simp
  rw [this]
  apply h𝒯.finite_sInter
  · exact Set.empty_subset 𝒯
  · exact Finite.of_subsingleton

-- Binary unions and intersections of open sets are open
theorem binary_union_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: A ∈ 𝒯) (hB: B ∈ 𝒯): A ∪ B ∈ 𝒯 := by
  have: A ∪ B = ⋃₀ {A, B} := by ext; simp
  rw [this]
  apply h𝒯.sUnion
  exact Set.pair_subset hA hB

theorem binary_inter_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: A ∈ 𝒯) (hB: B ∈ 𝒯): A ∩ B ∈ 𝒯 := by
  have: A ∩ B = ⋂₀ {A, B} := by ext; simp
  rw [this]
  apply h𝒯.finite_sInter
  · exact Set.pair_subset hA hB
  · exact Finite.Set.finite_insert A {B}

-- The union of a sequence of open sets is open
theorem seq_union_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A: ℕ → Set X} (h: ∀ n, A n ∈ 𝒯): Set.iUnion A ∈ 𝒯 := by
  apply h𝒯.sUnion
  exact Set.range_subset_iff.mpr h

-- theorem: finite intersection property is equivalent to binary intersections plus whole set
 theorem finite_inter_iff (T: Set (Set X)): (∀ U ⊆ T, U.Finite → ⋂₀ U ∈ T) ↔ Set.univ ∈ T ∧ ∀ A ∈ T, ∀ B ∈ T, A ∩ B ∈ T := by
  constructor
  · intro h
    constructor
    · rw [←Set.sInter_empty]
      apply h
      · apply Set.empty_subset
      · exact Set.finite_empty
    · intro _ hA _ hB
      rw [(Set.sInter_pair _ _).symm]
      apply h
      · exact Set.pair_subset hA hB
      · apply Set.toFinite
  intro ⟨_, hAB⟩ _ hU1 hU2
  refine Set.Finite.induction_on_subset _ hU2 ?empty ?insert
  · simp_all
  · intro _ _ hS _ _ ih
    rw [Set.sInter_insert]
    apply hAB
    · exact hU1 hS
    · exact ih

def openset (𝒯: Set (Set X)) (A: Set X): Prop :=
  A ∈ 𝒯

def closedset (𝒯: Set (Set X)) (A: Set X): Prop :=
  Aᶜ ∈ 𝒯

def clopenset (𝒯: Set (Set X)) (A: Set X): Prop :=
  openset 𝒯 A ∧ closedset 𝒯 A

-- pointless definition but sometimes feels right
def opensets (𝒯: Set (Set X)): Set (Set X) :=
  𝒯

def closedsets (𝒯: Set (Set X)): Set (Set X) :=
  {A | closedset 𝒯 A}

def clopensets (𝒯: Set (Set X)): Set (Set X) :=
  opensets 𝒯 ∩ closedsets 𝒯

theorem closedset_sInter {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): ∀ 𝒰 ⊆ closedsets 𝒯, ⋂₀ 𝒰 ∈ closedsets 𝒯 := by
  sorry

theorem closedset_finite_sUnion {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): ∀ 𝒰 ⊆ closedsets 𝒯, Finite 𝒰 → ⋃₀ 𝒰 ∈ closedsets 𝒯 := by
  sorry

theorem binary_union_closed {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: closedset 𝒯 A) (hB: closedset 𝒯 B): closedset 𝒯 (A ∪ B) := by
  sorry

theorem binary_inter_closed {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: closedset 𝒯 A) (hB: closedset 𝒯 B): closedset 𝒯 (A ∩ B) := by
  sorry

-- The union of a sequence of open sets is open
theorem seq_inter_closed {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A: ℕ → Set X} (h: ∀ n, closedset 𝒯 (A n)): closedset 𝒯 (Set.iInter A) := by
  sorry

-- the set of all subsets is a topology, aka the discrete topology
theorem discrete_is_topology (X: Type*): IsTopology (@Set.univ (Set X)) := {
  sUnion := by intros; trivial
  finite_sInter := by intros; trivial
}

-- the indiscrete (aka antidiscrete) topology! it is slightly less trivial to prove..
theorem indiscrete_is_topology (X: Type*): IsTopology {∅, @Set.univ X} := {
  sUnion := by apply Set.sUnion_mem_empty_univ
  finite_sInter := by
    intro 𝒰 h𝒰 _
    simp
    by_cases h: ∅ ∈ 𝒰
    · apply Or.inl
      exact Set.subset_eq_empty (fun x hx ↦ hx ∅ h) rfl
    · apply Or.inr
      intro _ hU
      match h𝒰 hU with
      | Or.inl h' => rw [h'] at hU; contradiction
      | Or.inr h' => exact h'
}

-- the opensets in a metric space form a topology
theorem metric_opensets_is_topology [DistanceSpace D] {d: X → X → D} (hd: IsMetric d): IsTopology (metric_opensets d) := {
  sUnion := by intro; exact metric_open_sUnion
  finite_sInter := by intro; exact metric_open_finite_sInter hd
}

-- given a metric on X, put a topology on X
def metric_to_topology [DistanceSpace D] (d: Metric X D): Topology X := {
  opensets := metric_opensets d.distance
  is_topology := metric_opensets_is_topology d.is_metric
}

def metrizable (𝒯: Topology X) (D: Type*) [DistanceSpace D]: Prop :=
  ∃ d: Metric X D, metric_to_topology d = 𝒯

-- the Sierpiński topology define on Bool with {true} open
def sierpiński_opensets: Set (Set Bool) :=
 {{}, {true}, {false, true}}

-- Helper lemma: in the sierpinski topology a set is open iff. it's subsingleton or the whole space.
theorem sierpiński_open_iff (A: Set Bool): A ∈ sierpiński_opensets ↔ A ⊆ {true} ∨ A = Set.univ := by
  constructor
  · intro h
    rcases h with _ | _ | _
    repeat simp_all
  · intro; simp [sierpiński_opensets]
    by_cases false ∈ A <;> by_cases true ∈ A
    repeat simp_all
    · right; left; ext x; match x with
      | false => simp_all
      | true => simp_all
    · left; ext x; match x with
      | false => simp_all
      | true => simp_all

-- this proof was very difficult despite being a space containig 2 points...
theorem sierpiński_is_topology: IsTopology sierpiński_opensets := {
  sUnion := by
    intro 𝒰 h𝒰
    by_cases h: ∀ U ∈ 𝒰, U ⊆ {true} -- either all of them are subsingleton, or one of them is the universe
    · apply (sierpiński_open_iff _).mpr
      exact Or.inl (Set.sUnion_subset h)
    · apply (sierpiński_open_iff _).mpr
      apply Or.inr
      simp at h
      obtain ⟨U, hU⟩ := h
      apply Set.univ_subset_iff.mp
      apply Set.subset_sUnion_of_subset _ U
      · have: U = Set.univ := by
          match (sierpiński_open_iff U).mp (h𝒰 hU.left) with
          | Or.inl _ => simp_all
          | Or.inr h => exact h
        rw [this]
      · exact hU.left
  finite_sInter := by
    intro 𝒰 h𝒰 _ -- either all of them are universes, or at least one is subsingleton
    by_cases h: ∀ U ∈ 𝒰, U = Set.univ
    · apply (sierpiński_open_iff _).mpr
      exact Or.inr (Set.sInter_eq_univ.mpr h)
    · simp at h
      obtain ⟨U, hU⟩ := h
      have: U ⊆ {true} := by have := ((sierpiński_open_iff U).mp (h𝒰 hU.left)); simp_all
      have: ⋂₀ 𝒰 ⊆ {true} := by simp; exists U; simp_all
      apply (sierpiński_open_iff _).mpr
      exact Or.inl this
}

def sierpiński_topology: Topology Bool := {
  opensets := sierpiński_opensets
  is_topology := sierpiński_is_topology
}





-- Definition: ℬ is a base for 𝒯 if every open set of 𝒯 is a union of sets from ℬ
def base (𝒯 ℬ: Set (Set X)): Prop :=
  ℬ ⊆ 𝒯 ∧ ∀ U ∈ 𝒯, ∃ 𝒰 ⊆ ℬ, U = ⋃₀ 𝒰

-- Every topology is a base for itself.
theorem base_self (𝒯: Set (Set X)): base 𝒯 𝒯 := by
constructor
· rfl
· intro U hU
  exists {U}
  constructor
  · exact Set.singleton_subset_iff.mpr hU
  · ext; simp

-- ℬ is a base for 𝒯 iff. ∀ U ∈ 𝒯, ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ⊆ U. Does not require 𝒯 to be a topology.
theorem base_iff (𝒯 ℬ: Set (Set X)): base 𝒯 ℬ ↔ ℬ ⊆ 𝒯 ∧ ∀ U ∈ 𝒯, ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ U := by
  constructor
  · intro h
    constructor
    · exact h.left
    · intro U hU x hx
      obtain ⟨C, hC⟩ := h.right U hU
      rw [hC.right] at hx
      obtain ⟨Bx, hBx⟩ := hx
      exists Bx
      repeat' constructor
      · exact hC.left hBx.left
      · exact hBx.right
      · rw [hC.right]
        intro x hx
        apply Set.mem_sUnion.mpr
        exists Bx
        constructor
        · exact hBx.left
        · exact hx
  · intro h
    constructor
    · exact h.left
    · intro U hU
      exists {B ∈ ℬ | B ⊆ U}
      simp
      ext x
      constructor
      · intro hx
        obtain ⟨B, _, _, _⟩ := h.right U hU x hx
        exists B
      · intro  ⟨B, ⟨_, hB2⟩, hB3⟩
        exact hB2 hB3

-- The set ℬ = {{x} | x ∈ X} is a base for the discrete topology.
theorem discrete_base (X: Type*): base (@Set.univ (Set X)) (⋃ x, {x}) := by
  apply (base_iff _ _).mpr
  constructor
  · exact fun _ _ => trivial
  · intro U hU x hx
    exists {x}
    repeat' (apply And.intro)
    · simp
    · rfl
    · exact Set.singleton_subset_iff.mpr hx

-- The set ℬ = {{X}} is a base for the indiscrete topology.
theorem indiscrete_base (X: Type*): base {∅, @Set.univ X} {@Set.univ X} := by
  constructor
  · apply Set.subset_insert
  · intro U hU
    match hU with
    | Or.inl _ => exists ∅; simp_all
    | Or.inr _ => exists {Set.univ}; simp_all

-- The set of open balls is a base for the metric topology
theorem metric_openballs_base [DistanceSpace D] {d: X → X → D} (hd: IsMetric d): base (metric_opensets d) (openballs d) := by
  apply (base_iff _ _).mpr
  constructor
  · exact openballs_sub_opensets hd
  · intro U hU x hx
    obtain ⟨r, hr1, hr2⟩ := hU x hx
    exists openball d x r
    repeat' (apply And.intro)
    · simp [openballs]
    · exact (openball_mem_iff hd x r).mpr hr1
    · exact hr2

-- sierpiński base
theorem sierpiński_base : base (sierpiński_opensets) {{true}, {false, true}} := by
  constructor
  · simp [sierpiński_opensets]
  · intro U hU
    by_cases false ∈ U
    · exists {{false, true}}
      constructor
      · apply Set.subset_insert
      · by_cases true ∈ U <;>
          cases hU with
          | inl => simp_all
          | inr h => cases h with
            | inl => simp_all
            | inr => simp_all
    · by_cases ht: true ∈ U
      · exists {{true}}
        cases hU with
        | inl => simp_all
        | inr h => cases h with
          | inl => simp_all
          | inr => simp_all
      · exists {}
        cases hU with
        | inl => simp_all
        | inr h => cases h with
          | inl => simp_all
          | inr => simp_all

-- We say ℬ "is a base" if there exists a topology for which it is a base.
def is_base (ℬ: Set (Set X)): Prop :=
  ∃ 𝒯, IsTopology 𝒯 ∧ base 𝒯 ℬ

-- If 𝒯 is a topology then 𝒯 is a base... for itself.
theorem topology_is_base {𝒯: Set (Set X)} (h: IsTopology 𝒯): is_base 𝒯 := by
  exists 𝒯
  exact ⟨h, base_self 𝒯⟩

-- If ℬ is a base for a topology 𝒯 is a topology then ℬ is a base... for 𝒯.
theorem base_is_base {𝒯 ℬ: Set (Set X)} (h1: IsTopology 𝒯) (h2: base 𝒯 ℬ): is_base ℬ := by
  exists 𝒯

-- Given an arbitrary collection ℬ, `unions ℬ` is the set of unions obtained of sets from ℬ.
def unions (ℬ: Set (Set X)): Set (Set X) :=
  ⋃ 𝒰 ⊆ ℬ, {⋃₀ 𝒰}

-- some simple theorems about `unions`
theorem unions_sub (ℬ: Set (Set X)): ℬ ⊆ unions ℬ := by
  intro U _
  simp [unions]
  exists {U}
  simp_all

theorem unions_mono {ℬ ℬ': Set (Set X)} (h: ℬ ⊆ ℬ'): unions ℬ ⊆ unions ℬ' := by
  simp_all [unions]
  intro B hB
  exists B
  constructor
  · exact le_trans hB h
  · rfl

-- the unions operator is idempotent
-- forward direction is obvious
-- for the reverse, the idea is if U = ⋃ i, V i and each V i = ⋃ j, B i j then U = ⋃ i j, B i j
theorem unions_idem {ℬ: Set (Set X)}: unions ℬ = unions (unions ℬ) := by
  apply le_antisymm
  · apply unions_sub
  · intro U hU
    simp_all [unions]
    obtain ⟨a, ha1, ha2⟩ := hU
    simp_all
    rw [←ha2]
    exists a
    sorry

theorem unions_topology {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): 𝒯 = unions 𝒯 := by
  apply le_antisymm
  · apply unions_sub
  · intro U hU
    simp_all [unions]
    obtain ⟨𝒰, h𝒰1, h𝒰2⟩ := hU
    rw [h𝒰2]
    exact h𝒯.sUnion 𝒰 h𝒰1

theorem base_unions (ℬ: Set (Set X)): base (unions ℬ) ℬ := by
  constructor
  · apply unions_sub
  · intro U hU
    simp_all [unions]

theorem base_iff_unions {𝒯 ℬ: Set (Set X)}: base 𝒯 ℬ ↔ ℬ ⊆ 𝒯 ∧ 𝒯 = unions ℬ := by
  constructor
  · intro h
    constructor
    · exact h.left
    · sorry
  · sorry

-- ℬ is a base iff. `unions ℬ` is a topology.
theorem is_base_iff_unions_topology (ℬ: Set (Set X)): is_base ℬ ↔ IsTopology (unions ℬ) := by
  --simp [unions]
  apply Iff.intro
  · intro ⟨𝒯, h𝒯₁, h𝒯₂, h𝒯₃⟩
    have: 𝒯 = unions ℬ := by
      apply le_antisymm


      sorry -- exact?
      rw [unions_topology h𝒯₁]
      exact unions_mono h𝒯₂
    rw [←this]
    exact h𝒯₁
  · intro h
    exists unions ℬ
    constructor
    · exact h
    · constructor
      · apply unions_sub
      · simp [unions]

structure base_conditions (ℬ: Set (Set X)): Prop where
  B1: X = ⋃₀ ℬ
  B2: ∀ B' ∈ ℬ, ∀ B'' ∈ ℬ, ∀ x ∈ B' ∩ B'', ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ B' ∩ B''

theorem is_base_iff_base_conditions (ℬ: Set (Set X)): is_base ℬ ↔ base_conditions ℬ := by
  constructor
  · intro ⟨T, hT₁, hT₂⟩
    constructor
    · sorry
    · intro B'  hb' B'' hB'' x hx
      sorry
  · intro h
    sorry

-- TODO: suppose T is generated by B. Then U is open iff. forall x in U, exists B in B, x in B sub U.





def neighborhood (𝒯: Set (Set X)) (N: Set X) (x: X): Prop :=
  ∃ U ∈ 𝒯, x ∈ U ∧ U ⊆ N

-- The whole space is a neighborhood of every point
theorem neighborhood_univ {𝒯: Set (Set X)} (h: IsTopology 𝒯) (x: X): neighborhood 𝒯 Set.univ x := by
  exists Set.univ
  simp
  exact univ_open h

-- If x ∈ U and U is open then U is a neighborhood of x
theorem open_neighborhood (𝒯: Set (Set X)) {U: Set X} {x: X} (h1: x ∈ U) (h2: U ∈ 𝒯): neighborhood 𝒯 U x := by
  exists U

-- A set is open iff. it is a neighborhood of all its points.
theorem open_iff_neighborhood_of_all_points {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A: Set X): A ∈ 𝒯 ↔ ∀ x ∈ A, neighborhood 𝒯 A x := by
  constructor
  · intro hA x hx
    exists A
  · intro h
    have : A = ⋃₀ {U | ∃ x ∈ A, U ∈ 𝒯 ∧ x ∈ U ∧ U ⊆ A} := by
      ext y
      constructor
      · intro hy
        rcases h y hy with ⟨U, hU, hyU, hUA⟩
        refine Set.mem_sUnion.mpr ⟨U, ?_, hyU⟩
        exact ⟨y, hy, hU, hyU, hUA⟩
      · intro hy
        rcases Set.mem_sUnion.mp hy with ⟨U, ⟨x, hxA, hU, hxU, hUA⟩, hyU⟩
        exact hUA hyU
    rw [this]
    apply h𝒯.sUnion
    intro U hU
    rcases hU with ⟨x,hx⟩
    rcases hx with ⟨h1,h2,h3⟩
    exact h2

-- In the discrete topology, N is a neighborhood of x iff x ∈ N.
theorem discrete_neighborhood_iff {X: Type*} (N: Set X) (x: X): neighborhood Set.univ N x ↔ x ∈ N := by
  constructor
  · intro ⟨U, _, hU2, hU3⟩
    exact hU3 hU2
  · intro
    exists {x}
    simp_all

-- In the indiscrete topology, N is a neighborhood of x iff N is the whole space
theorem indiscrete_neighborhood_iff {X: Type*} (N: Set X) (x: X): neighborhood {∅, Set.univ} N x ↔ N = Set.univ := by
  constructor
  · intro ⟨_, _, hU2, _⟩
    simp_all [ne_of_mem_of_not_mem' hU2]
  · intro h
    rw [h]
    apply neighborhood_univ (indiscrete_is_topology X)

-- The set of neighborhoods of a point
def Nbhds (𝒯: Set (Set X)) (x: X): Set (Set X) :=
 {N | neighborhood 𝒯 N x}

-- neighborhood properties
-- N1: if A is a neighborhood and A ⊆ B then B is a neighborhood
theorem neighborhood_upward_closed {𝒯: Set (Set X)} (x: X) {A B: Set X} (h1: neighborhood 𝒯 A x) (h2: A ⊆ B): neighborhood 𝒯 B x := by
  obtain ⟨U, hU1, hU2, hU3⟩ := h1
  exists U
  repeat' constructor
  · exact hU1
  · exact hU2
  · exact le_trans hU3 h2

-- N2: every finite intersection of neighborhoods is a neighborhood
theorem neighborhood_finite_inter {𝒯: Set (Set X)} (x: X) (𝒩: Set (Set X)) (h1: 𝒩 ⊆ Nbhds 𝒯 x) (h2: Finite 𝒩): ⋂₀ 𝒩 ∈ Nbhds 𝒯 x := by
  sorry

-- N3: x belongs to all its neighborhoods
theorem neighborhood_mem {𝒯: Set (Set X)} {x: X} {N: Set X} (h: neighborhood 𝒯 N x): x ∈ N := by
  obtain ⟨_, _, hU2, hU3⟩ := h
  exact hU3 hU2

-- N4: if V is a neighborhood of x, there exists a neighborhood W of x such that for all y in W, V is a neighborhood of y.
theorem neighborhood_N4 {𝒯: Set (Set X)} {x: X} {V: Set X} (h: neighborhood 𝒯 V x): ∃ W ∈ Nbhds 𝒯 x, ∀ y ∈ W, V ∈ Nbhds 𝒯 y := sorry

-- preceding 4 properties packaged as follows:
structure neighborhood_axioms (𝒩: X → Set (Set X)): Prop where
  upward_closed: ∀ x, ∀ A B: Set X, A ∈ 𝒩 x → A ⊆ B → B ∈ 𝒩 x
  finite_inter: ∀ x, ∀ 𝒰 ⊆ 𝒩 x, Finite 𝒰 → ⋂₀ 𝒰 ∈ 𝒩 x
  point_mem: ∀ x, ∀ N ∈ 𝒩 x, x ∈ N
  N4: ∀ x, ∀ V ∈ 𝒩 x, ∃ W ∈ 𝒩 x, ∀ y ∈ W, V ∈ 𝒩 y -- rename

-- Nhbds satisties these as we just showed
theorem nbhds_obeys_neighborhood_axioms {𝒯: Set (Set X)}: neighborhood_axioms (Nbhds 𝒯) := {
  upward_closed := neighborhood_upward_closed
  finite_inter := neighborhood_finite_inter
  point_mem := fun _ _ => neighborhood_mem
  N4 := fun _ _ => neighborhood_N4
}

def neighborhood_topology (𝒩: X → Set (Set X)): Set (Set X) :=
 {U | ∀ x ∈ U, U ∈ 𝒩 x}

theorem neighborhood_axioms_unique_topology (𝒩: X → Set (Set X)) (h𝒩: neighborhood_axioms 𝒩): ∃! 𝒯, (IsTopology 𝒯 ∧ 𝒩 = Nbhds 𝒯) := by
  exists neighborhood_topology 𝒩
  repeat' (apply And.intro)
  · sorry -- show that `neighborhood_topology 𝒩` is a topology
  · sorry -- show that `𝒩 = Nbhds (neighborhood_topology 𝒩)`
  · intro 𝒩' ⟨h1, h2⟩
    sorry -- suppose 𝒩' is a topology and 𝒩 = Nbhds 𝒩', want to show 𝒩' = neighborhood_topology 𝒩

-- TODO: define neighrbohood topology

-- TODO: fundamental neighborhood system aka neighborhood basis





def interior_point (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  neighborhood 𝒯 A x

def interior (𝒯: Set (Set X)) (A: Set X): Set X :=
 {x | interior_point 𝒯 A x}

-- Interior is monotone: if A ⊆ B then interior(A) ⊆ interior(B)
theorem interior_monotone (𝒯: Set (Set X)) {A B: Set X} (h: A ⊆ B): interior 𝒯 A ⊆ interior 𝒯 B := by
  simp [interior, interior_point]
  intro x hx
  exact neighborhood_upward_closed x hx h

-- Interior of the empty set is empty
theorem interior_empty (𝒯: Set (Set X)): interior 𝒯 ∅ = ∅ := by
  simp [interior, neighborhood, interior_point]

-- Interior of the universe is itself
theorem interior_univ {𝒯: Set (Set X)} (h: IsTopology 𝒯): interior 𝒯 Set.univ = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  intro _ _
  apply neighborhood_univ h

-- Interior is a subset of the original set
theorem interior_subset_self (𝒯: Set (Set X)) (A: Set X): interior 𝒯 A ⊆ A := by
  exact fun _ => neighborhood_mem

-- Interior is idempotent: interior(interior(A)) = interior(A)
theorem interior_idempotent (𝒯: Set (Set X)) (A: Set X): interior 𝒯 (interior 𝒯 A) = interior 𝒯 A := by
  apply le_antisymm
  · apply interior_subset_self
  · intro _ hx
    simp_all [interior, interior_point, neighborhood]
    obtain ⟨U, _, _, _⟩ := hx
    exists U
    repeat' constructor; simp_all
    intro _ _
    exists U

-- The interior is open
theorem interior_open {𝒯: Set (Set X)} (h: IsTopology 𝒯) (A: Set X): interior 𝒯 A ∈ 𝒯 := by
  apply (open_iff_neighborhood_of_all_points h (interior 𝒯 A)).mpr
  intro _ hx
  obtain ⟨U, hU₁, hU₂, _⟩ := hx
  exists U
  repeat' constructor
  · exact hU₁
  · exact hU₂
  · intro _ _
    exists U

-- The interior of A is largest open subset of A
theorem interior_largest_open_subset {𝒯: Set (Set X)} {A U: Set X} (h1: U ∈ 𝒯) (h2: U ⊆ A): U ⊆ interior 𝒯 A := by
  rw[interior]
  intro y hy
  refine Set.mem_setOf.mpr ?_
  rw[interior_point]
  rw[neighborhood]
  use U

-- The interior of A is the union of all open subsets of A.
-- (Is this proof beautiful or ugly?)
theorem interior_eq_union_open_subsets {𝒯: Set (Set X)} {A: Set X}: interior 𝒯 A = ⋃₀ {U ∈ 𝒯 | U ⊆ A} := by
  ext
  constructor
  · intro ⟨U, _, _, _⟩
    exists U
  · intro ⟨U, ⟨_, _⟩, _⟩
    exists U

-- A set is open iff. it is its own interior
theorem open_iff_eq_interior {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A: Set X): A ∈ 𝒯 ↔ A = interior 𝒯 A := by
  constructor
  · intro h
    apply Set.Subset.antisymm_iff.mpr
    constructor
    · apply interior_largest_open_subset h; rfl
    · apply interior_subset_self
  · intro h
    rw [h]
    apply interior_open h𝒯


-- interior (A ∩ B) = interior A ∩ interior B
theorem interior_inter_eq {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A B: Set X): interior 𝒯 (A ∩ B) = interior 𝒯 A ∩ interior 𝒯 B := by
  ext
  constructor
  · intro hx
    constructor
    · exact interior_monotone 𝒯 Set.inter_subset_left hx
    · exact interior_monotone 𝒯 Set.inter_subset_right hx
  · intro ⟨hA, hB⟩
    obtain ⟨U, hU₁, hU₂, hU₃⟩ := hA
    obtain ⟨V, hV₁, hV₂, hV₃⟩ := hB
    exists U ∩ V
    repeat' constructor
    · exact binary_inter_open h𝒯 hU₁ hV₁
    · exact hU₂
    · exact hV₂
    · exact Set.inter_subset_inter hU₃ hV₃

-- in the discrete topology, the interior of any set is itself
theorem discrete_interior (A: Set X): interior Set.univ A = A := by
  apply le_antisymm
  · apply interior_subset_self
  · intro
    apply (discrete_neighborhood_iff _ _).mpr

def adherent (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  ∀ N ∈ Nbhds 𝒯 x, Set.Nonempty (N ∩ A)

def closure (𝒯: Set (Set X)) (A: Set X): Set X :=
 {x | adherent 𝒯 A x}

-- Duality: closure(A) = interior(Aᶜ)ᶜ
-- Lets us prove results about closure in terms of interior
-- TODO: this proof is ugly!
theorem closure_eq (𝒯: Set (Set X)) (A: Set X): closure 𝒯 A = (interior 𝒯 Aᶜ)ᶜ := by
  ext
  constructor
  · intro hx
    simp_all [interior, neighborhood, interior_point]
    intro U h1 h2 h3
    have := hx U (open_neighborhood 𝒯 h2 h1)
    have: U ∩ A = ∅ := by -- this should be easier..
      ext
      constructor
      · intro ⟨hz1, hz2⟩
        exact h3 hz1 hz2
      · exact False.elim
    sorry -- contradiction
  · sorry
    -- intro hx N hN h
    -- obtain ⟨U, hU₁, hU₂, hU₃⟩ := hN
    -- simp_all [interior, neighborhood, interior_point]
    -- apply hx U hU₁ hU₂
    -- intro _ hz1 hz2
    -- have := Set.mem_inter (hU₃ hz1) hz2
    -- rw [h] at this
    -- contradiction

theorem closure_empty {𝒯: Set (Set X)} (h: IsTopology 𝒯): closure 𝒯 ∅ = ∅ := by
  simp [closure_eq, interior_univ h]

theorem closure_univ (𝒯: Set (Set X)): closure 𝒯 Set.univ = Set.univ := by
  simp [closure_eq, interior_empty]

theorem closure_compl_eq_compl_interior (𝒯: Set (Set X)) (A: Set X): closure 𝒯 Aᶜ = (interior 𝒯 A)ᶜ := by
  simp [closure_eq]

theorem compl_closure_eq_interior_compl (𝒯: Set (Set X)) (A: Set X): (closure 𝒯 A)ᶜ = interior 𝒯 Aᶜ := by
  simp [closure_eq]

theorem closure_monotone (𝒯: Set (Set X)) (A B: Set X){h:A⊆ B}: closure 𝒯 A ⊆ closure 𝒯 B := by
simp[closure, adherent]
intro x hx
intro U hU
apply hx at hU
have h1: U ∩ A ⊆ U ∩ B := by
  exact Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) h
exact Set.Nonempty.mono h1 hU

theorem closure_interior (𝒯: Set (Set X)) (A: Set X): closure 𝒯 (interior 𝒯 A) ⊆ closure 𝒯 A := by
  apply closure_monotone
  apply interior_subset_self

theorem closure_idempotent (𝒯: Set (Set X)) (A: Set X): closure 𝒯 (closure 𝒯 A) = closure 𝒯 A := by
  simp [closure_eq, interior_idempotent]

-- the closure is closed
theorem closure_closed {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A: Set X): closedset 𝒯 (closure 𝒯 A) := by
  simp [closure_eq, closedset]
  apply interior_open h𝒯

-- closure is a superset of the original
theorem closure_supset_self (𝒯: Set (Set X)) (A: Set X): A ⊆ closure 𝒯 A := by
  simp [closure_eq]
  apply Set.subset_compl_comm.mpr
  apply interior_subset_self

-- The closure of A is smallest closed supset of A
theorem closure_smallest_closed_supset {𝒯: Set (Set X)} {A U: Set X} (h1: Uᶜ ∈ 𝒯) (h2: A ⊆ U): closure 𝒯 A ⊆ U := by
  simp [closure_eq]
  have: Uᶜ ⊆ Aᶜ := Set.compl_subset_compl_of_subset h2
  have := interior_largest_open_subset h1 this
  exact Set.compl_subset_comm.mp this

theorem closure_eq_inter_closed_supsets {𝒯: Set (Set X)} {A: Set X}: closure 𝒯 A = ⋂₀ {U | Uᶜ ∈ 𝒯 ∧ A ⊆ U} := by
  simp [closure_eq]
  apply compl_inj_iff.mp
  simp
  rw [interior_eq_union_open_subsets]
  sorry

theorem closed_iff_eq_closure {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A: Set X): closedset 𝒯 A ↔ A = closure 𝒯 A := by
  simp [closure_eq, closedset]
  calc
    Aᶜ ∈ 𝒯 ↔ Aᶜ  = interior 𝒯 Aᶜ      := by apply open_iff_eq_interior h𝒯
         _ ↔ Aᶜᶜ = (interior 𝒯 Aᶜ)ᶜ   := by apply symm compl_inj_iff
         _ ↔ A   = (interior 𝒯 Aᶜ)ᶜ   := by rw [compl_compl]

-- closure (A ∪ B) = (closure A) ∪ (closure B)
theorem closure_union_eq {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A B: Set X): closure 𝒯 (A ∪ B) = closure 𝒯 A ∪ closure 𝒯 B := by
  simp [closure_eq]
  apply compl_inj_iff.mp
  simp
  apply interior_inter_eq h𝒯

-- in the discrete topology, the closure of any set is itself
theorem discrete_closure (A: Set X): closure Set.univ A = A := by
  simp [closure_eq, discrete_interior]

-- the frontier, aka boundary
def frontier_point (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  ∀ N ∈ Nbhds 𝒯 x, Set.Nonempty (N ∩ A) ∧ Set.Nonempty (N ∩ Aᶜ)

def frontier (𝒯: Set (Set X)) (A: Set X): Set X :=
  {x | frontier_point 𝒯 A x}

theorem frontier_eq (𝒯: Set (Set X)) (A: Set X): frontier 𝒯 A = closure 𝒯 A ∩ closure 𝒯 Aᶜ := by
  simp [frontier, frontier_point, closure, adherent]
  ext
  exact forall₂_and

-- the frontier of the closure is the same as the frontier
theorem frontier_closure_eq (𝒯: Set (Set X)) (A: Set X): frontier 𝒯 (closure 𝒯 A) = frontier 𝒯 A := by
  calc
    frontier 𝒯 (closure 𝒯 A) = closure 𝒯 (closure 𝒯 A) ∩ closure 𝒯 (closure 𝒯 A)ᶜ := by rw [frontier_eq]
                           _ = closure 𝒯 A ∩ closure 𝒯 (closure 𝒯 A)ᶜ := by rw [closure_idempotent]
                           _ = closure 𝒯 A ∩ closure 𝒯 (interior 𝒯 Aᶜ) := by rw [compl_closure_eq_interior_compl]
                           _ = closure 𝒯 A ∩ closure 𝒯 Aᶜ := by sorry
                           _ = frontier 𝒯 A := by rw [frontier_eq]

theorem frontier_closed (𝒯: Set (Set X)) (A: Set X): closedset 𝒯 (frontier 𝒯 A) := by
  sorry

-- TODO: is basic neighborhood worth defining?
theorem frontier_mem_iff {𝒯 ℬ: Set (Set X)} (h: base 𝒯 ℬ) (A: Set X) (x: X): x ∈ frontier 𝒯 A ↔ ∀ N ∈ Nbhds 𝒯 x ∩ ℬ, N ∩ A = ∅ ∧ N ∩ Aᶜ = ∅ := by
  sorry

theorem frontier_univ {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): frontier 𝒯 Set.univ = ∅ := by
  simp [frontier_eq, closure_empty h𝒯]

theorem frontier_empty {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): frontier 𝒯 ∅ = ∅ := by
  simp [frontier_eq, closure_empty h𝒯]

-- in a metric space, the frontier of the open ball is the sphere
theorem frontier_openball [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x: X) (r: D): frontier (metric_opensets d) (openball d x r) = sphere d x r := by
  sorry

-- in the discrete topology, the frontier of every set is empty
theorem discrete_frontier (A: Set X): frontier Set.univ A = ∅ := by
  simp [frontier_eq, discrete_closure]

def exterior_point (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  x ∈ interior 𝒯 Aᶜ

def exterior (𝒯: Set (Set X)) (A: Set X): Set X :=
  {x | exterior_point 𝒯 A x}

theorem exterior_eq (𝒯: Set (Set X)) (A: Set X): exterior 𝒯 A = (closure 𝒯 A)ᶜ := by
  simp [exterior, exterior_point, compl_closure_eq_interior_compl]

-- TODO this is clunky
-- the interior, frontier, and exterior form a disjoint union of the whole space.
theorem interior_frontier_exterior_partition (𝒯: Set (Set X)) (A: Set X):
  (interior 𝒯 A ∪ frontier 𝒯 A ∪ exterior 𝒯 A = X) ∧ (interior 𝒯 A ∩ frontier 𝒯 A = ∅) ∧ (interior 𝒯 A ∩ exterior 𝒯 A = ∅) ∧ (frontier 𝒯 A ∩ exterior 𝒯 A = ∅) := by
  repeat' constructor
  · sorry
  · sorry
  · sorry
  · sorry

-- in the discrete topology, the exterior of a set is its complement
theorem discrete_exterior (𝒯: Set (Set X)) (A: Set X): exterior Set.univ A = Aᶜ := by
  simp [exterior_eq, closure_eq, discrete_interior]

theorem closure_eq_interior_union_frontier (𝒯: Set (Set X)) (A: Set X): closure 𝒯 A = interior 𝒯 A ∪ frontier 𝒯 A := by
  sorry

theorem interior_eq_set_minus_frontier (𝒯: Set (Set X)) (A: Set X): interior 𝒯 A = A \ frontier 𝒯 A := by
  sorry





def dense (𝒯: Set (Set X)) (A: Set X): Prop :=
  ∀ U ∈ 𝒯, Set.Nonempty U → Set.Nonempty (A ∩ U)

theorem dense_univ (𝒯: Set (Set X)): dense 𝒯 Set.univ := by
  simp [dense]

theorem dense_iff_dense_in_base (𝒯 ℬ: Set (Set X)) (h: base 𝒯 ℬ) (A: Set X): dense 𝒯 A ↔ ∀ U ∈ ℬ, Set.Nonempty U → Set.Nonempty (A ∩ U) := by
  sorry

-- some theorems ? Q is dense, I is dense, is C is countable then Cᶜ is dense

theorem discrete_dense_iff (A: Set X): dense Set.univ A ↔ A = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_univ_subset
    intro x _
    simp [dense] at h
    exact Set.inter_singleton_nonempty.mp (h {x} (by exists x))
  · intro h
    rw [h]
    apply dense_univ

theorem indiscrete_dense (A: Set X): Set.Nonempty A → dense {∅, Set.univ} A := by
  intro h
  simp [dense]
  intro--
  exact h

-- theorem : dense in euclidean topology iff. dense in sorgenfry
theorem dense_iff (𝒯: Set (Set X)) (A: Set X): dense 𝒯 A ↔ closure 𝒯 A = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_univ_subset
    intro x _
    simp_all [closure, adherent, dense]
    intro N hN
    simp_all [Nbhds, neighborhood]
    obtain ⟨U, hU1, hU2, hU3⟩ := hN
    have := h U hU1 (by exists x)
    rw [Set.inter_comm]
    exact Set.Nonempty.mono (Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) hU3) this
  · intro h
    simp [dense]
    intro U hU1 hU2
    simp_all [closure, adherent]
    obtain ⟨x, hx⟩ := hU2
    have: x ∈ Set.univ := by exact trivial
    rw [←h] at this
    simp at this
    have: ∀ N ∈ Nbhds 𝒯 x, (N ∩ A).Nonempty := this
    have: U ∈ Nbhds 𝒯 x := by
      simp [Nbhds]
      exact open_neighborhood 𝒯 hx hU1
    rw [Set.inter_comm]
    (expose_names; exact this_1 U this)

theorem dense_antimono {𝒯₁ 𝒯₂: Set (Set X)} (h1: 𝒯₁ ⊆ 𝒯₂) {A: Set X} (h2: dense 𝒯₂ A): dense 𝒯₁ A := by
  intro U hU1
  exact h2 U (h1 hU1)

-- example: Z is dense in the topology generated by [a,infty)





-- fréchet and hausdorff spaces
def fréchet (𝒯: Set (Set X)): Prop :=
  ∀ x y, x ≠ y → ∃ U V, U ∈ Nbhds 𝒯 x ∧ V ∈ Nbhds 𝒯 y ∧ x ∉ V ∧ y ∉ U

-- a family 𝒯 is hausdorff (aka T2) if every pair of distinct points have disjoint neighborhoods.
def hausdorff (𝒯: Set (Set X)): Prop :=
  ∀ x y, x ≠ y → ∃ U V, U ∈ Nbhds 𝒯 x ∧ V ∈ Nbhds 𝒯 y ∧ Disjoint U V

theorem fréchet_implies_hausdorff (𝒯: Set (Set X)): hausdorff 𝒯 → fréchet 𝒯 := by
  intro h x y h1
  obtain ⟨U, V, hU1, hV1, h2⟩ := h x y h1
  exists U, V
  repeat' (apply And.intro)
  · exact hU1
  · exact hV1
  · exact Disjoint.notMem_of_mem_left h2 (neighborhood_mem hU1)
  · exact Disjoint.notMem_of_mem_left (id (Disjoint.symm h2)) (neighborhood_mem hV1)

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
theorem sierpiński_nonhausdorff: ¬hausdorff (sierpiński_topology.opensets) := by
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

-- If r > 0 then B(x, r) is a neighborhood of x. TODO: move somewhere else
theorem openball_neighborhood [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x: X) {r: D} (hr: 0 < r): neighborhood (metric_opensets d) (openball d x r) x := by
  exists (openball d x r)
  sorry
  -- repeat' constructor
  -- · exact openball_open hd x r
  -- · sorry -- exact?-- (openball_mem_iff hd x).mpr hr
  -- · sorry -- exact?

-- simple lemma: if balls are too far apart, their intersection is empty.
lemma separated_balls [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) {x1 x2: X} {r1 r2: D} (h: r1 + r2 ≤ d x1 x2): Disjoint (openball d x1 r1) (openball d x2 r2) := by
  apply Set.disjoint_iff.mpr
  intro x ⟨hx1, hx2⟩
  apply not_lt_of_ge h
  calc
    d x1 x2 ≤ d x1 x + d x x2 := by exact hd.triangle x1 x x2
          _ = d x1 x + d x2 x := by rw [hd.symmetric x x2]
          _ < r1 + r2 := by sorry -- exact? -- add_lt_add hx1 hx2

-- Every metric space is hausdorff.
-- Proof: given two distinct points x, y, let r = d(x, y) / 2. Then B(x, r) and B(y, r) are disjoint neighborhoods.
theorem metric_space_hausdorff {d: X → X → ENNReal} (hd: IsMetric d): hausdorff (metric_opensets d) := by
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
theorem nonhausdorff_nonmetrizable {𝒯: Topology X} (h: ¬ hausdorff 𝒯.opensets): ¬ metrizable 𝒯 ENNReal := by
  intro ⟨d, hd⟩
  rw [←hd] at h
  exact h (metric_space_hausdorff d.is_metric)

-- corollary: sierpiński space is nonmetrizable!
theorem sierpiński_nonmetrizable: ¬ metrizable sierpiński_topology ENNReal := by
  exact nonhausdorff_nonmetrizable sierpiński_nonhausdorff

-- TODO
-- show the cofinite topology is Frechet but not Hausdorff
-- the antidiscrete space is not frechte
-- Let O1, O2 be topologies. If O1 ⊆ O2 then O1 (Hausdorff/Frechet) implies O2 (Hausdorff/Frechet)

theorem frechet_iff (𝒯: Set (Set X)): fréchet 𝒯 ↔ ∀ x, closedset 𝒯 {x} := by
  sorry

-- show topology generated by [a, infty) is Frechet but not Hausdorff
-- we can call this the LCRI topology (left closed right infinite) or maybe just OI
def LCRI_base: Set (Set ENNReal) :=
  ⋃ (a: ENNReal), {Set.Ici a}

theorem LCRI_base_is_base: is_base LCRI_base := by
  sorry

theorem frechet_iff' (T: Set (Set X)): fréchet T ↔ ∀ x, {x} = Set.sInter (Nbhds T x) := by
  sorry





def subspace_topology (T: Set (Set X)) (A: Set X): Set (Set X) :=
  {A ∩ U | U ∈ T}

theorem subspace_topology_is_topology (T: Set (Set X)) (A: Set X) (hT: IsTopology T): IsTopology (subspace_topology T A) := by
  sorry

-- basis of a subspace

-- properties of topologies of metric spaces

-- product topology

-- equivalence of metrics

-- diagonal is closed iff hausdorff
def diagonal (X: Type*): Set (X × X) :=
  Set.image (fun x => (x, x)) Set.univ

theorem hausdorff_iff_diagonal_closed (T: Set (Set (X × X))): hausdorff T ↔ closedset T (diagonal X) := by
  sorry





-- continuity
def continuous_at (TX: Set (Set X)) (TY: Set (Set Y)) (f: X → Y) (x: X): Prop :=
  ∀ N' ∈ Nbhds TY (f x), ∃ N ∈ Nbhds TX x, f '' N ⊆ N'

def continuous (TX: Set (Set X)) (TY: Set (Set Y)) (f: X → Y): Prop :=
  ∀ x, continuous_at TX TY f x

def continuous_iff_open_preimage_open (TX: Set (Set X)) (TY: Set (Set Y)) (f: X → Y): continuous TX TY f ↔ ∀ V ∈ TY, Set.preimage f V ∈ TX := by
  sorry

def continuous_iff_closed_preimage_closed (TX: Set (Set X)) (TY: Set (Set Y)) (f: X → Y): continuous TX TY f ↔ ∀ F ∈ closedsets TY, Set.preimage f F ∈ closedsets TX := by
  sorry

def continuous_iff_image_closure_subseteq_closure_image (TX: Set (Set X)) (TY: Set (Set Y)) (f: X → Y): continuous TX TY f ↔ ∀ A: Set X, Set.image f (closure TX A) ⊆ closure TY (Set.image f A) := by
  sorry





noncomputable def Function.Inverse {f: X → Y} (h: Function.Bijective f): Y → X :=
  Classical.choose (Function.bijective_iff_has_inverse.mp h)

-- homeomorphisms
structure homeomorphism (TX: Set (Set X)) (TY: Set (Set Y)) (f: X → Y): Prop where
  bijection: Function.Bijective f
  continuous_forward: continuous TX TY f
  continuous_inverse: continuous TY TX (Function.Inverse bijection)

def homeomorphic (TX: Set (Set X)) (TY: Set (Set Y)): Prop :=
  ∃ f, homeomorphism TX TY f

-- this definition doesn't care about underlying type of points
def homeomorphic_spaces (X Y: TopologicalSpace): Prop :=
  ∃ f: X.points → Y.points, homeomorphism X.topology.opensets Y.topology.opensets f

-- a property is called a topological property if it's preserved under homeomorphism
def topological_property (P: TopologicalSpace → Prop): Prop :=
  ∀ X Y: TopologicalSpace, homeomorphic_spaces X Y → P X → P Y

def connected (T: Set (Set X)): Prop :=
  ∀ U V: Set X, U ∈ T → V ∈ T → U.Nonempty → V.Nonempty → U ∪ V = Set.univ → (U ∩ V).Nonempty

def connected_space (X: TopologicalSpace): Prop :=
  connected X.topology.opensets

-- connectedness is a topological property
theorem connected_topological_property: topological_property connected_space := by
  intro X Y h hX U V hU1 hV1 hU2 hV2 hUV
  sorry -- lol

-- let f: X → Y be a homeomorphism. Then f induces a homeomorphism X \ A -> Y \ f(A)





-- limit of a sequence in terms of the tail
def tail (x: Nat → X) (t: Nat): Nat → X :=
  fun n => x (t + n)

def converges (T: Set (Set X)) (x: Nat → X) (l: X): Prop :=
  ∀ N ∈ Nbhds T l, ∃ t: Nat, Set.range (tail x t) ⊆ N

def convergent (T: Set (Set X)) (x: Nat → X): Prop :=
  ∃ l, converges T x l

def converges_distance [DistanceSpaceStruct D] (d: X → X → D) (x: Nat → X) (l: X): Prop :=
  ∀ r, ⊥ < r → ∃ t, Set.range (tail x t) ⊆ openball d l r

def convergent_distance [DistanceSpaceStruct D] (d: X → X → D) (x: Nat → X): Prop :=
  ∃ l, converges_distance d x l

-- equivalent definition in a metric space
theorem limit_metric_iff [DistanceSpace D] (d: X → X → D) (x: Nat → X) (l: X): converges (metric_opensets d) x l ↔ converges_distance d x l := by
  sorry

def adherent_value (T: Set (Set X)) (x: Nat → X) (a: X): Prop :=
  ∀ N ∈ Nbhds T a, ∀ t, (Set.range (tail x t) ∩ N).Nonempty

-- defn of a subsequence

-- a is adherent iff exists subsequence converging to a

-- limits are unique in a hausdorff space
theorem hausdorff_limit_unique (T: Set (Set X)) (h: hausdorff T) (x: Nat → X) (l1 l2: X) (h1: converges T x l1) (h2: converges T x l2): l1 = l2 := by
  sorry

-- prop: adherent points preserved by sequences

-- the set of adherent values are closed

-- defn of countable/denumerable set





-- diameter of a set
noncomputable def diameter [CompleteDistanceSpace D] (d: X → X → D) (A: Set X): D :=
  sSup (⋃ (a ∈ A) (b ∈ A), {d a b})

theorem diameter_monotone [CompleteDistanceSpace D] (d: X → X → D) {A B: Set X} (h: A ⊆ B): diameter d A ≤ diameter d B := by
  sorry

theorem diameter_singleton [CompleteDistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x: X): diameter d {x} = 0 := by
  simp [diameter, hd.dist_self_bot x]

example [CompleteDistanceSpace D] (d: X → X → D): diameter d ∅ = 0 := by
  simp [diameter]

example [CompleteDistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x y: X): diameter d {x, y} = d x y := by
  simp [diameter]
  sorry

example [CompleteDistanceSpace D] (d: X → X → D) (hd: IsMetric d) (x: X) (r: D): diameter d (openball d x r) ≤ 2 • r := by
  simp [diameter]
  intros
  have := hd.triangle
  sorry

-- a set is bounded if it has finite diameter.
def bounded [CompleteDistanceSpace D] (d: X → X → D) (A: Set X): Prop :=
  diameter d A < ⊤

-- a set is boudned iff. it is contained in a ball of finite radius.
-- maybe closed ball easier.
theorem bounded_iff [CompleteDistanceSpace D] (d: X → X → D) (A: Set X): bounded d A ↔ ∃ x r, r < ⊤ ∧ A ⊆ openball d x r := by
  sorry

theorem bounded_subset [CompleteDistanceSpace D] (d: X → X → D) {A B: Set X} (h1: A ⊆ B) (h2: bounded d B): bounded d A := by
  exact lt_of_le_of_lt (diameter_monotone _ h1) h2

-- TODO if a finite family is all bounded their union is bounded.
theorem bounded_finite_union [CompleteDistanceSpace D] (d: X → X → D) (F: Set (Set X)) (h1: Finite F) (h2: ∀ A ∈ F, bounded d A): bounded d (⋃₀ F) := by
  sorry

def totally_bounded [CompleteDistanceSpace D] (d: X → X → D) (A: Set X): Prop :=
  ∀ ε, ⊥ < ε → ∃ C: Set X, Finite C ∧ A ⊆ ⋃ (x ∈ C), openball d x ε

theorem totally_bounded_bounded [CompleteDistanceSpace D] {d: X → X → D} {A: Set X} (h: totally_bounded d A): bounded d A := by
  sorry





-- cauchy sequence in terms of diameters of tails
def cauchy [DistanceSpaceStruct D] (d: X → X → D) (x: Nat → X): Prop :=
  ∀ ε, ⊥ < ε → ∃ t, ∀ m n, t ≤ m → t ≤ n → d (x m) (x n) < ε

def cauchy_sequence_diameter [CompleteDistanceSpace D] (d: X → X → D) (x: Nat → X): cauchy d x ↔ ∀ r, ⊥ < r → ∃ t, diameter d (Set.range (tail x t)) < r := by
  sorry

theorem convergent_cauchy [DistanceSpaceStruct D] {d: X → X → D} {x: Nat → X} (h: convergent_distance d x): cauchy d x := by
  sorry

example [DistanceSpace D] {d: X → X → D} {x: Nat → X} {a: X} (h1: cauchy d x) (h2: adherent_value (metric_opensets d) x a): converges_distance d x a := by
  sorry

def complete [DistanceSpaceStruct D] (d: X → X → D): Prop :=
  ∀ x, cauchy d x → convergent_distance d x

-- If A ⊆ X is complete then it is closed.
-- todo : use subspace metric?
example [DistanceSpaceStruct D] (d: X → X → D) (A: Set X) (h: complete (fun (a b: A) => d a b)): metric_closedset d A := by
  sorry

example [DistanceSpaceStruct D] (d: X → X → D) (A: Set X) (h1: complete d) (h2: metric_closedset d A): complete (fun (a b: A) => d a b) := by
  sorry

-- If two metrics are uniformly equivalent, then Cauchy iff Cauchy.
-- Hence complete iff complete.

-- If dX, dY complete then dX x dY (the product metric given by max) is complete

structure Completion [DistanceSpace D] {X0 X1: Type*} (d0: X0 → X0 → D) (d1: X1 → X1 → D) (i: X0 → X1): Prop where
  isometry: isometry d0 d1 i
  dense: dense (metric_opensets d1) (Set.range i)
  complete: complete d1

-- Appendix TODO move
-- given a metric space, extend to disctance on sets

noncomputable def distance_point_set [CompleteDistanceSpace D] (d: X → X → D) (a: X) (B: Set X): D :=
  sInf (⋃ (b ∈ B), {d a b})

noncomputable def distance_set_point [CompleteDistanceSpace D] (d: X → X → D) (A: Set X) (b: X): D :=
  sInf (⋃ (a ∈ A), {d a b})

noncomputable def set_dist [CompleteDistanceSpace D] (d: X → X → D) (A B: Set X): D :=
  sInf (⋃ (a ∈ A) (b ∈ B), {d a b})

-- noncomputable def hausdorff_dist (d: X → X → D) (A B: Set X): D :=
--   max (sSup ⋃ (x: )) ()


-- structure IsPseudoExtendedMetric (d: X → X → D): Prop where
--   eq: ∀ x, d x x = 0
--   symm: ∀ x y, d x y = d y x
--   triangle: ∀ x y z, d x z ≤ d x y + d y z

-- example (d: X → X → D): IsMetric (set_dist d) := {
--   eq_iff := sorry -- fails
--   symm := by
--     intro A B
--     simp [set_dist]
--     sorry
--   triangle := by
--     sorry
-- }
