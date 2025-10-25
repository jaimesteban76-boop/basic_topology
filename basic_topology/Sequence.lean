import basic_topology.Separation
import basic_topology.MetricTopology

variable {X Y D: Type*}

-- limit of a sequence in terms of the tail
def tail (x: Nat → X) (t: Nat): Nat → X :=
  fun n => x (t + n)

def converges (T: Set (Set X)) (x: Nat → X) (l: X): Prop :=
  ∀ N ∈ Nbhds T l, ∃ t, Set.range (tail x t) ⊆ N

def convergent (T: Set (Set X)) (x: Nat → X): Prop :=
  ∃ l, converges T x l

def converges_distance [DistanceSpaceStruct D] (d: X → X → D) (x: Nat → X) (l: X): Prop :=
  ∀ r, ⊥ < r → ∃ t, Set.range (tail x t) ⊆ openball d l r

def convergent_distance [DistanceSpaceStruct D] (d: X → X → D) (x: Nat → X): Prop :=
  ∃ l, converges_distance d x l

-- equivalent definition in a metric space
theorem converges_distance_iff [DistanceSpace D] (d: X → X → D) (hd: IsMetric d)(x: Nat → X) (l: X): converges (metric_opensets d) x l ↔ converges_distance d x l := by
  constructor
  · intro h r hr
    let N := openball d l r
    have h1: N ∈ Nbhds (metric_opensets d) l := by
      apply openball_neighborhood
      exact hd
      exact hr
    apply h
    exact h1
  · intro h
    simp [converges]
    intro N hN
    simp[converges_distance] at h
    simp[Nbhds,neighborhood, metric_opensets,metric_openset] at hN
    obtain ⟨ U,hU⟩ := hN
    have h3: ∃r>0, openball d l r ⊆ U := by
      apply hU.left
      exact hU.right.left
    obtain ⟨ R,hR⟩ := h3
    have: R>0 := by
      exact hR.left
    apply h at this
    obtain ⟨ t,ht⟩ := this
    use t
    intro x hx
    apply hU.2.2
    apply hR.2
    apply ht
    exact hx

def adherent_value (T: Set (Set X)) (x: Nat → X) (a: X): Prop :=
  ∀ N ∈ Nbhds T a, ∀ t, (Set.range (tail x t) ∩ N).Nonempty

-- defn of a subsequence

-- a is adherent iff exists subsequence converging to a

-- limits are unique in a hausdorff space
theorem hausdorff_limit_unique_sequences (T: Set (Set X)) (h: hausdorff T) (x: Nat → X) (l1 l2: X) (h1: converges T x l1) (h2: converges T x l2): l1 = l2 := by
  by_contra h3
  simp[converges] at h1
  simp[converges] at h2
  simp[hausdorff] at h
  apply h at h3
  obtain ⟨U,hu⟩ := h3
  obtain ⟨ V,hv⟩ := hu.right
  let hu1 := hu.left
  apply h1 at hu1
  let hv1 := hv.left
  apply h2 at hv1
  obtain ⟨ t1,ht1⟩ := hu1
  obtain ⟨ t2,ht2⟩ := hv1
  set t := max t1 t2
  have htu: Set.range (tail x t)⊆ Set.range (tail x t1) := by
    intro y hy
    simp[Set.range]
    simp [Set.range] at hy
    obtain ⟨ y1,hy1⟩ := hy
    rw[tail] at hy1
    simp[tail]
    have: ∃m, t=m+ t1 := by
      refine Nat.exists_eq_add_of_le' ?_
      exact Nat.le_max_left t1 t2
    obtain ⟨ m,hm⟩ := this
    use m+y1
    rw[ Eq.symm (Nat.add_assoc t1 m y1)]
    rw[Nat.add_comm t1 m]
    rw[← hm]
    exact hy1
  have htv: Set.range (tail x t)⊆ Set.range (tail x t2) := by
    intro y hy
    simp[Set.range]
    simp [Set.range] at hy
    obtain ⟨ y1,hy1⟩ := hy
    rw[tail] at hy1
    simp[tail]
    have: ∃m, t=m+ t2 := by
      refine Nat.exists_eq_add_of_le' ?_
      exact Nat.le_max_right t1 t2
    obtain ⟨ m,hm⟩ := this
    use m+y1
    rw[ Eq.symm (Nat.add_assoc t2 m y1)]
    rw[Nat.add_comm t2 m]
    rw[← hm]
    exact hy1
  have hu1: Set.range ( tail x t ) ⊆ U := by exact fun ⦃a⦄ a_1 ↦ ht1 (htu a_1)
  have hv1: Set.range ( tail x t ) ⊆ V := by exact fun ⦃a⦄ a_1 ↦ ht2 (htv a_1)
  have huv1: ¬ (Disjoint U V) := by
    refine Set.not_disjoint_iff.mpr ?_
    use x (t+1)
    constructor
    apply hu1
    simp [Set.range, tail ]
    apply hv1
    simp [Set.range, tail ]
  tauto


-- prop: adherent points preserved by sequences

-- the set of adherent values are closed

-- defn of countable/denumerable set
