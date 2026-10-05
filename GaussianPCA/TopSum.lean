import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp

/-!
# Finite top-coordinate sums

`topSum d a` is the largest sum over subsets of at most `d` coordinates.
For nonnegative coordinates and `d ≤ n` this is the usual sum of the largest
`d` coordinates. The definition is meaningful without either restriction.
-/

noncomputable section
open scoped BigOperators

namespace GaussianPCA

variable {n : ℕ}

/-- All coordinate subsets satisfying the uniform capacity constraint. -/
def admissibleSets (n d : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter (fun S => S.card ≤ d)

@[simp] theorem mem_admissibleSets {d : ℕ} {S : Finset (Fin n)} :
    S ∈ admissibleSets n d ↔ S.card ≤ d := by
  simp [admissibleSets]

theorem admissibleSets_nonempty (n d : ℕ) : (admissibleSets n d).Nonempty :=
  ⟨∅, by simp⟩

/-- The sum of the largest positive coordinates, up to capacity `d`. -/
def topSum (d : ℕ) (a : Fin n → ℝ) : ℝ :=
  (admissibleSets n d).sup' (admissibleSets_nonempty n d) (fun S => ∑ i ∈ S, a i)

/-- Every feasible coordinate set is bounded by the optimum. -/
theorem sum_le_topSum (d : ℕ) (a : Fin n → ℝ) (S : Finset (Fin n))
    (hS : S.card ≤ d) : (∑ i ∈ S, a i) ≤ topSum d a :=
  Finset.le_sup' (fun S => ∑ i ∈ S, a i) (mem_admissibleSets.mpr hS)

/-- To upper bound a top sum it suffices to bound all feasible subsets. -/
theorem topSum_le (d : ℕ) (a : Fin n → ℝ) {b : ℝ}
    (h : ∀ S : Finset (Fin n), S.card ≤ d → (∑ i ∈ S, a i) ≤ b) :
    topSum d a ≤ b :=
  Finset.sup'_le _ _ (fun S hS => h S (mem_admissibleSets.mp hS))

theorem topSum_nonneg (d : ℕ) (a : Fin n → ℝ) : 0 ≤ topSum d a := by
  simpa using sum_le_topSum d a ∅ (by simp)

/-- A maximizing finite subset always exists. -/
theorem exists_topSum_set (d : ℕ) (a : Fin n → ℝ) :
    ∃ S : Finset (Fin n), S.card ≤ d ∧ (∑ i ∈ S, a i) = topSum d a := by
  obtain ⟨S, hS, hEq⟩ :=
    Finset.exists_mem_eq_sup' (admissibleSets_nonempty n d) (fun S => ∑ i ∈ S, a i)
  exact ⟨S, mem_admissibleSets.mp hS, hEq.symm⟩

/-- For nonnegative input and `d ≤ n`, there is an optimizer of cardinality
exactly `d`, proving agreement with the paper's exact-cardinality definition. -/
theorem exists_topSum_set_card_eq (d : ℕ) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hd : d ≤ n) :
    ∃ S : Finset (Fin n), S.card = d ∧ (∑ i ∈ S, a i) = topSum d a := by
  obtain ⟨S, hS, hmax⟩ := exists_topSum_set d a
  obtain ⟨T, hST, _, hT⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ S) hS (by simpa using hd)
  refine ⟨T, hT, le_antisymm (sum_le_topSum d a T hT.le) ?_⟩
  rw [← hmax]
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun i _ _ => ha i)

/-- The top sum is monotone in every coordinate. -/
theorem topSum_mono (d : ℕ) {a b : Fin n → ℝ} (h : ∀ i, a i ≤ b i) :
    topSum d a ≤ topSum d b := by
  apply topSum_le
  intro S hS
  exact (Finset.sum_le_sum (fun i _ => h i)).trans (sum_le_topSum d b S hS)

@[simp] theorem topSum_zero (d : ℕ) : topSum (n := n) d (fun _ => 0) = 0 := by
  apply le_antisymm _ (topSum_nonneg _ _)
  apply topSum_le
  simp

@[simp] theorem topSum_zero_capacity (a : Fin n → ℝ) : topSum 0 a = 0 := by
  apply le_antisymm _ (topSum_nonneg _ _)
  apply topSum_le
  intro S hS
  have hzero : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hS)
  simp [hzero]

/-- Every selected coordinate of a maximizing set is nonnegative. -/
theorem topSum_set_nonneg (d : ℕ) (a : Fin n → ℝ) (S : Finset (Fin n))
    (hS : S.card ≤ d) (hmax : (∑ i ∈ S, a i) = topSum d a)
    {i : Fin n} (hi : i ∈ S) : 0 ≤ a i := by
  have h := sum_le_topSum d a (S.erase i) ((Finset.card_erase_le).trans hS)
  rw [← hmax] at h
  have heq := Finset.sum_erase_add S a hi
  linarith

/-- Exchanging a selected and an unselected coordinate cannot improve a maximum. -/
theorem topSum_set_exchange (d : ℕ) (a : Fin n → ℝ) (S : Finset (Fin n))
    (hS : S.card ≤ d) (hmax : (∑ i ∈ S, a i) = topSum d a)
    {i j : Fin n} (hi : i ∈ S) (hj : j ∉ S) : a j ≤ a i := by
  have hj' : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
  have hcard : (insert j (S.erase i)).card ≤ d := by
    rw [Finset.card_insert_of_notMem hj', Finset.card_erase_of_mem hi]
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have h := sum_le_topSum d a (insert j (S.erase i)) hcard
  rw [Finset.sum_insert hj', ← hmax] at h
  have heq := Finset.sum_erase_add S a hi
  linarith

/-- If a maximum does not fill capacity, every omitted coordinate is nonpositive. -/
theorem topSum_set_unselected_nonpos (d : ℕ) (a : Fin n → ℝ)
    (S : Finset (Fin n)) (hmax : (∑ i ∈ S, a i) = topSum d a)
    (hcard : S.card < d) {j : Fin n} (hj : j ∉ S) : a j ≤ 0 := by
  have h := sum_le_topSum d a (insert j S) (by
    rw [Finset.card_insert_of_notMem hj]
    omega)
  rw [Finset.sum_insert hj, ← hmax] at h
  linarith

/-- Each nonnegative threshold gives an upper bound on the retained sum. -/
theorem topSum_le_threshold (d : ℕ) (a : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    topSum d a ≤ (d : ℝ) * τ + ∑ i, max (a i - τ) 0 := by
  apply topSum_le
  intro S hS
  calc
    (∑ i ∈ S, a i) = (S.card : ℝ) * τ + ∑ i ∈ S, (a i - τ) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      linarith
    _ ≤ (d : ℝ) * τ + ∑ i ∈ S, max (a i - τ) 0 :=
      add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hS) hτ)
        (Finset.sum_le_sum (fun _ _ => le_max_left _ _))
    _ ≤ (d : ℝ) * τ + ∑ i, max (a i - τ) 0 :=
      add_le_add_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun _ _ _ => le_max_right _ _)) _

/-- The top sum is bounded by the total sum when all coordinates are nonnegative. -/
theorem topSum_le_sum (d : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    topSum d a ≤ ∑ i, a i := by
  have h := topSum_le_threshold d a (τ := 0) le_rfl
  simpa [max_eq_left, ha] using h

/-- A uniform integrable majorant, valid without a sign assumption. -/
theorem topSum_le_sum_abs (d : ℕ) (a : Fin n → ℝ) :
    topSum d a ≤ ∑ i, |a i| := by
  exact (topSum_mono d (fun i => le_abs_self (a i))).trans
    (topSum_le_sum d (fun i => |a i|) (fun _ => abs_nonneg _))

theorem abs_topSum_le_sum_abs (d : ℕ) (a : Fin n → ℝ) :
    |topSum d a| ≤ ∑ i, |a i| := by
  rw [abs_of_nonneg (topSum_nonneg d a)]
  exact topSum_le_sum_abs d a

/-- With at most `d` nonzero coordinates, all nonnegative energy is retained. -/
theorem topSum_eq_sum_of_support_card_le (d : ℕ) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hc : (Finset.univ.filter (fun i => a i ≠ 0)).card ≤ d) :
    topSum d a = ∑ i, a i := by
  apply le_antisymm (topSum_le_sum d a ha)
  have h := sum_le_topSum d a (Finset.univ.filter (fun i => a i ≠ 0)) hc
  rw [Finset.sum_filter_ne_zero] at h
  exact h

/-- A nonnegative vector has the ordinary full sum once all coordinates fit. -/
theorem topSum_eq_sum (d : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hd : n ≤ d) :
    topSum d a = ∑ i, a i := by
  apply le_antisymm (topSum_le_sum d a ha)
  exact sum_le_topSum d a Finset.univ (by simpa using hd)

/-- The selected level set in any maximum has exactly the truncated full count. -/
theorem topSum_set_level_card (d : ℕ) (a : Fin n → ℝ) (S : Finset (Fin n))
    (hS : S.card ≤ d) (hmax : (∑ i ∈ S, a i) = topSum d a)
    {t : ℝ} (ht : 0 ≤ t) :
    (S.filter (fun i => t < a i)).card =
      min d (Finset.univ.filter (fun i => t < a i)).card := by
  classical
  by_cases hsub : ∀ j, t < a j → j ∈ S
  · have heq : S.filter (fun i => t < a i) =
        Finset.univ.filter (fun i => t < a i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.right, fun h => ⟨hsub i h, h⟩⟩
    have hcard : (Finset.univ.filter (fun i => t < a i)).card ≤ d := by
      rw [← heq]
      exact (Finset.card_filter_le _ _).trans hS
    rw [heq, min_eq_right hcard]
  · push_neg at hsub
    obtain ⟨j, hjt, hjS⟩ := hsub
    have hselected : ∀ i ∈ S, t < a i := by
      intro i hi
      exact lt_of_lt_of_le hjt (topSum_set_exchange d a S hS hmax hi hjS)
    have hfull : S.card = d := by
      by_contra hne
      have hlt : S.card < d := lt_of_le_of_ne hS hne
      have hnonpos := topSum_set_unselected_nonpos d a S hmax hlt hjS
      linarith
    have heq : S.filter (fun i => t < a i) = S := Finset.filter_eq_self.mpr hselected
    have hcard : d ≤ (Finset.univ.filter (fun i => t < a i)).card := by
      rw [← hfull]
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hselected i hi
    rw [heq, hfull, min_eq_left hcard]

private theorem sum_max_sub_eq (a : Fin n → ℝ) (S : Finset (Fin n)) (τ : ℝ)
    (hin : ∀ i ∈ S, τ ≤ a i) (hout : ∀ i ∉ S, a i ≤ τ) :
    (∑ i, max (a i - τ) 0) = (∑ i ∈ S, a i) - (S.card : ℝ) * τ := by
  calc
    (∑ i, max (a i - τ) 0) = ∑ i ∈ S, max (a i - τ) 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      exact max_eq_right (sub_nonpos.mpr (hout i hi))
    _ = ∑ i ∈ S, (a i - τ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact max_eq_left (sub_nonneg.mpr (hin i hi))
    _ = _ := by simp [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

/-- A deterministic nonnegative threshold attains the top-sum relaxation. -/
theorem exists_topSum_threshold (d : ℕ) (a : Fin n → ℝ) (hd : 0 < d) :
    ∃ τ : ℝ, 0 ≤ τ ∧
      topSum d a = (d : ℝ) * τ + ∑ i, max (a i - τ) 0 := by
  classical
  obtain ⟨S, hS, hmax⟩ := exists_topSum_set d a
  by_cases hlt : S.card < d
  · refine ⟨0, le_rfl, ?_⟩
    rw [sum_max_sub_eq a S 0
      (fun i hi => topSum_set_nonneg d a S hS hmax hi)
      (fun i hi => topSum_set_unselected_nonpos d a S hmax hlt hi)]
    simpa using hmax.symm
  · have hfull : S.card = d := by omega
    have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image S a hnonempty
    refine ⟨a i, topSum_set_nonneg d a S hS hmax hi, ?_⟩
    rw [sum_max_sub_eq a S (a i) hmin
      (fun j hj => topSum_set_exchange d a S hS hmax hi hj), hfull]
    linarith

/-- **Paper Lemma 3.** The threshold variational identity, in an equivalent
capacity formulation that also permits negative coordinates. -/
theorem topSum_eq_sInf_threshold (d : ℕ) (a : Fin n → ℝ) (hd : 0 < d) :
    topSum d a = sInf {b : ℝ | ∃ τ : ℝ, 0 ≤ τ ∧
      b = (d : ℝ) * τ + ∑ i, max (a i - τ) 0} := by
  obtain ⟨τ, hτ, hEq⟩ := exists_topSum_threshold d a hd
  have hmem : topSum d a ∈ {b : ℝ | ∃ τ : ℝ, 0 ≤ τ ∧
      b = (d : ℝ) * τ + ∑ i, max (a i - τ) 0} := ⟨τ, hτ, hEq⟩
  have hbound : ∀ b ∈ {b : ℝ | ∃ τ : ℝ, 0 ≤ τ ∧
      b = (d : ℝ) * τ + ∑ i, max (a i - τ) 0}, topSum d a ≤ b := by
    rintro b ⟨t, ht, rfl⟩
    exact topSum_le_threshold d a ht
  exact le_antisymm (le_csInf ⟨_, hmem⟩ hbound)
    (csInf_le ⟨_, hbound⟩ hmem)

/-- Finite top-coordinate sums depend continuously on their coordinates. -/
theorem continuous_topSum (d : ℕ) : Continuous (topSum (n := n) d) := by
  unfold topSum
  apply Continuous.finset_sup'_apply
  intro S _
  fun_prop

end GaussianPCA
