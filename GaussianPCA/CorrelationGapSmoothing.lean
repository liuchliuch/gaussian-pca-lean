import GaussianPCA.CorrelationGapFinite
import Mathlib.Topology.Order.Compact

open scoped BigOperators
open Finset Set

noncomputable section

namespace GaussianPCA

/-- Replace two coordinates by their arithmetic mean. -/
def pairAverage {ι : Type*} [DecidableEq ι] (q : ι → ℝ) (i j : ι) : ι → ℝ :=
  Function.update (Function.update q i ((q i + q j) / 2)) j ((q i + q j) / 2)

@[simp] theorem pairAverage_left {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    pairAverage q i j i = (q i + q j) / 2 := by
  simp [pairAverage, hij]

@[simp] theorem pairAverage_right {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) (i j : ι) : pairAverage q i j j = (q i + q j) / 2 := by
  simp [pairAverage]

theorem pairAverage_other {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) {i j k : ι} (hki : k ≠ i) (hkj : k ≠ j) :
    pairAverage q i j k = q k := by simp [pairAverage, hki, hkj]

theorem pairAverage_mem_Icc {ι : Type*} [DecidableEq ι]
    {q : ι → ℝ} (hq : q ∈ Set.Icc 0 1) (i j : ι) :
    pairAverage q i j ∈ Set.Icc 0 1 := by
  have hi0 : 0 ≤ q i := hq.1 i
  have hj0 : 0 ≤ q j := hq.1 j
  have hi1 : q i ≤ 1 := hq.2 i
  have hj1 : q j ≤ 1 := hq.2 j
  constructor
  · intro k
    change 0 ≤ pairAverage q i j k
    by_cases hkj : k = j
    · subst k; simp only [pairAverage_right]; linarith
    · by_cases hki : k = i
      · subst k; simp [pairAverage, hkj]; linarith
      · rw [pairAverage_other q hki hkj]; exact hq.1 k
  · intro k
    change pairAverage q i j k ≤ 1
    by_cases hkj : k = j
    · subst k; simp only [pairAverage_right]; linarith
    · by_cases hki : k = i
      · subst k; simp [pairAverage, hkj]; linarith
      · rw [pairAverage_other q hki hkj]; exact hq.2 k

theorem sum_update_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (i : ι) (a : ℝ) :
    ∑ k, Function.update q i a k = (∑ k, q k) - q i + a := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i) q]
  ring

theorem sum_pairAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    ∑ k, pairAverage q i j k = ∑ k, q k := by
  unfold pairAverage
  rw [sum_update_univ, sum_update_univ]
  simp only [Function.update_of_ne hij.symm]
  ring

theorem sum_sq_pairAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    ∑ k, (pairAverage q i j k)^2 =
      (∑ k, (q k)^2) - (q i - q j)^2 / 2 := by
  have hu : (fun k => (pairAverage q i j k)^2) =
      Function.update (Function.update (fun k => (q k)^2) i (((q i + q j)/2)^2))
        j (((q i + q j)/2)^2) := by
    funext k
    by_cases hki : k = i
    · subst k; simp [pairAverage, hij]
    · by_cases hkj : k = j
      · subst k; simp [pairAverage]
      · simp [pairAverage, hki, hkj]
  rw [hu, sum_update_univ, sum_update_univ]
  simp only [Function.update_of_ne hij.symm]
  ring

/-- A continuous function on a cube that cannot increase under averaging two
coordinates is minimized, on each fixed-sum slice, at the constant vector.
The secondary minimization of the squared norm handles non-strict concavity. -/
theorem diagonal_le_of_pairAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (F : (ι → ℝ) → ℝ) (hF : Continuous F)
    (havg : ∀ q ∈ Set.Icc (0 : ι → ℝ) 1, ∀ i j, i ≠ j →
      F (pairAverage q i j) ≤ F q)
    {q : ι → ℝ} (hq : q ∈ Set.Icc 0 1) {p : ℝ}
    (hsum : ∑ i, q i = Fintype.card ι * p) : F (fun _ => p) ≤ F q := by
  let K : Set (ι → ℝ) := Set.Icc 0 1 ∩ {x | ∑ i, x i = ∑ i, q i}
  have hK : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)
  have hqK : q ∈ K := ⟨hq, rfl⟩
  obtain ⟨x, hxK, hx⟩ := hK.exists_isMinOn ⟨q, hqK⟩ hF.continuousOn
  let L : Set (ι → ℝ) := K ∩ {y | F y = F x}
  have hL : IsCompact L := hK.inter_right (isClosed_eq hF continuous_const)
  obtain ⟨y, hyL, hy⟩ := hL.exists_isMinOn ⟨x, hxK, rfl⟩
    (show ContinuousOn (fun z : ι → ℝ => ∑ i, (z i)^2) L from
      (by fun_prop : Continuous (fun z : ι → ℝ => ∑ i, (z i)^2)).continuousOn)
  have hyK : y ∈ K := hyL.1
  have hymin : ∀ z ∈ K, F y ≤ F z := by
    intro z hz
    rw [hyL.2]
    exact hx hz
  have hequal : ∀ i j, y i = y j := by
    intro i j
    by_contra hne
    have hij : i ≠ j := fun h => hne (congrArg y h)
    let z := pairAverage y i j
    have hzK : z ∈ K := ⟨pairAverage_mem_Icc hyK.1 i j, by
      change (∑ k, pairAverage y i j k) = ∑ k, q k
      rw [sum_pairAverage y hij, hyK.2]⟩
    have hFzy : F z = F y := le_antisymm (havg y hyK.1 i j hij) (hymin z hzK)
    have hzL : z ∈ L := ⟨hzK, hFzy.trans hyL.2⟩
    have hv := hy hzL
    change (∑ k, (y k)^2) ≤ ∑ k, (pairAverage y i j k)^2 at hv
    rw [sum_sq_pairAverage y hij] at hv
    have hpos : 0 < (y i - y j)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    linarith
  have hconst : y = fun _ => p := by
    funext i
    have hsy : ∑ j, y j = (Fintype.card ι : ℝ) * y i := by
      calc
        ∑ j, y j = ∑ _j : ι, y i := Finset.sum_congr rfl (fun j _ => hequal j i)
        _ = _ := by simp
    have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    apply (mul_right_inj' hc).mp
    rw [← hsy, hyK.2, hsum]
  rw [← hconst]
  exact hymin q hqK

/-- Averaging two Bernoulli probabilities with the same sum can only decrease
an expected discretely concave function of the success count. -/
theorem bernoulliExpectation_pairAverage_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ι → ℝ} (hq : q ∈ Set.Icc 0 1) {i j : ι} (hij : i ≠ j)
    {f : ℕ → ℝ} (hf : ∀ n, f n + f (n + 2) ≤ 2 * f (n + 1)) :
    bernoulliExpectation (pairAverage q i j) Finset.univ f ≤
      bernoulliExpectation q Finset.univ f := by
  let s : Finset ι := (Finset.univ.erase i).erase j
  have his : i ∉ s := by simp [s]
  have hjs : j ∉ s := by simp [s]
  have hu : (Finset.univ : Finset ι) = insert i (insert j s) := by
    ext k
    simp only [Finset.mem_univ, Finset.mem_insert, true_iff]
    by_cases hki : k = i
    · exact Or.inl hki
    by_cases hkj : k = j
    · exact Or.inr (Or.inl hkj)
    · exact Or.inr (Or.inr (by simp [s, hki, hkj]))
  have hc : ∀ g : ℕ → ℝ,
      bernoulliExpectation (pairAverage q i j) s g = bernoulliExpectation q s g := by
    intro g
    apply bernoulliExpectation_congr
    intro k hk
    have hki : k ≠ i := by simpa [s] using (Finset.mem_erase.mp
      (Finset.mem_erase.mp hk).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    exact pairAverage_other q hki hkj
  have hsec := bernoulliExpectation_second_difference_nonpos
    (s := s) (q := q) (fun k _ => ⟨hq.1 k, hq.2 k⟩) hf
  rw [hu, bernoulliExpectation_insert_pair _ his hjs hij,
    bernoulliExpectation_insert_pair _ his hjs hij]
  simp only [pairAverage_left q hij, pairAverage_right, hc]
  have hnonneg := mul_nonneg (sq_nonneg (q i - q j))
    (sub_nonneg.mpr hsec)
  nlinarith

/-- The binomial law minimizes expected concave success-count functions among
independent Bernoulli laws of fixed mean. -/
theorem bernoulliExpectation_diagonal_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {q : ι → ℝ} (hq : q ∈ Set.Icc 0 1) {p : ℝ}
    (hsum : ∑ i, q i = Fintype.card ι * p) {f : ℕ → ℝ}
    (hf : ∀ n, f n + f (n + 2) ≤ 2 * f (n + 1)) :
    bernoulliExpectation (fun _ : ι => p) Finset.univ f ≤
      bernoulliExpectation q Finset.univ f := by
  apply diagonal_le_of_pairAverage (fun q => bernoulliExpectation q Finset.univ f)
    (continuous_bernoulliExpectation _ _) _ hq hsum
  intro p hp i j hij
  exact bernoulliExpectation_pairAverage_le hp hij hf

end GaussianPCA
