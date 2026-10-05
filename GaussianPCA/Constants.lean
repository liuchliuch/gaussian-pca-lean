import GaussianPCA.ConstantsDefinition
import Mathlib.Tactic

/-!
# The exact constants in the Gaussian PCA comparison

The finite-rank comparison is proved directly from the monotonicity of the
Stirling sequence. No contention-resolution or correlation-gap result is used
as an assumption in this file.
-/

open scoped Topology Nat Asymptotics
open Filter Real

namespace GaussianPCA

lemma poissonDefect_eq (d : ℕ) :
    poissonDefect d = ((d : ℝ) / exp 1) ^ d / (d.factorial : ℝ) := by
  unfold poissonDefect
  rw [exp_neg, div_pow, ← exp_nat_mul, mul_one]
  ring

lemma poissonDefect_pos {d : ℕ} (hd : 0 < d) : 0 < poissonDefect d := by
  unfold poissonDefect
  positivity

lemma poissonDefect_nonneg (d : ℕ) : 0 ≤ poissonDefect d := by
  unfold poissonDefect
  positivity

lemma poissonDefect_eq_stirling {d : ℕ} (hd : 0 < d) :
    poissonDefect d = 1 / (sqrt (2 * (d : ℝ)) * Stirling.stirlingSeq d) := by
  rw [poissonDefect_eq, Stirling.stirlingSeq]
  have hn : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hs : sqrt (2 * (d : ℝ)) ≠ 0 := by positivity
  have hf : (d.factorial : ℝ) ≠ 0 := by positivity
  have hp : ((d : ℝ) / exp 1) ^ d ≠ 0 := pow_ne_zero _ (div_ne_zero hn (exp_ne_zero _))
  field_simp

lemma stirlingLeading_pos {d : ℕ} (hd : 0 < d) : 0 < stirlingLeading d := by
  unfold stirlingLeading
  positivity

lemma poissonDefect_le_leading {d : ℕ} (hd : 0 < d) :
    poissonDefect d ≤ stirlingLeading d := by
  rw [poissonDefect_eq_stirling hd]
  unfold stirlingLeading
  have heq : sqrt (2 * π * (d : ℝ)) = sqrt (2 * (d : ℝ)) * sqrt π := by
    rw [← sqrt_mul (by positivity)]
    congr 1
    ring
  rw [heq]
  exact one_div_le_one_div_of_le (by positivity)
    (mul_le_mul_of_nonneg_left (Stirling.sqrt_pi_le_stirlingSeq hd.ne') (sqrt_nonneg _))

lemma stirlingLeading_le_half {d : ℕ} (hd : 0 < d) : stirlingLeading d ≤ 1 / 2 := by
  unfold stirlingLeading
  apply one_div_le_one_div_of_le (by norm_num)
  apply (le_sqrt (by norm_num) (by positivity)).2
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith [Real.two_le_pi]

lemma poissonConstant_pos {d : ℕ} (hd : 0 < d) : 0 < poissonConstant d := by
  have h := (poissonDefect_le_leading hd).trans (stirlingLeading_le_half hd)
  unfold poissonConstant
  linarith

lemma poissonConstant_le_one (d : ℕ) : poissonConstant d ≤ 1 := by
  unfold poissonConstant
  linarith [poissonDefect_nonneg d]

/-- This factorial normalization decreases for positive indices. -/
noncomputable def normalizedFactorial (n : ℕ) : ℝ :=
  (n.factorial : ℝ) / ((n : ℝ) / exp 1) ^ n / n

lemma normalizedFactorial_pos {n : ℕ} (hn : 0 < n) : 0 < normalizedFactorial n := by
  unfold normalizedFactorial
  positivity

lemma normalizedFactorial_eq {n : ℕ} (hn : 0 < n) :
    normalizedFactorial n = 2 * Stirling.stirlingSeq n / sqrt (2 * (n : ℝ)) := by
  unfold normalizedFactorial Stirling.stirlingSeq
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : sqrt (2 * (n : ℝ)) ≠ 0 := by positivity
  have hp : ((n : ℝ) / exp 1) ^ n ≠ 0 := by positivity
  have hsq := sq_sqrt (show 0 ≤ 2 * (n : ℝ) by positivity)
  field_simp
  nlinarith [sq_sqrt (show 0 ≤ (n : ℝ) * 2 by positivity)]

lemma normalizedFactorial_antitone {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m) :
    normalizedFactorial m ≤ normalizedFactorial n := by
  have hm : 0 < m := hn.trans_le hnm
  rw [normalizedFactorial_eq hn, normalizedFactorial_eq hm]
  have hS : Stirling.stirlingSeq m ≤ Stirling.stirlingSeq n := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    exact Stirling.stirlingSeq'_antitone (Nat.succ_le_succ_iff.mp hnm)
  have hSn : 0 < Stirling.stirlingSeq n := by unfold Stirling.stirlingSeq; positivity
  apply div_le_div₀ (by positivity) (by linarith) (by positivity)
  exact sqrt_le_sqrt (by exact_mod_cast Nat.mul_le_mul_left 2 hnm)

/-- An exact identity reducing the binomial loss to a ratio of normalized factorials. -/
lemma finiteRankConstant_defect_eq {d r : ℕ} (hd : 0 < d) (hdr : d < r) :
    1 - finiteRankConstant d r =
      poissonDefect d * (normalizedFactorial r / normalizedFactorial (r - d)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hdr.le
  have hn : 0 < n := by omega
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hr' : ((d + n : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : ((d + n).choose d : ℝ) * (d.factorial : ℝ) * (n.factorial : ℝ) =
      ((d + n).factorial : ℝ) := by
    simpa only [Nat.add_sub_cancel_left, Nat.cast_mul] using
      congrArg (fun k : ℕ => (k : ℝ))
        (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right d n))
  have hp : 1 - (d : ℝ) / (d + n) = (n : ℝ) / (d + n) := by field_simp; ring
  unfold finiteRankConstant normalizedFactorial
  rw [poissonDefect_eq]
  simp only [Nat.add_sub_cancel_left, Nat.cast_add]
  rw [show d + n + 1 - d = n + 1 by omega, hp, ← hf]
  simp only [div_pow, pow_add, pow_one]
  field_simp
  ring

/-- The finite-rank loss is at most its Poisson limit, with no asymptotic assumption. -/
theorem poissonConstant_le_finiteRankConstant {d r : ℕ} (hd : 0 < d) (hdr : d < r) :
    poissonConstant d ≤ finiteRankConstant d r := by
  have hn : 0 < r - d := Nat.sub_pos_of_lt hdr
  have hratio : normalizedFactorial r / normalizedFactorial (r - d) ≤ 1 :=
    (div_le_one (normalizedFactorial_pos hn)).2
      (normalizedFactorial_antitone hn (Nat.sub_le r d))
  have h := mul_le_mul_of_nonneg_left hratio (poissonDefect_nonneg d)
  rw [← finiteRankConstant_defect_eq hd hdr, mul_one] at h
  unfold poissonConstant
  linarith

theorem finiteRankConstant_pos {d r : ℕ} (hd : 0 < d) (hdr : d < r) :
    0 < finiteRankConstant d r :=
  (poissonConstant_pos hd).trans_le (poissonConstant_le_finiteRankConstant hd hdr)

theorem finiteRankConstant_inv_le {d r : ℕ} (hd : 0 < d) (hdr : d < r) :
    (finiteRankConstant d r)⁻¹ ≤ (poissonConstant d)⁻¹ :=
  inv_anti₀ (poissonConstant_pos hd) (poissonConstant_le_finiteRankConstant hd hdr)

lemma normalizedFactorial_ratio {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    normalizedFactorial m / normalizedFactorial n =
      (Stirling.stirlingSeq m / Stirling.stirlingSeq n) * sqrt ((n : ℝ) / m) := by
  rw [normalizedFactorial_eq hn, normalizedFactorial_eq hm]
  rw [sqrt_div (by positivity), sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hn' : sqrt (n : ℝ) ≠ 0 := by positivity
  have hm' : sqrt (m : ℝ) ≠ 0 := by positivity
  have h2 : sqrt (2 : ℝ) ≠ 0 := by positivity
  have hs : Stirling.stirlingSeq n ≠ 0 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact (Stirling.stirlingSeq'_pos n).ne'
  field_simp

/-- For a fixed retained rank, the finite-rank constants converge to the Poisson constant. -/
theorem tendsto_finiteRankConstant (d : ℕ) (hd : 0 < d) :
    Tendsto (finiteRankConstant d) atTop (𝓝 (poissonConstant d)) := by
  have hS := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hS' := hS.comp (tendsto_sub_atTop_nat d)
  have hsπ : sqrt π ≠ 0 := by positivity
  have hratio : Tendsto (fun r : ℕ => (r - d : ℕ) / (r : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    have h : Tendsto (fun r : ℕ => 1 - (d : ℝ) / r) atTop (𝓝 (1 - 0 : ℝ)) :=
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (d : ℝ))
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop d] with r hr
    rw [Nat.cast_sub hr]
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (hd.trans_le hr).ne'
    field_simp
  have hlim : Tendsto (fun r : ℕ => normalizedFactorial r / normalizedFactorial (r - d))
      atTop (𝓝 (1 : ℝ)) := by
    have h := (hS.div hS' hsπ).mul hratio.sqrt
    simp only [div_self hsπ, sqrt_one, mul_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop d] with r hr
    exact (normalizedFactorial_ratio (Nat.sub_pos_of_lt hr) (hd.trans hr)).symm
  have h : Tendsto (fun r : ℕ => 1 - poissonDefect d *
      (normalizedFactorial r / normalizedFactorial (r - d)))
      atTop (𝓝 (1 - poissonDefect d * 1)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim)
  simp only [mul_one] at h
  change Tendsto (finiteRankConstant d) atTop (𝓝 (1 - poissonDefect d))
  apply h.congr'
  filter_upwards [eventually_gt_atTop d] with r hr
  linarith [finiteRankConstant_defect_eq hd hr]

end GaussianPCA
