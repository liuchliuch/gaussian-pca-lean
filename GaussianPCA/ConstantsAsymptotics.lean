import GaussianPCA.Constants

/-!
# Quantitative Stirling remainder and inverse-constant asymptotics

Mathlib proves a successive-logarithm estimate for its Stirling sequence.
Telescoping that estimate against `1/(2n)` supplies the rate needed here; mere
asymptotic equivalence of factorials would not by itself imply this remainder.
-/

open scoped Topology Nat Asymptotics
open Filter Real

namespace GaussianPCA

private lemma stirlingSeq_pos {n : ℕ} (hn : 0 < n) : 0 < Stirling.stirlingSeq n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact Stirling.stirlingSeq'_pos n

/-- A concrete logarithmic Stirling remainder, sufficient for a `1/n` error term. -/
theorem log_stirlingSeq_error_bounds {n : ℕ} (hn : 0 < n) :
    0 ≤ log (Stirling.stirlingSeq n) - log (sqrt π) ∧
      log (Stirling.stirlingSeq n) - log (sqrt π) ≤ 1 / (2 * (n : ℝ)) := by
  constructor
  · exact sub_nonneg.mpr (log_le_log (by positivity) (Stirling.sqrt_pi_le_stirlingSeq hn.ne'))
  · let f : ℕ → ℝ := fun k => log (Stirling.stirlingSeq (k + 1)) - 1 / (2 * (k + 1 : ℕ))
    have hmono : Monotone f := by
      apply monotone_nat_of_le_succ
      intro k
      have h := Stirling.log_stirlingSeq_sub_log_stirlingSeq_succ k
      have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
      have htel : 1 / (4 * ((k + 1 : ℕ) : ℝ) ^ 2) ≤
          1 / (2 * ((k + 1 : ℕ) : ℝ)) - 1 / (2 * ((k + 2 : ℕ) : ℝ)) := by
        have hk0 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hk1 : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
        push_cast at *
        nlinarith
      dsimp [f]
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using (by linarith :
        log (Stirling.stirlingSeq (k + 1)) - 1 / (2 * ((k + 1 : ℕ) : ℝ)) ≤
          log (Stirling.stirlingSeq (k + 2)) - 1 / (2 * ((k + 2 : ℕ) : ℝ)))
    have hlog : Tendsto (fun k : ℕ => log (Stirling.stirlingSeq (k + 1))) atTop (𝓝 (log (sqrt π))) :=
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)).log (by positivity)
    have hinv : Tendsto (fun k : ℕ => 1 / (2 * ((k + 1 : ℕ) : ℝ))) atTop (𝓝 (0 : ℝ)) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ)).comp (tendsto_add_atTop_nat 1)
      convert h using 1
      ext k
      simp only [Function.comp_apply]
      ring
    have hlim : Tendsto f atTop (𝓝 (log (sqrt π))) := by
      simpa [f] using hlog.sub hinv
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have h := hmono.ge_of_tendsto hlim k
    dsimp [f] at h
    linarith

lemma poissonDefect_eq_leading_mul_exp {n : ℕ} (hn : 0 < n) :
    poissonDefect n = stirlingLeading n *
      exp (-(log (Stirling.stirlingSeq n) - log (sqrt π))) := by
  rw [neg_sub, exp_sub, exp_log (by positivity : 0 < sqrt π),
    exp_log (stirlingSeq_pos hn), poissonDefect_eq_stirling hn]
  unfold stirlingLeading
  have hs : sqrt (2 * π * (n : ℝ)) = sqrt (2 * (n : ℝ)) * sqrt π := by
    rw [← sqrt_mul (by positivity)]
    congr 1
    ring
  rw [hs]
  have hS := (stirlingSeq_pos hn).ne'
  have hπ : sqrt π ≠ 0 := by positivity
  have hn' : sqrt (2 * (n : ℝ)) ≠ 0 := by positivity
  field_simp

/-- An effective error estimate for the Poisson mass in Stirling's formula. -/
theorem leading_sub_poissonDefect_bounds {n : ℕ} (hn : 0 < n) :
    0 ≤ stirlingLeading n - poissonDefect n ∧
      stirlingLeading n - poissonDefect n ≤ 1 / (2 * (n : ℝ)) := by
  constructor
  · exact sub_nonneg.mpr (poissonDefect_le_leading hn)
  · let δ := log (Stirling.stirlingSeq n) - log (sqrt π)
    have hδ := log_stirlingSeq_error_bounds hn
    have he : 1 - exp (-δ) ≤ δ := by
      have h := add_one_le_exp (-δ)
      linarith
    rw [poissonDefect_eq_leading_mul_exp hn]
    have ha : 0 ≤ stirlingLeading n := (stirlingLeading_pos hn).le
    have ha1 : stirlingLeading n ≤ 1 := (stirlingLeading_le_half hn).trans (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left he ha
    have hmul' := mul_le_mul_of_nonneg_right ha1 hδ.1
    dsimp [δ] at *
    nlinarith

lemma stirlingLeading_sq {n : ℕ} (hn : 0 < n) :
    stirlingLeading n ^ 2 = 1 / (2 * π * (n : ℝ)) := by
  unfold stirlingLeading
  rw [div_pow, sq_sqrt (by positivity)]
  norm_num

lemma poissonDefect_sq_bound {n : ℕ} (hn : 0 < n) :
    poissonDefect n ^ 2 ≤ 1 / (2 * (n : ℝ)) := by
  calc
    poissonDefect n ^ 2 ≤ stirlingLeading n ^ 2 :=
      pow_le_pow_left₀ (poissonDefect_nonneg n) (poissonDefect_le_leading hn) 2
    _ = 1 / (2 * π * (n : ℝ)) := stirlingLeading_sq hn
    _ ≤ 1 / (2 * (n : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      have hn' : 0 ≤ (n : ℝ) := by positivity
      nlinarith [Real.two_le_pi]

/-- A uniform explicit bound proving the full first-order inverse asymptotic. -/
theorem poissonConstant_inverse_remainder_bound {n : ℕ} (hn : 0 < n) :
    |(poissonConstant n)⁻¹ - 1 - stirlingLeading n| ≤ 2 / (n : ℝ) := by
  have hq := poissonDefect_nonneg n
  have hqhalf := (poissonDefect_le_leading hn).trans (stirlingLeading_le_half hn)
  have hγ := poissonConstant_pos hn
  have herr := leading_sub_poissonDefect_bounds hn
  have hsq := poissonDefect_sq_bound hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hid : (poissonConstant n)⁻¹ - 1 - stirlingLeading n =
      poissonDefect n ^ 2 / poissonConstant n - (stirlingLeading n - poissonDefect n) := by
    unfold poissonConstant
    have hne : 1 - poissonDefect n ≠ 0 := hγ.ne'
    field_simp
    ring
  have hterm : 0 ≤ poissonDefect n ^ 2 / poissonConstant n := by positivity
  have hterm' : poissonDefect n ^ 2 / poissonConstant n ≤ 2 * poissonDefect n ^ 2 := by
    apply (div_le_iff₀ hγ).2
    unfold poissonConstant
    have hprod := mul_nonneg (sq_nonneg (poissonDefect n))
      (show 0 ≤ 1 - 2 * poissonDefect n by linarith)
    nlinarith
  rw [hid, abs_le]
  have hdiv : 1 / (2 * (n : ℝ)) = (1 / (n : ℝ)) / 2 := by ring
  have hdiv2 : 2 / (n : ℝ) = 2 * (1 / (n : ℝ)) := by ring
  rw [hdiv] at herr hsq
  rw [hdiv2]
  constructor <;> nlinarith [one_div_pos.mpr hn']

/-- The precise `1 + 1/√(2πn) + O(1/n)` assertion, as an actual `IsBigO` theorem. -/
theorem poissonConstant_inverse_asymptotic :
    (fun n : ℕ => (poissonConstant n)⁻¹ - 1 - 1 / sqrt (2 * π * (n : ℝ)))
      =O[atTop] (fun n : ℕ => 1 / (n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ))]
  simpa [stirlingLeading, div_eq_mul_inv] using poissonConstant_inverse_remainder_bound hn

/-- The coarser dimension-free `1 + O(1/√n)` comparison. -/
theorem poissonConstant_inverse_bigO :
    (fun n : ℕ => (poissonConstant n)⁻¹ - 1)
      =O[atTop] (fun n : ℕ => 1 / sqrt (n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : 0 < n := hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrem := poissonConstant_inverse_remainder_bound hn0
  have hlead : stirlingLeading n ≤ 1 / sqrt (n : ℝ) := by
    unfold stirlingLeading
    apply one_div_le_one_div_of_le (by positivity)
    apply sqrt_le_sqrt
    nlinarith [Real.two_le_pi]
  have hsqrt : sqrt (n : ℝ) ≤ n := by
    apply (sqrt_le_iff).2
    constructor <;> nlinarith
  have hinv : 1 / (n : ℝ) ≤ 1 / sqrt (n : ℝ) :=
    one_div_le_one_div_of_le (by positivity) hsqrt
  have habs : |(poissonConstant n)⁻¹ - 1| ≤
      |(poissonConstant n)⁻¹ - 1 - stirlingLeading n| + |stirlingLeading n| := by
    simpa only [sub_add_cancel] using
      abs_add_le ((poissonConstant n)⁻¹ - 1 - stirlingLeading n) (stirlingLeading n)
  rw [abs_of_nonneg (stirlingLeading_pos hn0).le] at habs
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / sqrt (n : ℝ))]
  have hdiv : 2 / (n : ℝ) = 2 * (1 / (n : ℝ)) := by ring
  rw [hdiv] at hrem
  linarith [one_div_nonneg.mpr (sqrt_nonneg (n : ℝ))]

end GaussianPCA
