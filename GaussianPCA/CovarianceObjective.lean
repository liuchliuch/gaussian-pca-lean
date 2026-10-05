import GaussianPCA.Objective
import GaussianPCA.Spectral

/-!
# Basis objectives for an arbitrary positive-semidefinite covariance

The objective is defined on the actual Gaussian law, and the optimization ranges
over real orthogonal matrices. The spectral theorem and Gaussian uniqueness
identify these objectives with the independent-coordinate model. In particular,
no eigenbasis-existence or objective-comparison hypothesis is hidden in a data
structure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

namespace GaussianPCA

/-- The retained energy in the row-coordinate orthogonal basis `U`. -/
def covarianceEnergy {n : ℕ} (d : ℕ) (μ : Measure (Vector n))
    (U : CovarianceMatrix n) : ℝ :=
  ∫ x, topSum d (fun i => (U *ᵥ x) i ^ 2) ∂μ

/-- The set of all energies obtained by an actual orthogonal basis. -/
def covarianceBasisEnergyValues {n : ℕ} (d : ℕ) (μ : Measure (Vector n)) : Set ℝ :=
  {v | ∃ U : CovarianceMatrix n, IsOrthogonal U ∧ v = covarianceEnergy d μ U}

/-- Optimal nonlinear retained energy for a specified multivariate law. -/
def covarianceOpt {n : ℕ} (d : ℕ) (μ : Measure (Vector n)) : ℝ :=
  sSup (covarianceBasisEnergyValues d μ)

/-- The energy in the actual eigenbasis supplied by the spectral theorem. -/
def covarianceKLEnergy {n : ℕ} (d : ℕ) (μ : Measure (Vector n))
    {C : CovarianceMatrix n} (hC : C.PosSemidef) : ℝ :=
  covarianceEnergy d μ (eigenbasisMatrix hC).transpose

lemma IsOrthogonal.transpose {n : ℕ} {U : CovarianceMatrix n}
    (hU : IsOrthogonal U) : IsOrthogonal U.transpose := by
  simpa only [IsOrthogonal, Matrix.transpose_transpose] using hU.symm

lemma IsOrthogonal.mul {n : ℕ} {U V : CovarianceMatrix n}
    (hU : IsOrthogonal U) (hV : IsOrthogonal V) : IsOrthogonal (U * V) := by
  constructor
  · rw [Matrix.transpose_mul]
    calc
      (U * V) * (V.transpose * U.transpose) =
          (U * (V * V.transpose)) * U.transpose := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV.1, Matrix.mul_one, hU.1]
  · rw [Matrix.transpose_mul]
    calc
      (V.transpose * U.transpose) * (U * V) =
          (V.transpose * (U.transpose * U)) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU.2, Matrix.mul_one, hV.2]

lemma measurable_covarianceEnergy_integrand {n : ℕ} (d : ℕ)
    (U : CovarianceMatrix n) :
    Measurable (fun x : Vector n => topSum d (fun i => (U *ᵥ x) i ^ 2)) := by
  apply (continuous_topSum d).measurable.comp
  exact measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply i).comp (measurable_mulVec U)).pow_const 2

/-- Pushing a law forward by `Q` right-multiplies its coordinate matrix by `Q`. -/
lemma covarianceEnergy_map {n : ℕ} (d : ℕ) (μ : Measure (Vector n))
    (Q U : CovarianceMatrix n) :
    covarianceEnergy d (μ.map (fun x => Q *ᵥ x)) U = covarianceEnergy d μ (U * Q) := by
  unfold covarianceEnergy
  rw [integral_map (measurable_mulVec Q).aemeasurable
    (measurable_covarianceEnergy_integrand d U).aestronglyMeasurable]
  simp only [Matrix.mulVec_mulVec]

lemma covarianceEnergy_klMeasure {n : ℕ} (d : ℕ) (eig : Vector n)
    (U : CovarianceMatrix n) :
    covarianceEnergy d (klMeasure eig) U = rotatedEnergy d eig U := by
  unfold covarianceEnergy klMeasure
  rw [integral_map (measurable_klSample eig).aemeasurable
    (measurable_covarianceEnergy_integrand d U).aestronglyMeasurable]
  rfl

/-- Every basis energy for an arbitrary Gaussian law has the exact independent
spectral-model representation. No orthogonality restriction is needed here. -/
theorem covarianceEnergy_eq_rotatedEnergy {n : ℕ} (d : ℕ)
    {μ : Measure (Vector n)} {C : CovarianceMatrix n}
    (hμ : IsCenteredGaussian μ C) (hC : C.PosSemidef) (U : CovarianceMatrix n) :
    covarianceEnergy d μ U =
      rotatedEnergy d (spectrumValues hC) (U * eigenbasisMatrix hC) := by
  rw [hμ.eq_spectral_pushforward hC, covarianceEnergy_map, covarianceEnergy_klMeasure]

/-- Right multiplication by the actual eigenbasis gives precisely the same
set of feasible objective values. -/
theorem covarianceBasisEnergyValues_eq {n : ℕ} (d : ℕ)
    {μ : Measure (Vector n)} {C : CovarianceMatrix n}
    (hμ : IsCenteredGaussian μ C) (hC : C.PosSemidef) :
    covarianceBasisEnergyValues d μ = basisEnergyValues d (spectrumValues hC) := by
  ext v
  constructor
  · rintro ⟨U, hU, rfl⟩
    refine ⟨U * eigenbasisMatrix hC, hU.mul (eigenbasisMatrix_isOrthogonal hC), ?_⟩
    exact covarianceEnergy_eq_rotatedEnergy d hμ hC U
  · rintro ⟨V, hV, rfl⟩
    refine ⟨V * (eigenbasisMatrix hC).transpose,
      hV.mul (eigenbasisMatrix_isOrthogonal hC).transpose, ?_⟩
    rw [covarianceEnergy_eq_rotatedEnergy d hμ hC,
      Matrix.mul_assoc, (eigenbasisMatrix_isOrthogonal hC).2, Matrix.mul_one]

/-- The actual PSD-covariance optimization equals the concrete spectral model. -/
theorem covarianceOpt_eq_optEnergy {n : ℕ} (d : ℕ)
    {μ : Measure (Vector n)} {C : CovarianceMatrix n}
    (hμ : IsCenteredGaussian μ C) (hC : C.PosSemidef) :
    covarianceOpt d μ = optEnergy d (spectrumValues hC) := by
  unfold covarianceOpt optEnergy
  rw [covarianceBasisEnergyValues_eq d hμ hC]

/-- The energy of the actual KL basis equals the independent Gaussian KL energy. -/
theorem covarianceKLEnergy_eq_klEnergy {n : ℕ} (d : ℕ)
    {μ : Measure (Vector n)} {C : CovarianceMatrix n}
    (hμ : IsCenteredGaussian μ C) (hC : C.PosSemidef) :
    covarianceKLEnergy d μ hC = klEnergy d (spectrumValues hC) := by
  unfold covarianceKLEnergy
  rw [covarianceEnergy_eq_rotatedEnergy d hμ hC,
    (eigenbasisMatrix_isOrthogonal hC).2, rotatedEnergy_one]

lemma spectrumRank_spectrumValues {n : ℕ} {C : CovarianceMatrix n}
    (hC : C.PosSemidef) : spectrumRank (spectrumValues hC) = C.rank :=
  (rank_eq_card_positive_spectrumValues hC).symm

/-- The KL eigenbasis is feasible for the actual-law optimization. -/
theorem covarianceKLEnergy_le_covarianceOpt {n : ℕ} (d : ℕ)
    {μ : Measure (Vector n)} {C : CovarianceMatrix n}
    (hμ : IsCenteredGaussian μ C) (hC : C.PosSemidef) :
    covarianceKLEnergy d μ hC ≤ covarianceOpt d μ := by
  rw [covarianceKLEnergy_eq_klEnergy d hμ hC, covarianceOpt_eq_optEnergy d hμ hC]
  exact klEnergy_le_optEnergy d _ (spectrumValues_nonneg hC)

/-- Degenerate-rank clause of Paper Theorem 2 for the actual covariance law. -/
theorem covarianceKLEnergy_eq_trace_of_rank_le {n : ℕ} (d : ℕ)
    {μ : Measure (Vector n)} {C : CovarianceMatrix n}
    (hμ : IsCenteredGaussian μ C) (hC : C.PosSemidef) (hr : C.rank ≤ d) :
    covarianceKLEnergy d μ hC = Matrix.trace C := by
  rw [covarianceKLEnergy_eq_klEnergy d hμ hC, trace_eq_sum_spectrumValues hC]
  apply klEnergy_eq_trace_of_rank_le d _ (spectrumValues_nonneg hC)
  rwa [spectrumRank_spectrumValues hC]

/-- Degenerate-rank optimum clause of Paper Theorem 2 for the actual law. -/
theorem covarianceOpt_eq_trace_of_rank_le {n : ℕ} (d : ℕ)
    {μ : Measure (Vector n)} {C : CovarianceMatrix n}
    (hμ : IsCenteredGaussian μ C) (hC : C.PosSemidef) (hr : C.rank ≤ d) :
    covarianceOpt d μ = Matrix.trace C := by
  rw [covarianceOpt_eq_optEnergy d hμ hC, trace_eq_sum_spectrumValues hC]
  apply optEnergy_eq_trace_of_rank_le d _ (spectrumValues_nonneg hC)
  rwa [spectrumRank_spectrumValues hC]

end GaussianPCA
