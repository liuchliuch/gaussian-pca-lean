import GaussianPCA.CovarianceObjective
import GaussianPCA.GaussianLayerApplication
import GaussianPCA.ConstantsAsymptotics

/-!
# The correlation-gap comparison for nonlinear Gaussian PCA

The final theorem quantifies over actual centered Gaussian probability laws and
positive semidefinite covariance matrices. All analytic and combinatorial
inequalities are discharged by the imported proofs.
-/

noncomputable section
open MeasureTheory Matrix

namespace GaussianPCA

theorem spectral_correlation_gap_bound {n : ℕ} (d : ℕ) (eig : Vector n)
    (heig : ∀ i, 0 ≤ eig i) (hd : 1 ≤ d) (hr : d < spectrumRank eig) :
    klEnergy d eig ≤ optEnergy d eig ∧
    optEnergy d eig ≤ (finiteRankConstant d (spectrumRank eig))⁻¹ * klEnergy d eig ∧
    (finiteRankConstant d (spectrumRank eig))⁻¹ * klEnergy d eig ≤
      (poissonConstant d)⁻¹ * klEnergy d eig := by
  have hc := finiteRankConstant_pos (show 0 < d by omega) hr
  have hlow := klEnergy_ge_finiteRankConstant_mul_thresholdEnergy d eig heig hd hr
  refine ⟨klEnergy_le_optEnergy d eig heig, ?_, ?_⟩
  · calc
      optEnergy d eig ≤ thresholdEnergy d eig := optEnergy_le_thresholdEnergy d eig heig
      _ ≤ klEnergy d eig / finiteRankConstant d (spectrumRank eig) := by
        apply (le_div_iff₀ hc).2
        nlinarith
      _ = (finiteRankConstant d (spectrumRank eig))⁻¹ * klEnergy d eig := by ring
  · exact mul_le_mul_of_nonneg_right
      (finiteRankConstant_inv_le (show 0 < d by omega) hr) (klEnergy_nonneg d eig)

/-- Paper Theorem 2, the nontrivial-rank clause for any PSD covariance law. -/
theorem covariance_correlation_gap_bound {n : ℕ} (d : ℕ)
    {μ : Measure (Vector n)} {C : CovarianceMatrix n}
    (hμ : IsCenteredGaussian μ C) (hC : C.PosSemidef)
    (hd : 1 ≤ d) (hr : d < C.rank) :
    covarianceKLEnergy d μ hC ≤ covarianceOpt d μ ∧
    covarianceOpt d μ ≤ (finiteRankConstant d C.rank)⁻¹ * covarianceKLEnergy d μ hC ∧
    (finiteRankConstant d C.rank)⁻¹ * covarianceKLEnergy d μ hC ≤
      (poissonConstant d)⁻¹ * covarianceKLEnergy d μ hC := by
  rw [covarianceKLEnergy_eq_klEnergy d hμ hC, covarianceOpt_eq_optEnergy d hμ hC]
  have h := spectral_correlation_gap_bound d (spectrumValues hC)
    (spectrumValues_nonneg hC) hd (by rwa [spectrumRank_spectrumValues hC])
  simpa only [spectrumRank_spectrumValues hC] using h

/-- The complete rank split in Paper Theorem 2. -/
theorem nonlinear_gaussian_pca {n : ℕ} (d : ℕ)
    {μ : Measure (Vector n)} {C : CovarianceMatrix n}
    (hμ : IsCenteredGaussian μ C) (hC : C.PosSemidef) (hd : 1 ≤ d) (_hdn : d ≤ n) :
    (C.rank ≤ d → covarianceOpt d μ = Matrix.trace C ∧
      covarianceKLEnergy d μ hC = Matrix.trace C) ∧
    (d < C.rank → covarianceKLEnergy d μ hC ≤ covarianceOpt d μ ∧
      covarianceOpt d μ ≤ (finiteRankConstant d C.rank)⁻¹ * covarianceKLEnergy d μ hC ∧
      (finiteRankConstant d C.rank)⁻¹ * covarianceKLEnergy d μ hC ≤
        (poissonConstant d)⁻¹ * covarianceKLEnergy d μ hC) := by
  constructor
  · intro hr
    exact ⟨covarianceOpt_eq_trace_of_rank_le d hμ hC hr,
      covarianceKLEnergy_eq_trace_of_rank_le d hμ hC hr⟩
  · exact covariance_correlation_gap_bound d hμ hC hd

/-- The original constant-one conjecture is recorded only as a proposition.
No proof of this open conjecture is asserted by this project. -/
def MallatZeitouniConjecture : Prop :=
  ∀ (n d : ℕ) (μ : Measure (Vector n)) (C : CovarianceMatrix n)
    (hC : C.PosSemidef), IsCenteredGaussian μ C → 1 ≤ d → d < n →
      covarianceOpt d μ ≤ covarianceKLEnergy d μ hC

end GaussianPCA
