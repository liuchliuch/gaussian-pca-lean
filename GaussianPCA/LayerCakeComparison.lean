import GaussianPCA.LayerCakeThreshold
import GaussianPCA.LayerCakeTopSum

noncomputable section
open scoped ENNReal BigOperators
open Set MeasureTheory Filter

namespace GaussianPCA

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Integrating any pointwise correlation-gap estimate gives the corresponding
    comparison between retained energy and the deterministic-threshold relaxation. -/
theorem integral_topSum_ge_threshold_of_layer_bound {n d : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {B : Fin n → Ω → ℝ}
    (hd : 0 < d) (hBm : ∀ i, Measurable (B i))
    (hB : ∀ i, Integrable (B i) μ) (hB0 : ∀ i ω, 0 ≤ B i ω)
    (c : ℝ)
    (hgap : ∀ t, 0 < t → c * min (d : ℝ) (tailMean μ B t) ≤
      ∫ ω, min (d : ℝ) (layerCount B t ω : ℝ) ∂μ) :
    c * thresholdRelaxation μ d B ≤ ∫ ω, topSum d (fun i => B i ω) ∂μ := by
  rw [thresholdRelaxation_eq_integral_tailMean μ hd hBm hB,
    integral_topSum_eq_integral_layers μ d hBm hB0]
  rw [← integral_const_mul]
  apply setIntegral_mono_on
  · exact (integrableOn_cap (measurable_tailMean μ B) (tailMean_nonneg μ B)
      (integrableOn_tailMean μ hBm hB 0) (Nat.cast_nonneg d)).const_mul c
  · exact integrableOn_expected_layerCap μ d hBm hB hB0
  · exact measurableSet_Ioi
  · exact hgap

end GaussianPCA
