import GaussianPCA.LayerCake
import GaussianPCA.TopSum

noncomputable section
open scoped ENNReal BigOperators
open Set MeasureTheory Filter

namespace GaussianPCA

lemma lintegral_upperInterval (a : ℝ) :
    (∫⁻ t in Ioi 0, (Iio a).indicator (fun _ => (1 : ℝ≥0∞)) t) =
      ENNReal.ofReal a := by
  rw [lintegral_indicator measurableSet_Iio]
  simp [Measure.restrict_apply, measurableSet_Iio, Iio_inter_Ioi, Real.volume_Ioo]

lemma cast_filter_card_eq_indicator_sum {n : ℕ} (S : Finset (Fin n))
    (a : Fin n → ℝ) (t : ℝ) :
    ((S.filter fun i => t < a i).card : ℝ≥0∞) =
      ∑ i ∈ S, (Iio (a i)).indicator (fun _ => (1 : ℝ≥0∞)) t := by
  classical
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, indicator, mem_Iio]

/-- The exact pointwise layer-cake representation of the sum of the largest
    nonnegative coordinates. This has no sorting or tie-breaking assumptions. -/
theorem topSum_eq_lintegral_layers {n : ℕ} (d : ℕ) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    ENNReal.ofReal (topSum d a) =
      ∫⁻ t in Ioi 0, (min d (Finset.univ.filter fun i => t < a i).card : ℕ) := by
  obtain ⟨S, hS, hmax⟩ := exists_topSum_set d a
  rw [← hmax, ENNReal.ofReal_sum_of_nonneg (fun i _ => ha i)]
  calc
    (∑ i ∈ S, ENNReal.ofReal (a i)) =
        ∫⁻ t in Ioi 0, ∑ i ∈ S, (Iio (a i)).indicator (fun _ => (1 : ℝ≥0∞)) t := by
      rw [lintegral_finset_sum S (fun i _ => measurable_const.indicator measurableSet_Iio)]
      exact Finset.sum_congr rfl fun i _ => (lintegral_upperInterval (a i)).symm
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [← cast_filter_card_eq_indicator_sum,
        topSum_set_level_card d a S hS hmax ht.le]

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_layerCount_uncurry {n : ℕ} {B : Fin n → Ω → ℝ}
    (hB : ∀ i, Measurable (B i)) :
    Measurable (fun p : Ω × ℝ => layerCount B p.2 p.1) := by
  classical
  simp only [layerCount, Finset.card_filter]
  apply Finset.measurable_fun_sum
  intro i hi
  exact Measurable.ite (measurableSet_lt measurable_snd ((hB i).comp measurable_fst))
    measurable_const measurable_const

lemma measurable_layerCount {n : ℕ} {B : Fin n → Ω → ℝ}
    (hB : ∀ i, Measurable (B i)) (t : ℝ) : Measurable (layerCount B t) :=
  (measurable_layerCount_uncurry hB).comp (measurable_id.prodMk measurable_const)

lemma measurable_layerCap_uncurry {n : ℕ} (d : ℕ) {B : Fin n → Ω → ℝ}
    (hB : ∀ i, Measurable (B i)) :
    Measurable (fun p : Ω × ℝ => min (d : ℝ) (layerCount B p.2 p.1 : ℝ)) :=
  measurable_const.min ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    (measurable_layerCount_uncurry hB))

lemma measurable_topSum {n : ℕ} (d : ℕ) {B : Fin n → Ω → ℝ}
    (hB : ∀ i, Measurable (B i)) :
    Measurable (fun ω => topSum d (fun i => B i ω)) :=
  (continuous_topSum d).measurable.comp (measurable_pi_lambda _ hB)

lemma integrable_topSum {n : ℕ} (μ : Measure Ω) (d : ℕ) {B : Fin n → Ω → ℝ}
    (hBm : ∀ i, Measurable (B i)) (hB : ∀ i, Integrable (B i) μ)
    (hB0 : ∀ i ω, 0 ≤ B i ω) :
    Integrable (fun ω => topSum d (fun i => B i ω)) μ := by
  apply (integrable_finset_sum Finset.univ (fun i _ => hB i)).mono'
    (measurable_topSum d hBm).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (topSum_nonneg d _)]
    exact topSum_le_sum d _ (fun i => hB0 i ω)

/-- Tonelli's layer-cake identity, valid even when the expected top sum is infinite. -/
theorem lintegral_topSum_eq_lintegral_layers {n : ℕ} (μ : Measure Ω) [SFinite μ]
    (d : ℕ) {B : Fin n → Ω → ℝ} (hBm : ∀ i, Measurable (B i))
    (hB0 : ∀ i ω, 0 ≤ B i ω) :
    (∫⁻ ω, ENNReal.ofReal (topSum d (fun i => B i ω)) ∂μ) =
      ∫⁻ t in Ioi 0, ∫⁻ ω, (min d (layerCount B t ω) : ℕ) ∂μ := by
  simp_rw [topSum_eq_lintegral_layers d _ (fun i => hB0 i _)]
  apply lintegral_lintegral_swap
  have hm : Measurable (fun p : Ω × ℝ =>
      (min d (layerCount B p.2 p.1) : ℕ)) :=
    measurable_const.min (measurable_layerCount_uncurry hBm)
  exact ((measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp hm).aemeasurable


lemma integrable_layerCap {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (d : ℕ) {B : Fin n → Ω → ℝ} (hBm : ∀ i, Measurable (B i)) (t : ℝ) :
    Integrable (fun ω => min (d : ℝ) (layerCount B t ω : ℝ)) μ := by
  apply (integrable_const (d : ℝ)).mono'
    (measurable_const.min ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (measurable_layerCount hBm t))).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Nat.cast_nonneg d) (Nat.cast_nonneg _))]
    exact min_le_left _ _

lemma ofReal_integral_layerCap {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (d : ℕ) {B : Fin n → Ω → ℝ} (hBm : ∀ i, Measurable (B i)) (t : ℝ) :
    ENNReal.ofReal (∫ ω, min (d : ℝ) (layerCount B t ω : ℝ) ∂μ) =
      ∫⁻ ω, (min d (layerCount B t ω) : ℕ) ∂μ := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_layerCap μ d hBm t)
    (Eventually.of_forall fun ω => by positivity)]
  apply lintegral_congr
  intro ω
  rw [← Nat.cast_min, ENNReal.ofReal_natCast]

/-- The expected retained energy is the integral of the expected capped count.
    Both expectations are actual Bochner integrals. -/
theorem integral_topSum_eq_integral_layers {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (d : ℕ) {B : Fin n → Ω → ℝ} (hBm : ∀ i, Measurable (B i))
    (hB0 : ∀ i ω, 0 ≤ B i ω) :
    (∫ ω, topSum d (fun i => B i ω) ∂μ) =
      ∫ t in Ioi 0, ∫ ω, min (d : ℝ) (layerCount B t ω : ℝ) ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun ω => topSum_nonneg d _)
    (measurable_topSum d hBm).aestronglyMeasurable,
    lintegral_topSum_eq_lintegral_layers μ d hBm hB0,
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun t => integral_nonneg fun ω => by positivity)
      (measurable_layerCap_uncurry d hBm).stronglyMeasurable.integral_prod_left'.aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro t
  exact (ofReal_integral_layerCap μ d hBm t).symm

lemma integrableOn_expected_layerCap {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (d : ℕ) {B : Fin n → Ω → ℝ} (hBm : ∀ i, Measurable (B i))
    (hB : ∀ i, Integrable (B i) μ) (hB0 : ∀ i ω, 0 ≤ B i ω) :
    IntegrableOn (fun t => ∫ ω, min (d : ℝ) (layerCount B t ω : ℝ) ∂μ) (Ioi 0) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_layerCap_uncurry d hBm).stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    (Eventually.of_forall fun t => integral_nonneg fun ω => by positivity)).1
  simp_rw [ofReal_integral_layerCap μ d hBm]
  rw [← lintegral_topSum_eq_lintegral_layers μ d hBm hB0]
  exact (integrable_topSum μ d hBm hB hB0).lintegral_lt_top.ne

end GaussianPCA
