import GaussianPCA.LayerCake

noncomputable section
open scoped ENNReal BigOperators
open Set MeasureTheory Filter

namespace GaussianPCA

lemma integrableOn_cap {m : ℝ → ℝ} (hm : Measurable m) (hm0 : ∀ t, 0 ≤ m t)
    (hmi : IntegrableOn m (Ioi 0)) {d : ℝ} (hd : 0 ≤ d) :
    IntegrableOn (fun t => min d (m t)) (Ioi 0) := by
  apply hmi.mono' (measurable_const.min hm).aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hd (hm0 t))]
    exact min_le_right _ _

lemma integral_Ioi_split {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (∫ t in Ioi 0, f t) = (∫ t in Ioc 0 τ, f t) + ∫ t in Ioi τ, f t := by
  rw [← Ioc_union_Ioi_eq_Ioi hτ]
  apply setIntegral_union
  · exact disjoint_left.2 fun t ht ht' => (not_lt_of_ge ht.2) ht'
  · exact measurableSet_Ioi
  · exact hf.mono_set Ioc_subset_Ioi_self
  · exact hf.mono_set (Ioi_subset_Ioi hτ)

lemma integral_cap_le_threshold {m : ℝ → ℝ} (hm : Measurable m)
    (hm0 : ∀ t, 0 ≤ m t) (hmi : IntegrableOn m (Ioi 0))
    {d τ : ℝ} (hd : 0 ≤ d) (hτ : 0 ≤ τ) :
    (∫ t in Ioi 0, min d (m t)) ≤ d * τ + ∫ t in Ioi τ, m t := by
  have hcap := integrableOn_cap hm hm0 hmi hd
  rw [integral_Ioi_split hcap hτ]
  have hleft : (∫ t in Ioc 0 τ, min d (m t)) ≤ d * τ := by
    calc
      _ ≤ ∫ _ in Ioc (0 : ℝ) τ, d :=
        setIntegral_mono_on (hcap.mono_set Ioc_subset_Ioi_self)
          (integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc (fun _ _ => min_le_left _ _)
      _ = _ := by simp [Real.volume_Ioc, Measure.real, hτ, mul_comm]
  have hright : (∫ t in Ioi τ, min d (m t)) ≤ ∫ t in Ioi τ, m t :=
    setIntegral_mono_on (hcap.mono_set (Ioi_subset_Ioi hτ))
      (hmi.mono_set (Ioi_subset_Ioi hτ)) measurableSet_Ioi
      (fun _ _ => min_le_right _ _)
  exact add_le_add hleft hright

lemma integral_cap_eq_at_crossing {m : ℝ → ℝ} (hm : Measurable m)
    (hm0 : ∀ t, 0 ≤ m t) (hmi : IntegrableOn m (Ioi 0))
    {d τ : ℝ} (hd : 0 ≤ d) (hτ : 0 ≤ τ)
    (hleft : ∀ t, 0 < t → t < τ → d ≤ m t)
    (hright : ∀ t, τ < t → m t ≤ d) :
    (∫ t in Ioi 0, min d (m t)) = d * τ + ∫ t in Ioi τ, m t := by
  rw [integral_Ioi_split (integrableOn_cap hm hm0 hmi hd) hτ]
  congr 1
  · rw [integral_Ioc_eq_integral_Ioo]
    calc
      _ = ∫ _ in Ioo (0 : ℝ) τ, d := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t ht
        exact min_eq_left (hleft t ht.1 ht.2)
      _ = _ := by simp [Real.volume_Ioo, Measure.real, hτ, mul_comm]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact min_eq_right (hright t ht)

/-- The integral of a capped antitone tail is exactly the least deterministic
    threshold cost. The existence assertion also certifies attainment. -/
theorem isLeast_threshold_integral {m : ℝ → ℝ} (hm : Antitone m)
    (hm0 : ∀ t, 0 ≤ m t) (hmi : IntegrableOn m (Ioi 0))
    (hlim : Tendsto m atTop (nhds 0)) {d : ℝ} (hd : 0 < d) :
    IsLeast {v : ℝ | ∃ τ : ℝ, 0 ≤ τ ∧ v = d * τ + ∫ t in Ioi τ, m t}
      (∫ t in Ioi 0, min d (m t)) := by
  constructor
  · obtain ⟨τ, hτ, hl, hr⟩ := exists_antitone_crossing hm hlim hd
    exact ⟨τ, hτ, integral_cap_eq_at_crossing hm.measurable hm0 hmi hd.le hτ hl hr⟩
  · rintro v ⟨τ, hτ, rfl⟩
    exact integral_cap_le_threshold hm.measurable hm0 hmi hd.le hτ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Distribution-general threshold-relaxation identity. Independence and
    continuity of the coordinate distributions are unnecessary. -/
theorem thresholdRelaxation_eq_integral_tailMean {n d : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {B : Fin n → Ω → ℝ}
    (hd : 0 < d) (hBm : ∀ i, Measurable (B i))
    (hB : ∀ i, Integrable (B i) μ) :
    thresholdRelaxation μ d B = ∫ t in Ioi 0, min (d : ℝ) (tailMean μ B t) := by
  have hleast := isLeast_threshold_integral (tailMean_antitone μ B)
    (tailMean_nonneg μ B) (integrableOn_tailMean μ hBm hB 0)
    (tendsto_tailMean μ hBm) (d := (d : ℝ)) (by exact_mod_cast hd)
  rw [thresholdRelaxation]
  have hsets : {v : ℝ | ∃ τ : ℝ, 0 ≤ τ ∧
      v = (d : ℝ) * τ + ∑ i, ∫ ω, max (B i ω - τ) 0 ∂μ} =
      {v : ℝ | ∃ τ : ℝ, 0 ≤ τ ∧
      v = (d : ℝ) * τ + ∫ t in Ioi τ, tailMean μ B t} := by
    simp_rw [sum_integral_posPart_eq_tailMean μ hBm hB]
  rw [hsets]
  exact hleast.csInf_eq

end GaussianPCA
