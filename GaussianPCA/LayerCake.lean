import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Layer-cake identities for nonnegative coordinate energies

The measure-theoretic statements here use ordinary Lebesgue and Bochner integrals.
They apply to arbitrary measurable coordinates, so in particular include Gaussian
squares with zero variances without any non-atomicity or strict-positivity assumption.
-/

noncomputable section

open scoped ENNReal BigOperators
open Set MeasureTheory Filter

namespace GaussianPCA

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The strict upper-tail probability, as a real number. -/
def tailProb (μ : Measure Ω) (B : Ω → ℝ) (t : ℝ) : ℝ :=
  μ.real {ω | t < B ω}

/-- Sum of the marginal strict-tail probabilities. -/
def tailMean {n : ℕ} (μ : Measure Ω) (B : Fin n → Ω → ℝ) (t : ℝ) : ℝ :=
  ∑ i, tailProb μ (B i) t

/-- The random number of coordinates strictly above a level. -/
def layerCount {n : ℕ} (B : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  (Finset.univ.filter fun i => t < B i ω).card

/-- The positive-part stop-loss expectation equals its integrated strict tail. -/
theorem lintegral_posPart_eq_tail (μ : Measure Ω) [SFinite μ]
    {B : Ω → ℝ} (hB : Measurable B) (τ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (max (B ω - τ) 0) ∂μ) =
      ∫⁻ t in Ioi τ, μ {ω | t < B ω} := by
  have hpoint (b : ℝ) :
      ENNReal.ofReal (max (b - τ) 0) =
        ∫⁻ t in Ioi τ, (Iio b).indicator (fun _ => (1 : ℝ≥0∞)) t := by
    rw [lintegral_indicator measurableSet_Iio]
    simp [Measure.restrict_apply, measurableSet_Iio, Real.volume_Ioo,
      Iio_inter_Ioi, ENNReal.ofReal_max]
  simp_rw [hpoint]
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro t
    have hind : (fun ω => (Iio (B ω)).indicator (fun _ => (1 : ℝ≥0∞)) t) =
        {ω | t < B ω}.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      simp only [indicator, mem_Iio, mem_setOf_eq]
    rw [hind, lintegral_indicator (measurableSet_lt measurable_const hB)]
    simp
  · have hset : MeasurableSet {p : Ω × ℝ | p.2 < B p.1} :=
      measurableSet_lt measurable_snd (hB.comp measurable_fst)
    have hind : (Function.uncurry fun ω t =>
        (Iio (B ω)).indicator (fun _ => (1 : ℝ≥0∞)) t) =
        {p : Ω × ℝ | p.2 < B p.1}.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext p
      simp only [Function.uncurry, indicator, mem_Iio, mem_setOf_eq]
    rw [hind]
    exact (measurable_const.indicator hset).aemeasurable


lemma tailProb_nonneg (μ : Measure Ω) (B : Ω → ℝ) (t : ℝ) :
    0 ≤ tailProb μ B t := ENNReal.toReal_nonneg

lemma tailProb_antitone (μ : Measure Ω) [IsFiniteMeasure μ] (B : Ω → ℝ) :
    Antitone (tailProb μ B) := by
  intro s t hst
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => hst.trans_lt hω)

lemma measurable_tailProb (μ : Measure Ω) [IsFiniteMeasure μ] (B : Ω → ℝ) :
    Measurable (tailProb μ B) := (tailProb_antitone μ B).measurable

lemma tailMean_nonneg {n : ℕ} (μ : Measure Ω) (B : Fin n → Ω → ℝ) (t : ℝ) :
    0 ≤ tailMean μ B t := Finset.sum_nonneg fun i _ => tailProb_nonneg μ (B i) t

lemma tailMean_antitone {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (B : Fin n → Ω → ℝ) : Antitone (tailMean μ B) := by
  intro s t hst
  exact Finset.sum_le_sum fun i _ => tailProb_antitone μ (B i) hst

lemma measurable_tailMean {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (B : Fin n → Ω → ℝ) : Measurable (tailMean μ B) :=
  (tailMean_antitone μ B).measurable

lemma integrable_posPart (μ : Measure Ω) [IsFiniteMeasure μ]
    {B : Ω → ℝ} (hB : Integrable B μ) (τ : ℝ) :
    Integrable (fun ω => max (B ω - τ) 0) μ :=
  (hB.sub (integrable_const τ)).sup (integrable_const 0)

lemma integrableOn_tailProb (μ : Measure Ω) [IsFiniteMeasure μ]
    {B : Ω → ℝ} (hBm : Measurable B) (hB : Integrable B μ) (τ : ℝ) :
    IntegrableOn (tailProb μ B) (Ioi τ) := by
  have hm : Measurable (fun t => μ {ω | t < B ω}) :=
    (show Antitone (fun t => μ {ω | t < B ω}) from
      fun s t hst => measure_mono fun ω hω => hst.trans_lt hω).measurable
  exact integrable_toReal_of_lintegral_ne_top hm.aemeasurable
    (by rw [← lintegral_posPart_eq_tail μ hBm τ]
        exact (integrable_posPart μ hB τ).lintegral_lt_top.ne)

/-- Real-valued (Bochner) form of the stop-loss tail formula. -/
theorem integral_posPart_eq_tail (μ : Measure Ω) [IsFiniteMeasure μ]
    {B : Ω → ℝ} (hBm : Measurable B) (hB : Integrable B μ) (τ : ℝ) :
    (∫ ω, max (B ω - τ) 0 ∂μ) = ∫ t in Ioi τ, tailProb μ B t := by
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun ω => max (B ω - τ) 0)
      (Eventually.of_forall fun ω => le_max_right _ _) (integrable_posPart μ hB τ).aestronglyMeasurable,
    lintegral_posPart_eq_tail μ hBm τ,
    integral_eq_lintegral_of_nonneg_ae (f := tailProb μ B)
      (Eventually.of_forall fun t => tailProb_nonneg μ B t)
      (measurable_tailProb μ B).aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro t
  exact (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm

lemma integrableOn_tailMean {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    {B : Fin n → Ω → ℝ} (hBm : ∀ i, Measurable (B i))
    (hB : ∀ i, Integrable (B i) μ) (τ : ℝ) :
    IntegrableOn (tailMean μ B) (Ioi τ) :=
  integrable_finset_sum _ fun i _ => integrableOn_tailProb μ (hBm i) (hB i) τ

/-- Sum of stop-loss expectations as the integral of the mean layer count. -/
theorem sum_integral_posPart_eq_tailMean {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    {B : Fin n → Ω → ℝ} (hBm : ∀ i, Measurable (B i))
    (hB : ∀ i, Integrable (B i) μ) (τ : ℝ) :
    (∑ i, ∫ ω, max (B i ω - τ) 0 ∂μ) = ∫ t in Ioi τ, tailMean μ B t := by
  simp_rw [integral_posPart_eq_tail μ (hBm _) (hB _) τ]
  exact (integral_finset_sum _ fun i _ => integrableOn_tailProb μ (hBm i) (hB i) τ).symm


/-- The deterministic-threshold relaxation of a family of random coordinates. -/
def thresholdRelaxation {n : ℕ} (μ : Measure Ω) (d : ℕ) (B : Fin n → Ω → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ τ : ℝ, 0 ≤ τ ∧
    v = (d : ℝ) * τ + ∑ i, ∫ ω, max (B i ω - τ) 0 ∂μ}

lemma tendsto_tailProb (μ : Measure Ω) [IsFiniteMeasure μ]
    {B : Ω → ℝ} (hB : Measurable B) :
    Tendsto (tailProb μ B) atTop (nhds 0) := by
  have hinter : (⋂ t : ℝ, {ω | t < B ω}) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false]
    exact fun h => (lt_irrefl (B ω)) (h (B ω))
  have hlim := tendsto_measure_iInter_atTop
    (μ := μ) (s := fun t : ℝ => {ω | t < B ω})
    (fun t => (measurableSet_lt measurable_const hB).nullMeasurableSet)
    (fun s t hst ω hω => hst.trans_lt hω)
    ⟨0, measure_ne_top μ _⟩
  rw [hinter, measure_empty] at hlim
  simpa [tailProb, Measure.real, Function.comp_def] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hlim

lemma tendsto_tailMean {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    {B : Fin n → Ω → ℝ} (hB : ∀ i, Measurable (B i)) :
    Tendsto (tailMean μ B) atTop (nhds 0) := by
  simpa [tailMean] using tendsto_finset_sum Finset.univ fun i _ => tendsto_tailProb μ (hB i)

/-- Every antitone tail vanishing at infinity crosses a positive level, allowing
    a jump at the crossing. No continuity assumption is needed. -/
lemma exists_antitone_crossing {m : ℝ → ℝ} (hm : Antitone m)
    (hlim : Tendsto m atTop (nhds 0)) {d : ℝ} (hd : 0 < d) :
    ∃ τ : ℝ, 0 ≤ τ ∧ (∀ t, 0 < t → t < τ → d ≤ m t) ∧
      (∀ t, τ < t → m t ≤ d) := by
  let S : Set ℝ := {t | 0 ≤ t ∧ d < m t}
  by_cases hS : S.Nonempty
  · obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually_lt_const hd)
    have hbdd : BddAbove S := by
      refine ⟨T, fun t ht => ?_⟩
      exact le_of_not_gt fun htt => (not_lt_of_ge (hT t htt.le).le) ht.2
    refine ⟨sSup S, ?_, ?_, ?_⟩
    · obtain ⟨t, ht⟩ := hS
      exact ht.1.trans (le_csSup hbdd ht)
    · intro t ht htτ
      obtain ⟨u, hu, htu⟩ := exists_lt_of_lt_csSup hS htτ
      exact hu.2.le.trans (hm htu.le)
    · intro t hτt
      by_contra htd
      have ht0 : 0 ≤ t := by
        obtain ⟨u, hu⟩ := hS
        exact hu.1.trans ((le_csSup hbdd hu).trans hτt.le)
      have htS : t ∈ S := ⟨ht0, lt_of_not_ge htd⟩
      exact (not_lt_of_ge (le_csSup hbdd htS)) hτt
  · refine ⟨0, le_rfl, fun t ht ht0 => (not_lt_of_ge ht.le ht0).elim, ?_⟩
    intro t ht
    by_contra htd
    exact hS ⟨t, ht.le, lt_of_not_ge htd⟩

end GaussianPCA
