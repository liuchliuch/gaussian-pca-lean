import GaussianPCA.Objective
import GaussianPCA.LayerCakeComparison
import GaussianPCA.CorrelationGap

/-!
# Gaussian layer-cake comparison, including singular covariance

The finite-rank correlation gap is applied on precisely the positive-variance
coordinates. Coordinates with zero eigenvalue have zero energy identically,
so no positive-definiteness assumption is introduced by the reduction.
-/

noncomputable section
open scoped ENNReal BigOperators
open Set MeasureTheory ProbabilityTheory

namespace GaussianPCA

/-- The coordinate energy of a genuine KL Gaussian sample. -/
def gaussianEnergyCoordinate {n : ℕ} (eig : Vector n) (i : Fin n) (z : Vector n) : ℝ :=
  (klSample eig z i)^2

lemma measurable_gaussianEnergyCoordinate {n : ℕ} (eig : Vector n) (i : Fin n) :
    Measurable (gaussianEnergyCoordinate eig i) := by
  unfold gaussianEnergyCoordinate klSample
  fun_prop

lemma gaussianEnergyCoordinate_nonneg {n : ℕ} (eig : Vector n) (i : Fin n) (z : Vector n) :
    0 ≤ gaussianEnergyCoordinate eig i z := sq_nonneg _

lemma integrable_gaussianEnergyCoordinate {n : ℕ} (eig : Vector n)
    (heig : ∀ i, 0 ≤ eig i) (i : Fin n) :
    Integrable (gaussianEnergyCoordinate eig i) (gaussianMeasure n) := by
  exact (memLp_of_gaussianLaw (by unfold klSample; fun_prop)
    (gaussianMeasure_map_klSample_coordinate eig heig i) 2 (by norm_num)).integrable_sq

lemma independent_gaussianEnergyCoordinates {n : ℕ} (eig : Vector n) :
    iIndepFun (gaussianEnergyCoordinate eig) (gaussianMeasure n) := by
  exact (independent_kl_coordinates eig).comp (fun _ (x : ℝ) => x^2) (fun _ => by fun_prop)

lemma gaussianEnergyCoordinate_eq_zero {n : ℕ} (eig : Vector n) {i : Fin n}
    (hi : eig i = 0) (z : Vector n) : gaussianEnergyCoordinate eig i z = 0 := by
  simp [gaussianEnergyCoordinate, klSample, hi]

lemma gaussian_layerCount_support {n : ℕ} (eig : Vector n) (heig : ∀ i, 0 ≤ eig i)
    {t : ℝ} (ht : 0 ≤ t) (z : Vector n) :
    ((Finset.univ.filter fun i => 0 < eig i).filter
      fun i => t < gaussianEnergyCoordinate eig i z).card =
      layerCount (gaussianEnergyCoordinate eig) t z := by
  congr 1
  ext i
  by_cases hi : 0 < eig i
  · simp [hi]
  · have hi0 : eig i = 0 := le_antisymm (le_of_not_gt hi) (heig i)
    simp [hi, gaussianEnergyCoordinate_eq_zero eig hi0,
      not_lt_of_ge ht]

lemma gaussian_tailMean_support {n : ℕ} (eig : Vector n) (heig : ∀ i, 0 ≤ eig i)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ i ∈ Finset.univ.filter (fun i => 0 < eig i),
      (gaussianMeasure n).real {z | t < gaussianEnergyCoordinate eig i z}) =
      tailMean (gaussianMeasure n) (gaussianEnergyCoordinate eig) t := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hinot
  have hi0 : eig i = 0 := by
    apply le_antisymm _ (heig i)
    simpa using hinot
  simp [gaussianEnergyCoordinate_eq_zero eig hi0, not_lt_of_ge ht]

lemma thresholdRelaxation_gaussian_eq {n : ℕ} (d : ℕ) (eig : Vector n)
    (heig : ∀ i, 0 ≤ eig i) :
    thresholdRelaxation (gaussianMeasure n) d (gaussianEnergyCoordinate eig) =
      thresholdEnergy d eig := by
  unfold thresholdRelaxation thresholdEnergy thresholdValues gaussianEnergyCoordinate
  simp_rw [integral_kl_excess eig heig]

/-- Lemma 6: the sharp finite-rank layer-cake comparison, with all Gaussian,
    independence, integrability, and threshold identities proved explicitly. -/
theorem klEnergy_ge_finiteRankConstant_mul_thresholdEnergy {n : ℕ}
    (d : ℕ) (eig : Vector n) (heig : ∀ i, 0 ≤ eig i)
    (hd : 1 ≤ d) (hdr : d < spectrumRank eig) :
    finiteRankConstant d (spectrumRank eig) * thresholdEnergy d eig ≤ klEnergy d eig := by
  have hgap (t : ℝ) (ht : 0 < t) :
      finiteRankConstant d (spectrumRank eig) *
        min (d : ℝ) (tailMean (gaussianMeasure n) (gaussianEnergyCoordinate eig) t) ≤
      ∫ z, min (d : ℝ) (layerCount (gaussianEnergyCoordinate eig) t z : ℝ)
        ∂gaussianMeasure n := by
    have h := independent_level_rank_bound_finset
      (measurable_gaussianEnergyCoordinate eig) (independent_gaussianEnergyCoordinates eig)
      (Finset.univ.filter fun i => 0 < eig i) t d hd hdr
    simpa only [gaussian_tailMean_support eig heig ht.le,
      gaussian_layerCount_support eig heig ht.le, spectrumRank] using h
  have h := integral_topSum_ge_threshold_of_layer_bound (gaussianMeasure n)
    (B := gaussianEnergyCoordinate eig) (by omega : 0 < d)
    (measurable_gaussianEnergyCoordinate eig) (integrable_gaussianEnergyCoordinate eig heig)
    (gaussianEnergyCoordinate_nonneg eig) (finiteRankConstant d (spectrumRank eig)) hgap
  rw [thresholdRelaxation_gaussian_eq d eig heig] at h
  exact h

end GaussianPCA
