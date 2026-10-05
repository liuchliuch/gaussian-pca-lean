import GaussianPCA.Gaussian
import GaussianPCA.TopSum

/-!
# Retained-energy objectives and the deterministic upper relaxation

These definitions are genuine expectations on the product Gaussian probability
space. The supremum ranges over actual orthogonal matrices.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

namespace GaussianPCA

def klEnergy {n : ℕ} (d : ℕ) (eig : Vector n) : ℝ :=
  ∫ z, topSum d (fun i => (klSample eig z i)^2) ∂gaussianMeasure n

def rotatedEnergy {n : ℕ} (d : ℕ) (eig : Vector n) (U : CovarianceMatrix n) : ℝ :=
  ∫ z, topSum d (fun i => (rotatedSample U eig z i)^2) ∂gaussianMeasure n

def basisEnergyValues {n : ℕ} (d : ℕ) (eig : Vector n) : Set ℝ :=
  {v | ∃ U : CovarianceMatrix n, IsOrthogonal U ∧ v = rotatedEnergy d eig U}

def optEnergy {n : ℕ} (d : ℕ) (eig : Vector n) : ℝ := sSup (basisEnergyValues d eig)

def thresholdValues {n : ℕ} (d : ℕ) (eig : Vector n) : Set ℝ :=
  {v | ∃ τ : ℝ, 0 ≤ τ ∧ v = (d : ℝ)*τ + ∑ i, gaussianExcess (eig i) τ}

def thresholdEnergy {n : ℕ} (d : ℕ) (eig : Vector n) : ℝ := sInf (thresholdValues d eig)

def spectrumRank {n : ℕ} (eig : Vector n) : ℕ :=
  (Finset.univ.filter fun i => 0 < eig i).card

lemma klEnergy_nonneg {n : ℕ} (d : ℕ) (eig : Vector n) : 0 ≤ klEnergy d eig :=
  integral_nonneg fun _ => topSum_nonneg _ _

lemma rotatedEnergy_nonneg {n : ℕ} (d : ℕ) (eig : Vector n)
    (U : CovarianceMatrix n) : 0 ≤ rotatedEnergy d eig U :=
  integral_nonneg fun _ => topSum_nonneg _ _

lemma rotatedEnergy_one {n : ℕ} (d : ℕ) (eig : Vector n) :
    rotatedEnergy d eig (1 : CovarianceMatrix n) = klEnergy d eig := by
  simp [rotatedEnergy, klEnergy, rotatedSample]

lemma klEnergy_mem_basisEnergyValues {n : ℕ} (d : ℕ) (eig : Vector n) :
    klEnergy d eig ∈ basisEnergyValues d eig :=
  ⟨1, isOrthogonal_one n, (rotatedEnergy_one d eig).symm⟩

lemma basisEnergyValues_nonempty {n : ℕ} (d : ℕ) (eig : Vector n) :
    (basisEnergyValues d eig).Nonempty := ⟨_, klEnergy_mem_basisEnergyValues d eig⟩

lemma thresholdValues_nonempty {n : ℕ} (d : ℕ) (eig : Vector n) :
    (thresholdValues d eig).Nonempty := ⟨_, 0, le_rfl, rfl⟩

lemma thresholdValues_bddBelow {n : ℕ} (d : ℕ) (eig : Vector n) :
    BddBelow (thresholdValues d eig) := by
  refine ⟨0, ?_⟩
  rintro v ⟨τ, hτ, rfl⟩
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hτ)
    (Finset.sum_nonneg fun i _ => gaussianExcess_nonneg _ _)

lemma thresholdEnergy_nonneg {n : ℕ} (d : ℕ) (eig : Vector n) :
    0 ≤ thresholdEnergy d eig := by
  apply le_csInf (thresholdValues_nonempty d eig)
  rintro v ⟨τ, hτ, rfl⟩
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hτ)
    (Finset.sum_nonneg fun i _ => gaussianExcess_nonneg _ _)

lemma integrable_topSum_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} (d : ℕ) (X : Fin n → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (hi : ∀ i, Integrable (fun ω => (X i ω)^2) μ) :
    Integrable (fun ω => topSum d (fun i => (X i ω)^2)) μ := by
  have hs := integrable_finset_sum Finset.univ (fun i _ => hi i)
  apply hs.mono' ((continuous_topSum d).measurable.comp
    (measurable_pi_lambda _ fun i => (hm i).pow_const 2)).aestronglyMeasurable
  filter_upwards [] with ω
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (topSum_nonneg _ _)]
  exact topSum_le_sum _ _ (fun _ => sq_nonneg _)

lemma measurable_rotated_coordinate {n : ℕ} (U : CovarianceMatrix n)
    (eig : Vector n) (i : Fin n) : Measurable (fun z => rotatedSample U eig z i) := by
  unfold rotatedSample klSample Matrix.mulVec dotProduct
  fun_prop

lemma integrable_rotated_sq {n : ℕ} (U : CovarianceMatrix n)
    (eig : Vector n) (heig : ∀ i, 0 ≤ eig i) (i : Fin n) :
    Integrable (fun z => (rotatedSample U eig z i)^2) (gaussianMeasure n) := by
  exact (memLp_of_gaussianLaw (measurable_rotated_coordinate U eig i)
    (gaussianMeasure_map_rotatedSample_coordinate U eig heig i) 2 (by norm_num)).integrable_sq

lemma integrable_rotated_topSum {n : ℕ} (d : ℕ) (U : CovarianceMatrix n)
    (eig : Vector n) (heig : ∀ i, 0 ≤ eig i) :
    Integrable (fun z => topSum d (fun i => (rotatedSample U eig z i)^2))
      (gaussianMeasure n) :=
  integrable_topSum_sq d _ (measurable_rotated_coordinate U eig) (integrable_rotated_sq U eig heig)

lemma rotatedEnergy_le_threshold_value {n : ℕ} (d : ℕ) (eig : Vector n)
    (heig : ∀ i, 0 ≤ eig i) (U : CovarianceMatrix n) (hU : IsOrthogonal U)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    rotatedEnergy d eig U ≤ (d : ℝ)*τ + ∑ i, gaussianExcess (eig i) τ := by
  have hi (i : Fin n) : Integrable
      (fun z => max ((rotatedSample U eig z i)^2 - τ) 0) (gaussianMeasure n) :=
    ((integrable_rotated_sq U eig heig i).sub (integrable_const τ)).sup (integrable_const 0)
  calc
    rotatedEnergy d eig U ≤ ∫ z, (d : ℝ)*τ +
        ∑ i, max ((rotatedSample U eig z i)^2 - τ) 0 ∂gaussianMeasure n := by
      exact integral_mono (integrable_rotated_topSum d U eig heig)
        ((integrable_const _).add (integrable_finset_sum _ fun i _ => hi i))
        (fun z => topSum_le_threshold d _ hτ)
    _ = (d : ℝ)*τ + ∑ i, gaussianExcess (rotatedVariance U eig i) τ := by
      rw [integral_add (integrable_const _) (integrable_finset_sum _ fun i _ => hi i),
        integral_finset_sum _ (fun i _ => hi i)]
      simp only [integral_const, measureReal_univ_eq_one, one_smul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact integral_excess_of_gaussianLaw (rotatedVariance_nonneg U eig heig i)
        (measurable_rotated_coordinate U eig i)
        (gaussianMeasure_map_rotatedSample_coordinate U eig heig i) τ
    _ ≤ (d : ℝ)*τ + ∑ i, gaussianExcess (eig i) τ :=
      add_le_add_left (hU.sum_convex_rotatedVariance_le eig heig _ (gaussianExcess_convex τ)) _

theorem rotatedEnergy_le_thresholdEnergy {n : ℕ} (d : ℕ) (eig : Vector n)
    (heig : ∀ i, 0 ≤ eig i) (U : CovarianceMatrix n) (hU : IsOrthogonal U) :
    rotatedEnergy d eig U ≤ thresholdEnergy d eig := by
  apply le_csInf (thresholdValues_nonempty d eig)
  rintro v ⟨τ, hτ, rfl⟩
  exact rotatedEnergy_le_threshold_value d eig heig U hU τ hτ

lemma basisEnergyValues_bddAbove {n : ℕ} (d : ℕ) (eig : Vector n)
    (heig : ∀ i, 0 ≤ eig i) : BddAbove (basisEnergyValues d eig) := by
  refine ⟨thresholdEnergy d eig, ?_⟩
  rintro v ⟨U, hU, rfl⟩
  exact rotatedEnergy_le_thresholdEnergy d eig heig U hU

theorem klEnergy_le_optEnergy {n : ℕ} (d : ℕ) (eig : Vector n)
    (heig : ∀ i, 0 ≤ eig i) : klEnergy d eig ≤ optEnergy d eig :=
  le_csSup (basisEnergyValues_bddAbove d eig heig) (klEnergy_mem_basisEnergyValues d eig)

theorem optEnergy_le_thresholdEnergy {n : ℕ} (d : ℕ) (eig : Vector n)
    (heig : ∀ i, 0 ≤ eig i) : optEnergy d eig ≤ thresholdEnergy d eig := by
  apply csSup_le (basisEnergyValues_nonempty d eig)
  rintro v ⟨U, hU, rfl⟩
  exact rotatedEnergy_le_thresholdEnergy d eig heig U hU

lemma thresholdEnergy_le_trace {n : ℕ} (d : ℕ) (eig : Vector n)
    (heig : ∀ i, 0 ≤ eig i) : thresholdEnergy d eig ≤ ∑ i, eig i := by
  apply csInf_le (thresholdValues_bddBelow d eig)
  refine ⟨0, le_rfl, ?_⟩
  simp only [mul_zero, zero_add]
  exact Finset.sum_congr rfl (fun i _ => (gaussianExcess_zero_threshold (heig i)).symm)

lemma integral_kl_sq {n : ℕ} (eig : Vector n) (heig : ∀ i, 0 ≤ eig i) (i : Fin n) :
    (∫ z, (klSample eig z i)^2 ∂gaussianMeasure n) = eig i := by
  have h := integral_kl_excess eig heig i 0
  simpa only [sub_zero, max_eq_left (sq_nonneg _), gaussianExcess_zero_threshold (heig i)] using h

lemma integrable_kl_sq {n : ℕ} (eig : Vector n) (heig : ∀ i, 0 ≤ eig i) (i : Fin n) :
    Integrable (fun z => (klSample eig z i)^2) (gaussianMeasure n) := by
  simpa [rotatedSample] using integrable_rotated_sq (1 : CovarianceMatrix n) eig heig i

theorem klEnergy_eq_trace_of_rank_le {n : ℕ} (d : ℕ) (eig : Vector n)
    (heig : ∀ i, 0 ≤ eig i) (hr : spectrumRank eig ≤ d) : klEnergy d eig = ∑ i, eig i := by
  have hpoint (z : Vector n) : topSum d (fun i => (klSample eig z i)^2) =
      ∑ i, (klSample eig z i)^2 := by
    apply topSum_eq_sum_of_support_card_le d _ (fun i => sq_nonneg _)
    apply le_trans (Finset.card_le_card ?_) hr
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hne : eig i ≠ 0 := by
      intro hzero
      apply hi
      simp [klSample, hzero]
    exact lt_of_le_of_ne (heig i) (Ne.symm hne)
  unfold klEnergy
  simp_rw [hpoint]
  rw [integral_finset_sum _ (fun i _ => integrable_kl_sq eig heig i)]
  exact Finset.sum_congr rfl (fun i _ => integral_kl_sq eig heig i)

theorem optEnergy_eq_trace_of_rank_le {n : ℕ} (d : ℕ) (eig : Vector n)
    (heig : ∀ i, 0 ≤ eig i) (hr : spectrumRank eig ≤ d) : optEnergy d eig = ∑ i, eig i := by
  apply le_antisymm ((optEnergy_le_thresholdEnergy d eig heig).trans
    (thresholdEnergy_le_trace d eig heig))
  rw [← klEnergy_eq_trace_of_rank_le d eig heig hr]
  exact klEnergy_le_optEnergy d eig heig

end GaussianPCA
