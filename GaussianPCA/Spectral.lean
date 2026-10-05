import GaussianPCA.Gaussian

/-!
# The spectral bridge for arbitrary positive semidefinite covariance

This module proves that the concrete independent Gaussian model represents every
centered Gaussian law with a positive semidefinite covariance matrix. Eigenbases
come from mathlib's spectral theorem, rather than an extra diagonalization axiom.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators NNReal ENNReal

namespace GaussianPCA

/-- The centered diagonal Gaussian law determined by its eigenvalues. -/
def klMeasure {n : ℕ} (eig : Vector n) : Measure (Vector n) :=
  (gaussianMeasure n).map (klSample eig)

lemma measurable_klSample {n : ℕ} (eig : Vector n) : Measurable (klSample eig) := by
  unfold klSample
  fun_prop

lemma measurable_mulVec {n : ℕ} (U : CovarianceMatrix n) :
    Measurable (fun x : Vector n => U *ᵥ x) := by
  unfold Matrix.mulVec dotProduct
  fun_prop

instance {n : ℕ} (eig : Vector n) : IsProbabilityMeasure (klMeasure eig) := by
  unfold klMeasure
  exact Measure.isProbabilityMeasure_map (measurable_klSample eig).aemeasurable

lemma dot_mulVec_eq_transpose_mulVec_dot {n : ℕ}
    (a x : Vector n) (U : CovarianceMatrix n) :
    a ⬝ᵥ (U *ᵥ x) = (U.transpose *ᵥ a) ⬝ᵥ x := by
  rw [dotProduct_mulVec]
  congr 1
  simpa using Matrix.vecMul_transpose U.transpose a

lemma IsCenteredGaussian.isProbabilityMeasure {n : ℕ} {μ : Measure (Vector n)}
    {C : CovarianceMatrix n} (hμ : IsCenteredGaussian μ C) :
    IsProbabilityMeasure μ := by
  have h := congrArg (fun ν : Measure ℝ => ν Set.univ) (hμ 0)
  constructor
  simpa only [Measure.map_apply
    (show Measurable (fun x : Vector n => (0 : Vector n) ⬝ᵥ x) by fun_prop) MeasurableSet.univ,
    Set.preimage_univ, measure_univ] using h

lemma linearForm_eq_dot {n : ℕ} (L : Vector n →L[ℝ] ℝ) :
    ∀ x, L x = (fun i => L (Pi.single i 1)) ⬝ᵥ x := by
  intro x
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : Vector n) := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  calc
    L x = L (∑ i, x i • (Pi.single i (1 : ℝ) : Vector n)) := congrArg L hx
    _ = (fun i => L (Pi.single i 1)) ⬝ᵥ x := by
      simp [dotProduct, mul_comm]

lemma measure_eq_of_linear_projections {n : ℕ} {μ ν : Measure (Vector n)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ a : Vector n, μ.map (fun x => a ⬝ᵥ x) = ν.map (fun x => a ⬝ᵥ x)) : μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  have hL : (L : Vector n → ℝ) = fun x => (fun i => L (Pi.single i 1)) ⬝ᵥ x :=
    funext (linearForm_eq_dot L)
  rw [hL, h]

lemma IsCenteredGaussian.unique {n : ℕ} {μ ν : Measure (Vector n)}
    {C : CovarianceMatrix n} (hμ : IsCenteredGaussian μ C) (hν : IsCenteredGaussian ν C) :
    μ = ν := by
  letI := hμ.isProbabilityMeasure
  letI := hν.isProbabilityMeasure
  apply measure_eq_of_linear_projections
  intro a
  rw [hμ a, hν a]

lemma IsCenteredGaussian.map {n : ℕ} {μ : Measure (Vector n)}
    {C : CovarianceMatrix n} (hμ : IsCenteredGaussian μ C) (U : CovarianceMatrix n) :
    IsCenteredGaussian (μ.map (fun x => U *ᵥ x)) (U * C * U.transpose) := by
  intro a
  rw [Measure.map_map (by fun_prop) (measurable_mulVec U)]
  have hf : (fun x => a ⬝ᵥ x) ∘ (fun x => U *ᵥ x) =
      fun x => (U.transpose *ᵥ a) ⬝ᵥ x := by
    funext x
    exact dot_mulVec_eq_transpose_mulVec_dot a x U
  rw [hf, hμ]
  congr 2
  simp only [← Matrix.mulVec_mulVec, dot_mulVec_eq_transpose_mulVec_dot]

lemma isCenteredGaussian_klMeasure {n : ℕ} (eig : Vector n) (heig : ∀ i, 0 ≤ eig i) :
    IsCenteredGaussian (klMeasure eig) (Matrix.diagonal eig) := by
  intro a
  unfold klMeasure
  rw [Measure.map_map (by fun_prop) (measurable_klSample eig)]
  have hf : (fun x => a ⬝ᵥ x) ∘ klSample eig =
      fun z => ∑ i, (a i * Real.sqrt (eig i)) * z i := by
    funext z
    simp [dotProduct, klSample, mul_assoc]
  rw [hf, gaussianMeasure_map_linear]
  congr 1
  apply Subtype.ext
  change ((∑ i, ⟨(a i * Real.sqrt (eig i))^2, sq_nonneg _⟩ : ℝ≥0) : ℝ) = _
  rw [NNReal.coe_sum]
  change (∑ i, (a i * Real.sqrt (eig i))^2) =
    max (a ⬝ᵥ (Matrix.diagonal eig *ᵥ a)) 0
  have hnonneg : 0 ≤ a ⬝ᵥ (Matrix.diagonal eig *ᵥ a) := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_nonneg
    intro i _
    nlinarith [sq_nonneg (a i), heig i]
  rw [max_eq_left hnonneg]
  simp only [dotProduct, Matrix.mulVec_diagonal, mul_pow, Real.sq_sqrt (heig _)]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Eigenvalues of an arbitrary positive semidefinite real matrix. -/
def spectrumValues {n : ℕ} {C : CovarianceMatrix n} (hC : C.PosSemidef) : Vector n :=
  hC.isHermitian.eigenvalues

/-- The actual orthogonal eigenbasis furnished by the spectral theorem. -/
def eigenbasisMatrix {n : ℕ} {C : CovarianceMatrix n} (hC : C.PosSemidef) :
    CovarianceMatrix n := hC.isHermitian.eigenvectorUnitary

lemma spectrumValues_nonneg {n : ℕ} {C : CovarianceMatrix n} (hC : C.PosSemidef)
    (i : Fin n) : 0 ≤ spectrumValues hC i := hC.eigenvalues_nonneg i

lemma eigenbasisMatrix_isOrthogonal {n : ℕ} {C : CovarianceMatrix n}
    (hC : C.PosSemidef) : IsOrthogonal (eigenbasisMatrix hC) := by
  let Q := hC.isHermitian.eigenvectorUnitary
  have h1 := unitary.coe_mul_star_self Q
  have h2 := unitary.coe_star_mul_self Q
  constructor
  · simpa [eigenbasisMatrix, Q, Matrix.star_eq_conjTranspose] using h1
  · simpa [eigenbasisMatrix, Q, Matrix.star_eq_conjTranspose] using h2

lemma spectral_decomposition {n : ℕ} {C : CovarianceMatrix n}
    (hC : C.PosSemidef) :
    C = eigenbasisMatrix hC * Matrix.diagonal (spectrumValues hC) *
      (eigenbasisMatrix hC).transpose := by
  simpa [eigenbasisMatrix, spectrumValues, Matrix.star_eq_conjTranspose]
    using hC.isHermitian.spectral_theorem

lemma trace_eq_sum_spectrumValues {n : ℕ} {C : CovarianceMatrix n}
    (hC : C.PosSemidef) : Matrix.trace C = ∑ i, spectrumValues hC i := by
  simpa [spectrumValues] using hC.isHermitian.trace_eq_sum_eigenvalues

lemma rank_eq_card_positive_spectrumValues {n : ℕ} {C : CovarianceMatrix n}
    (hC : C.PosSemidef) :
    C.rank = (Finset.univ.filter fun i => 0 < spectrumValues hC i).card := by
  rw [hC.isHermitian.rank_eq_card_non_zero_eigs]
  simp only [Fintype.card_subtype, spectrumValues]
  congr 1
  apply Finset.filter_congr
  intro i _
  constructor
  · intro h
    exact lt_of_le_of_ne (hC.eigenvalues_nonneg i) (Ne.symm h)
  · exact ne_of_gt

/-- Every Gaussian law with covariance `C` is exactly the pushforward of the
independent KL model by an orthogonal eigenbasis. -/
lemma IsCenteredGaussian.eq_spectral_pushforward {n : ℕ} {μ : Measure (Vector n)}
    {C : CovarianceMatrix n} (hμ : IsCenteredGaussian μ C) (hC : C.PosSemidef) :
    μ = (klMeasure (spectrumValues hC)).map (fun x => eigenbasisMatrix hC *ᵥ x) := by
  apply hμ.unique
  have h := (isCenteredGaussian_klMeasure (spectrumValues hC)
    (spectrumValues_nonneg hC)).map (eigenbasisMatrix hC)
  rwa [← spectral_decomposition hC] at h

end GaussianPCA
