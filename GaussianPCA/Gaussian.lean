import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

/-!
# Gaussian data and covariance semantics

The sample space is the finite product of real standard Gaussian measures.
General centered Gaussian data are specified by the distributions of all real
linear forms, including singular covariance matrices.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators NNReal ENNReal

namespace GaussianPCA

abbrev Vector (n : ℕ) := Fin n → ℝ
abbrev CovarianceMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The genuine product probability measure of independent standard Gaussians. -/
def gaussianMeasure (n : ℕ) : Measure (Vector n) :=
  Measure.pi fun _ => gaussianReal 0 1

instance (n : ℕ) : IsProbabilityMeasure (gaussianMeasure n) := by
  unfold gaussianMeasure
  infer_instance

/-- Coordinates in a Karhunen–Loève basis, for a specified nonnegative spectrum. -/
def klSample {n : ℕ} (eig : Vector n) (z : Vector n) : Vector n :=
  fun i => Real.sqrt (eig i) * z i

/-- The sample after changing basis by an orthogonal row-coordinate matrix. -/
def rotatedSample {n : ℕ} (U : CovarianceMatrix n) (eig : Vector n)
    (z : Vector n) : Vector n := U *ᵥ klSample eig z

/-- Orthogonality is an actual matrix identity, with both directions recorded. -/
def IsOrthogonal {n : ℕ} (U : CovarianceMatrix n) : Prop :=
  U * U.transpose = 1 ∧ U.transpose * U = 1

/-- Multivariate centered Gaussian semantics via all linear projections. -/
def IsCenteredGaussian {n : ℕ} (μ : Measure (Vector n))
    (C : CovarianceMatrix n) : Prop :=
  ∀ a : Vector n,
    μ.map (fun x => a ⬝ᵥ x) =
      gaussianReal 0 (Real.toNNReal (a ⬝ᵥ (C *ᵥ a)))

/-- The variance vector of an orthogonal transform of a diagonal covariance. -/
def rotatedVariance {n : ℕ} (U : CovarianceMatrix n) (eig : Vector n) : Vector n :=
  fun i => ∑ j, (U i j) ^ 2 * eig j

/-- One-dimensional stop-loss transform used by the threshold relaxation. -/
def gaussianExcess (variance threshold : ℝ) : ℝ :=
  ∫ z, max (variance * z ^ 2 - threshold) 0 ∂gaussianReal 0 1

lemma gaussianMeasure_map_eval {n : ℕ} (i : Fin n) :
    (gaussianMeasure n).map (fun x => x i) = gaussianReal 0 1 := by
  exact (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq

lemma independent_gaussian_coordinates (n : ℕ) :
    iIndepFun (fun (i : Fin n) (x : Vector n) => x i) (gaussianMeasure n) := by
  exact iIndepFun_pi fun _ => measurable_id.aemeasurable

lemma independent_kl_coordinates {n : ℕ} (eig : Vector n) :
    iIndepFun (fun i z => klSample eig z i) (gaussianMeasure n) := by
  exact iIndepFun_pi fun i => (measurable_id.const_mul (Real.sqrt (eig i))).aemeasurable

lemma klSample_sq {n : ℕ} (eig : Vector n) (heig : ∀ i, 0 ≤ eig i)
    (z : Vector n) (i : Fin n) : (klSample eig z i)^2 = eig i * (z i)^2 := by
  rw [klSample, mul_pow, Real.sq_sqrt (heig i)]

lemma gaussianReal_map_sqrt {v : ℝ} (hv : 0 ≤ v) :
    (gaussianReal 0 1).map (fun z => Real.sqrt v * z) = gaussianReal 0 v.toNNReal := by
  rw [gaussianReal_map_const_mul]
  have hs : (⟨(Real.sqrt v)^2, sq_nonneg _⟩ : ℝ≥0) = v.toNNReal := by
    apply Subtype.ext
    simp [Real.sq_sqrt hv, Real.toNNReal_of_nonneg hv]
  simp [hs]

lemma gaussianMeasure_map_klSample_coordinate {n : ℕ} (eig : Vector n)
    (heig : ∀ i, 0 ≤ eig i) (i : Fin n) :
    (gaussianMeasure n).map (fun z => klSample eig z i) =
      gaussianReal 0 (Real.toNNReal (eig i)) := by
  change (gaussianMeasure n).map ((fun z => Real.sqrt (eig i) * z) ∘ (fun z => z i)) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), gaussianMeasure_map_eval,
    gaussianReal_map_sqrt (heig i)]

/-- Finite independent sums have the expected Gaussian law, proved from the
binary convolution theorem rather than postulated as a distributional axiom. -/
lemma gaussianReal_finset_sum {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hX : iIndepFun X μ) (hXm : ∀ i, Measurable (X i))
    (mean : ι → ℝ) (variance : ι → ℝ≥0)
    (hLaw : ∀ i, μ.map (X i) = gaussianReal (mean i) (variance i))
    (s : Finset ι) :
    μ.map (fun x => ∑ i ∈ s, X i x) =
      gaussianReal (∑ i ∈ s, mean i) (∑ i ∈ s, variance i) := by
  have hfun (t : Finset ι) : (fun x => ∑ j ∈ t, X j x) = ∑ j ∈ t, X j := by
    funext x
    simp
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hInd := (hX.indepFun_finset_sum_of_notMem hXm hi).symm
    have ih' : μ.map (∑ j ∈ s, X j) =
        gaussianReal (∑ j ∈ s, mean j) (∑ j ∈ s, variance j) := by
      rw [← hfun]
      exact ih
    have h := gaussianReal_add_gaussianReal_of_indepFun hInd (hLaw i) ih'
    rw [hfun, Finset.sum_insert hi]
    simpa [Finset.sum_insert hi] using h

lemma gaussianMeasure_map_linear {n : ℕ} (a : Vector n) :
    (gaussianMeasure n).map (fun z => ∑ i, a i * z i) =
      gaussianReal 0 (∑ i, ⟨(a i)^2, sq_nonneg _⟩) := by
  have hInd : iIndepFun (fun i z => a i * z i) (gaussianMeasure n) :=
    iIndepFun_pi fun i => (measurable_id.const_mul (a i)).aemeasurable
  have hLaw (i : Fin n) :
      (gaussianMeasure n).map (fun z => a i * z i) =
        gaussianReal 0 ⟨(a i)^2, sq_nonneg _⟩ := by
    change (gaussianMeasure n).map ((fun z => a i * z) ∘ (fun z => z i)) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop), gaussianMeasure_map_eval,
      gaussianReal_map_const_mul]
    simp
  simpa using gaussianReal_finset_sum hInd (fun i => by fun_prop)
    (fun _ => 0) (fun i => ⟨(a i)^2, sq_nonneg _⟩) hLaw Finset.univ

lemma gaussianMeasure_map_rotatedSample_coordinate {n : ℕ}
    (U : CovarianceMatrix n) (eig : Vector n) (heig : ∀ i, 0 ≤ eig i) (i : Fin n) :
    (gaussianMeasure n).map (fun z => rotatedSample U eig z i) =
      gaussianReal 0 (Real.toNNReal (rotatedVariance U eig i)) := by
  have h := gaussianMeasure_map_linear (fun j => U i j * Real.sqrt (eig j))
  have hv : (∑ j : Fin n, ⟨(U i j * Real.sqrt (eig j))^2, sq_nonneg _⟩ : ℝ≥0) =
      (rotatedVariance U eig i).toNNReal := by
    apply Subtype.ext
    change ((∑ j : Fin n, ⟨(U i j * Real.sqrt (eig j))^2, sq_nonneg _⟩ : ℝ≥0) : ℝ) = _
    rw [NNReal.coe_sum]
    unfold rotatedVariance
    have hnonneg : 0 ≤ ∑ j : Fin n, U i j ^ 2 * eig j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg (U i j)) (heig j)
    change (∑ j : Fin n, (U i j * Real.sqrt (eig j))^2) =
      max (∑ j : Fin n, U i j^2 * eig j) 0
    rw [max_eq_left hnonneg]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_pow (U i j) (Real.sqrt (eig j)) 2 |>.trans (by rw [Real.sq_sqrt (heig j)])
  rw [hv] at h
  convert h using 1
  congr 1
  funext z
  simp [rotatedSample, Matrix.mulVec, dotProduct, klSample, mul_assoc]

lemma memLp_of_gaussianLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0} (hX : Measurable X)
    (hLaw : μ.map X = gaussianReal m v) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp X p μ := by
  have h := memLp_id_gaussianReal' (μ := m) (v := v) p hp
  rw [← hLaw] at h
  simpa using h.comp_of_map hX.aemeasurable

lemma integrable_sq_gaussian (m : ℝ) (v : ℝ≥0) :
    Integrable (fun z : ℝ => z^2) (gaussianReal m v) :=
  (memLp_id_gaussianReal' 2 (by norm_num)).integrable_sq

lemma integral_sq_standardGaussian :
    (∫ z : ℝ, z^2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_eq_integral (μ := gaussianReal 0 1)
    (X := fun z : ℝ => z) measurable_id.aemeasurable
  simpa using h.symm

lemma integrable_gaussianExcess (v τ : ℝ) :
    Integrable (fun z : ℝ => max (v * z^2 - τ) 0) (gaussianReal 0 1) := by
  exact (((integrable_sq_gaussian 0 1).const_mul v).sub (integrable_const τ)).sup
    (integrable_const 0)

lemma gaussianExcess_nonneg (v τ : ℝ) : 0 ≤ gaussianExcess v τ :=
  integral_nonneg fun _ => le_max_right _ _

lemma gaussianExcess_zero_threshold {v : ℝ} (hv : 0 ≤ v) :
    gaussianExcess v 0 = v := by
  unfold gaussianExcess
  simp_rw [sub_zero, max_eq_left (mul_nonneg hv (sq_nonneg _))]
  rw [integral_const_mul, integral_sq_standardGaussian, mul_one]

lemma gaussianExcess_zero_variance {τ : ℝ} (hτ : 0 ≤ τ) :
    gaussianExcess 0 τ = 0 := by
  simp [gaussianExcess, max_eq_right (neg_nonpos.mpr hτ)]

lemma gaussianExcess_convex (τ : ℝ) :
    ConvexOn ℝ (Set.Ici 0) (fun v => gaussianExcess v τ) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro u hu v hv a b ha hb hab
  simp only [smul_eq_mul]
  have hint := ((integrable_gaussianExcess u τ).const_mul a).add
    ((integrable_gaussianExcess v τ).const_mul b)
  calc
    gaussianExcess (a*u+b*v) τ ≤
      ∫ z : ℝ, a * max (u*z^2-τ) 0 + b * max (v*z^2-τ) 0 ∂gaussianReal 0 1 := by
      apply integral_mono (integrable_gaussianExcess _ _) hint
      intro z
      change max ((a*u+b*v)*z^2-τ) 0 ≤ a*max (u*z^2-τ) 0 + b*max (v*z^2-τ) 0
      apply max_le
      · have h1 := mul_le_mul_of_nonneg_left (le_max_left (u*z^2-τ) 0) ha
        have h2 := mul_le_mul_of_nonneg_left (le_max_left (v*z^2-τ) 0) hb
        nlinarith [congrArg (fun t : ℝ => t*τ) hab]
      · exact add_nonneg (mul_nonneg ha (le_max_right _ _))
          (mul_nonneg hb (le_max_right _ _))
    _ = a * gaussianExcess u τ + b * gaussianExcess v τ := by
      rw [integral_add ((integrable_gaussianExcess u τ).const_mul a)
        ((integrable_gaussianExcess v τ).const_mul b)]
      simp only [integral_const_mul, gaussianExcess]

lemma integral_excess_of_gaussianLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {v : ℝ} (hv : 0 ≤ v)
    (hX : Measurable X) (hLaw : μ.map X = gaussianReal 0 v.toNNReal) (τ : ℝ) :
    (∫ x, max ((X x)^2 - τ) 0 ∂μ) = gaussianExcess v τ := by
  rw [← integral_map hX.aemeasurable
      (f := fun y : ℝ => max (y^2-τ) 0) (by fun_prop), hLaw,
    ← gaussianReal_map_sqrt hv, integral_map (by fun_prop) (by fun_prop)]
  simp [gaussianExcess, mul_pow, Real.sq_sqrt hv]

lemma integral_kl_excess {n : ℕ} (eig : Vector n) (heig : ∀ i, 0 ≤ eig i)
    (i : Fin n) (τ : ℝ) :
    (∫ z, max ((klSample eig z i)^2 - τ) 0 ∂gaussianMeasure n) =
      gaussianExcess (eig i) τ := by
  apply integral_excess_of_gaussianLaw (heig i)
  · unfold klSample
    fun_prop
  · exact gaussianMeasure_map_klSample_coordinate eig heig i

lemma isOrthogonal_one (n : ℕ) : IsOrthogonal (1 : CovarianceMatrix n) := by
  simp [IsOrthogonal]

lemma IsOrthogonal.row_square_sum {n : ℕ} {U : CovarianceMatrix n}
    (hU : IsOrthogonal U) (i : Fin n) : ∑ j, (U i j)^2 = 1 := by
  have h := congrFun (congrFun hU.1 i) i
  simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h

lemma IsOrthogonal.column_square_sum {n : ℕ} {U : CovarianceMatrix n}
    (hU : IsOrthogonal U) (j : Fin n) : ∑ i, (U i j)^2 = 1 := by
  have h := congrFun (congrFun hU.2 j) j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h

lemma rotatedVariance_nonneg {n : ℕ} (U : CovarianceMatrix n) (eig : Vector n)
    (heig : ∀ i, 0 ≤ eig i) (i : Fin n) : 0 ≤ rotatedVariance U eig i := by
  exact Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (heig j)

lemma IsOrthogonal.sum_rotatedVariance {n : ℕ} {U : CovarianceMatrix n}
    (hU : IsOrthogonal U) (eig : Vector n) :
    ∑ i, rotatedVariance U eig i = ∑ i, eig i := by
  unfold rotatedVariance
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hU.column_square_sum, one_mul]

/-- The finite-dimensional Schur/Jensen step, using the squared entries of the
orthogonal matrix as a doubly stochastic matrix. -/
lemma IsOrthogonal.sum_convex_rotatedVariance_le {n : ℕ} {U : CovarianceMatrix n}
    (hU : IsOrthogonal U) (eig : Vector n) (heig : ∀ i, 0 ≤ eig i)
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f) :
    ∑ i, f (rotatedVariance U eig i) ≤ ∑ i, f (eig i) := by
  calc
    _ ≤ ∑ i, ∑ j, (U i j)^2 * f (eig j) := by
      apply Finset.sum_le_sum
      intro i _
      simpa [rotatedVariance, smul_eq_mul] using
        hf.map_sum_le (t := Finset.univ) (w := fun j => (U i j)^2)
          (p := eig) (fun j _ => sq_nonneg _) (hU.row_square_sum i)
          (fun j _ => heig j)
    _ = ∑ j, f (eig j) := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hU.column_square_sum, one_mul]

end GaussianPCA
