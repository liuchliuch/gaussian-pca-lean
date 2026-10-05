import GaussianPCA.CorrelationGapSmoothing
import GaussianPCA.CorrelationGapProbability
import GaussianPCA.BinomialRank

open scoped BigOperators
open Finset Set MeasureTheory ProbabilityTheory

noncomputable section

namespace GaussianPCA

/-- Equal Bernoulli probabilities give the recursively defined binomial law. -/
theorem bernoulliExpectation_constant_probability {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ℝ) (f : ℕ → ℝ) :
    bernoulliExpectation (fun _ : ι => p) s f = binomialExpectation s.card p f := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | @insert i s hi ih =>
    rw [bernoulliExpectation_insert _ hi, Finset.card_insert_of_notMem hi,
      binomialExpectation_succ, ih, ih]

/-- The extremal equal-probability vector attains the exact coefficient. -/
theorem bernoulliExpectation_uniform_exact {r : ℕ} (d : ℕ)
    (hd : 1 ≤ d) (hdr : d < r) :
    bernoulliExpectation (fun _ : Fin r => (d : ℝ) / r) Finset.univ
      (fun n => min (d : ℝ) (n : ℝ)) = (d : ℝ) * finiteRankConstant d r := by
  rw [bernoulliExpectation_constant_probability]
  simpa only [Finset.card_univ, Fintype.card_fin, binomialRank] using
    binomialRank_eq_finiteRankConstant d r hd hdr

/-- The sharp uniform-matroid correlation-gap inequality for a finite family
of independent Bernoulli probabilities. -/
theorem finiteRankConstant_mul_min_le_bernoulliExpectation_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ℕ) (hd : 1 ≤ d) (hdr : d < Fintype.card ι)
    {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    finiteRankConstant d (Fintype.card ι) * min (d : ℝ) (∑ i, q i) ≤
      bernoulliExpectation q Finset.univ (fun n => min (d : ℝ) (n : ℝ)) := by
  have hr : 0 < Fintype.card ι := by omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hr
  let p : ℝ := (∑ i, q i) / Fintype.card ι
  have hrR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hr
  have hp0 : 0 ≤ p := div_nonneg (Finset.sum_nonneg (fun i _ => (hq i).1)) hrR.le
  have hp1 : p ≤ 1 := by
    apply (div_le_one hrR).mpr
    calc
      ∑ i, q i ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hq i).2)
      _ = (Fintype.card ι : ℝ) := by simp
  have hsum : ∑ i, q i = (Fintype.card ι : ℝ) * p := by
    dsimp [p]
    field_simp
  have hdiag := bernoulliExpectation_diagonal_le
    (q := q) (p := p) ⟨fun i => (hq i).1, fun i => (hq i).2⟩
    (by simpa using hsum) (f := fun n => min (d : ℝ) (n : ℝ))
    (fun n => by simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
      min_nat_second_difference_nonpos d n)
  rw [bernoulliExpectation_constant_probability] at hdiag
  simp only [Finset.card_univ] at hdiag
  calc
    finiteRankConstant d (Fintype.card ι) * min (d : ℝ) (∑ i, q i) =
        finiteRankConstant d (Fintype.card ι) * min (d : ℝ) ((Fintype.card ι : ℝ) * p) := by rw [← hsum]
    _ ≤ binomialRank d (Fintype.card ι) p :=
      finiteRankConstant_mul_min_le_binomialRank d (Fintype.card ι) hd hdr hp0 hp1
    _ ≤ _ := hdiag

theorem finiteRankConstant_mul_min_le_bernoulliExpectation
    {r : ℕ} (d : ℕ) (hd : 1 ≤ d) (hdr : d < r)
    {q : Fin r → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    finiteRankConstant d r * min (d : ℝ) (∑ i, q i) ≤
      bernoulliExpectation q Finset.univ (fun n => min (d : ℝ) (n : ℝ)) := by
  simpa only [Fintype.card_fin] using
    finiteRankConstant_mul_min_le_bernoulliExpectation_fintype d hd (by simpa using hdr) hq

/-- Lemma 5 of the paper, for actual independent measurable Bernoulli events
on an arbitrary probability space. -/
theorem uniformMatroid_bernoulli_bound_fintype {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : ι → Set Ω} (hs : ∀ i, MeasurableSet (s i))
    (hind : iIndepSet s μ) (d : ℕ) (hd : 1 ≤ d) (hdr : d < Fintype.card ι) :
    finiteRankConstant d (Fintype.card ι) * min (d : ℝ) (∑ i, μ.real (s i)) ≤
      ∫ ω, min (d : ℝ) ((bernoulliSelected s ω).card : ℝ) ∂μ := by
  rw [integral_bernoulliSelected hs hind (fun n => min (d : ℝ) (n : ℝ))]
  exact finiteRankConstant_mul_min_le_bernoulliExpectation_fintype d hd hdr
    (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩)

theorem uniformMatroid_bernoulli_bound {r : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : Fin r → Set Ω} (hs : ∀ i, MeasurableSet (s i))
    (hind : iIndepSet s μ) (d : ℕ) (hd : 1 ≤ d) (hdr : d < r) :
    finiteRankConstant d r * min (d : ℝ) (∑ i, μ.real (s i)) ≤
      ∫ ω, min (d : ℝ) ((bernoulliSelected s ω).card : ℝ) ∂μ := by
  rw [integral_bernoulliSelected hs hind (fun n => min (d : ℝ) (n : ℝ))]
  exact finiteRankConstant_mul_min_le_bernoulliExpectation d hd hdr
    (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩)

/-- Equality in the Bernoulli bound when every success probability is `d/r`.
This also identifies the sharpness witness at the level of actual random events. -/
theorem uniformMatroid_bernoulli_exact {r : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : Fin r → Set Ω} (hs : ∀ i, MeasurableSet (s i))
    (hind : iIndepSet s μ) (d : ℕ) (hd : 1 ≤ d) (hdr : d < r)
    (hq : ∀ i, μ.real (s i) = (d : ℝ) / r) :
    (∫ ω, min (d : ℝ) ((bernoulliSelected s ω).card : ℝ) ∂μ) =
      (d : ℝ) * finiteRankConstant d r := by
  rw [integral_bernoulliSelected hs hind (fun n => min (d : ℝ) (n : ℝ))]
  have hprob : (fun i => μ.real (s i)) = fun _ : Fin r => (d : ℝ) / r :=
    funext hq
  rw [hprob]
  exact bernoulliExpectation_uniform_exact d hd hdr

/-- Independent random variables induce independent level events. -/
theorem iIndepSet_exceedances {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ι → Ω → ℝ} (hB : ∀ i, Measurable (B i))
    (hind : iIndepFun B μ) (t : ℝ) :
    iIndepSet (fun i => {ω | t < B i ω}) μ := by
  apply (iIndepSet_iff_meas_biInter (fun i => measurableSet_lt measurable_const (hB i))).mpr
  intro s
  simpa only [Set.preimage_setOf_eq] using
    hind.measure_inter_preimage_eq_mul s (sets := fun _ => Set.Ioi t)
      (fun _ _ => measurableSet_Ioi)

/-- The pointwise-in-level inequality used in the Gaussian layer-cake proof. -/
theorem independent_level_rank_bound_fintype {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ι → Ω → ℝ} (hB : ∀ i, Measurable (B i))
    (hind : iIndepFun B μ) (t : ℝ) (d : ℕ) (hd : 1 ≤ d) (hdr : d < Fintype.card ι) :
    finiteRankConstant d (Fintype.card ι) * min (d : ℝ) (∑ i, μ.real {ω | t < B i ω}) ≤
      ∫ ω, min (d : ℝ) (((Finset.univ.filter fun i => t < B i ω).card) : ℝ) ∂μ := by
  simpa only [bernoulliSelected] using uniformMatroid_bernoulli_bound_fintype
    (fun i => measurableSet_lt measurable_const (hB i))
    (iIndepSet_exceedances hB hind t) d hd hdr

theorem independent_level_rank_bound {r : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : Fin r → Ω → ℝ} (hB : ∀ i, Measurable (B i))
    (hind : iIndepFun B μ) (t : ℝ) (d : ℕ) (hd : 1 ≤ d) (hdr : d < r) :
    finiteRankConstant d r * min (d : ℝ) (∑ i, μ.real {ω | t < B i ω}) ≤
      ∫ ω, min (d : ℝ) (((Finset.univ.filter fun i => t < B i ω).card) : ℝ) ∂μ := by
  simpa only [bernoulliSelected] using uniformMatroid_bernoulli_bound
    (fun i => measurableSet_lt measurable_const (hB i))
    (iIndepSet_exceedances hB hind t) d hd hdr

/-- The support-sensitive form of the level-rank bound.  In particular the
constant depends on the number of positive covariance eigenvalues. -/
theorem independent_level_rank_bound_finset {ι Ω : Type*} [DecidableEq ι]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ι → Ω → ℝ} (hB : ∀ i, Measurable (B i))
    (hind : iIndepFun B μ) (s : Finset ι) (t : ℝ)
    (d : ℕ) (hd : 1 ≤ d) (hdr : d < s.card) :
    finiteRankConstant d s.card * min (d : ℝ) (∑ i ∈ s, μ.real {ω | t < B i ω}) ≤
      ∫ ω, min (d : ℝ) (((s.filter fun i => t < B i ω).card) : ℝ) ∂μ := by
  have hind' : iIndepFun (fun i : s => B i) μ := hind.precomp Subtype.val_injective
  have h := independent_level_rank_bound_fintype (fun i : s => hB i) hind' t d hd
    (by simpa using hdr)
  have hc (ω : Ω) : (Finset.univ.filter (fun i : s => t < B i ω)).card =
      (s.filter (fun i => t < B i ω)).card := by
    rw [Finset.univ_eq_attach, Finset.filter_attach (fun i : ι => t < B i ω) s]
    simp
  have hsum : (∑ i : s, μ.real {ω | t < B i ω}) =
      ∑ i ∈ s, μ.real {ω | t < B i ω} :=
    Finset.sum_coe_sort s (fun i : ι => μ.real {ω | t < B i ω})
  rw [hsum] at h
  simpa only [Fintype.card_coe, hc] using h

end GaussianPCA
