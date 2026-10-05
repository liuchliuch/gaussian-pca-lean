import GaussianPCA.CorrelationGapFinite
import Mathlib.Probability.Independence.Integration

open scoped BigOperators
open Finset Set MeasureTheory ProbabilityTheory

noncomputable section

namespace GaussianPCA

/-- The random subset encoded by a finite family of events. -/
noncomputable def bernoulliSelected {ι Ω : Type*} [Fintype ι]
    (s : ι → Set Ω) (ω : Ω) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => ω ∈ s i)

/-- An atom of the joint Bernoulli distribution, including all failures. -/
def bernoulliAtom {ι Ω : Type*} [Fintype ι]
    (s : ι → Set Ω) (a : Finset ι) : Set Ω :=
  {ω | bernoulliSelected s ω = a}

theorem bernoulliAtom_eq_biInter {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Set Ω) (a : Finset ι) :
    bernoulliAtom s a = ⋂ i ∈ (Finset.univ : Finset ι),
      if i ∈ a then s i else (s i)ᶜ := by
  classical
  ext ω
  simp only [bernoulliAtom, Set.mem_setOf_eq, bernoulliSelected, Finset.ext_iff,
    Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iInter, forall_true_left]
  constructor
  · intro h i
    by_cases hi : i ∈ a
    · simpa [hi] using (h i).mpr hi
    · simpa [hi] using (mt (h i).mp hi)
  · intro h i
    by_cases hi : i ∈ a
    · have hmem : ω ∈ s i := by simpa [hi] using h i
      simp [hi, hmem]
    · have hmem : ω ∉ s i := by simpa [hi] using h i
      simp [hi, hmem]

theorem measurableSet_bernoulliAtom {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {s : ι → Set Ω} (hs : ∀ i, MeasurableSet (s i))
    (a : Finset ι) : MeasurableSet (bernoulliAtom s a) := by
  rw [bernoulliAtom_eq_biInter]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  split_ifs
  · exact hs i
  · exact (hs i).compl

/-- Independence gives the complete atom law, rather than merely the marginal
success probabilities. -/
theorem measureReal_bernoulliAtom {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : ι → Set Ω} (hs : ∀ i, MeasurableSet (s i))
    (hind : iIndepSet s μ) (a : Finset ι) :
    μ.real (bernoulliAtom s a) =
      bernoulliWeight (fun i => μ.real (s i)) Finset.univ a := by
  have hgen : ∀ i, MeasurableSet[MeasurableSpace.generateFrom {s i}] (s i) := by
    intro i
    exact MeasurableSpace.measurableSet_generateFrom (by simp)
  have hmul := (iIndepSet_iff s μ).mp hind (Finset.univ : Finset ι)
    (f := fun i => if i ∈ a then s i else (s i)ᶜ)
    (fun i _ => by dsimp only; split_ifs; exact hgen i; exact (hgen i).compl)
  rw [← bernoulliAtom_eq_biInter] at hmul
  unfold bernoulliWeight Measure.real
  rw [hmul, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  dsimp only
  split_ifs with hi
  · rfl
  · change μ.real (s i)ᶜ = 1 - μ.real (s i)
    simpa using measureReal_compl (μ := μ) (hs i)

/-- The finite polynomial expectation is exactly the ordinary Bochner
expectation for independent measurable Bernoulli events. -/
theorem integral_bernoulliSelected {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : ι → Set Ω} (hs : ∀ i, MeasurableSet (s i))
    (hind : iIndepSet s μ) (f : ℕ → ℝ) :
    (∫ ω, f (bernoulliSelected s ω).card ∂μ) =
      bernoulliExpectation (fun i => μ.real (s i)) Finset.univ f := by
  classical
  have hrepr (ω : Ω) : f (bernoulliSelected s ω).card =
      ∑ a ∈ (Finset.univ : Finset ι).powerset,
        (bernoulliAtom s a).indicator (fun _ => f a.card) ω := by
    rw [Finset.sum_eq_single (bernoulliSelected s ω)]
    · simp [bernoulliAtom]
    · intro a ha hne
      have hnot : ω ∉ bernoulliAtom s a := by
        simpa [bernoulliAtom, eq_comm] using hne
      simp [hnot]
    · intro hnot
      exact False.elim (hnot (Finset.mem_powerset.mpr (Finset.subset_univ _)))
  simp_rw [hrepr]
  rw [integral_finset_sum]
  · unfold bernoulliExpectation
    apply Finset.sum_congr rfl
    intro a ha
    rw [integral_indicator_const _ (measurableSet_bernoulliAtom hs a),
      measureReal_bernoulliAtom hs hind]
    rfl
  · intro a ha
    exact (integrable_const _).indicator (measurableSet_bernoulliAtom hs a)

end GaussianPCA
