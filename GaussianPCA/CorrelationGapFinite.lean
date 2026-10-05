import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

open scoped BigOperators
open Finset

noncomputable section

namespace GaussianPCA

/-- Probability of one atom in a finite independent Bernoulli family. -/
def bernoulliWeight {ι : Type*} [DecidableEq ι] (q : ι → ℝ)
    (s a : Finset ι) : ℝ :=
  ∏ i ∈ s, if i ∈ a then q i else 1 - q i

/-- The expectation of a function of the number of successes in a finite
independent Bernoulli family.  Its probability interpretation is proved below. -/
def bernoulliExpectation {ι : Type*} [DecidableEq ι] (q : ι → ℝ)
    (s : Finset ι) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ s.powerset, bernoulliWeight q s a * f a.card

@[simp] theorem bernoulliExpectation_empty {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) (f : ℕ → ℝ) : bernoulliExpectation q ∅ f = f 0 := by
  simp [bernoulliExpectation, bernoulliWeight]

theorem bernoulliWeight_nonneg {ι : Type*} [DecidableEq ι]
    {q : ι → ℝ} {s a : Finset ι}
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1) : 0 ≤ bernoulliWeight q s a := by
  apply Finset.prod_nonneg
  intro i hi
  split_ifs
  · exact (hq i hi).1
  · exact sub_nonneg.mpr (hq i hi).2

theorem bernoulliExpectation_mono {ι : Type*} [DecidableEq ι]
    {q : ι → ℝ} {s : Finset ι} {f g : ℕ → ℝ}
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hfg : ∀ n ≤ s.card, f n ≤ g n) :
    bernoulliExpectation q s f ≤ bernoulliExpectation q s g := by
  apply Finset.sum_le_sum
  intro a ha
  exact mul_le_mul_of_nonneg_left
    (hfg _ (Finset.card_le_card (Finset.mem_powerset.mp ha)))
    (bernoulliWeight_nonneg hq)

theorem bernoulliExpectation_congr {ι : Type*} [DecidableEq ι]
    {q p : ι → ℝ} {s : Finset ι} (f : ℕ → ℝ)
    (h : ∀ i ∈ s, q i = p i) :
    bernoulliExpectation q s f = bernoulliExpectation p s f := by
  unfold bernoulliExpectation
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [h i hi]

theorem bernoulliExpectation_add {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) (s : Finset ι) (f g : ℕ → ℝ) :
    bernoulliExpectation q s (fun n => f n + g n) =
      bernoulliExpectation q s f + bernoulliExpectation q s g := by
  simp [bernoulliExpectation, mul_add, Finset.sum_add_distrib]

theorem bernoulliExpectation_mul {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) (s : Finset ι) (c : ℝ) (f : ℕ → ℝ) :
    bernoulliExpectation q s (fun n => c * f n) =
      c * bernoulliExpectation q s f := by
  simp [bernoulliExpectation, Finset.mul_sum, mul_left_comm]

theorem bernoulliExpectation_insert {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) {s : Finset ι} {i : ι} (hi : i ∉ s) (f : ℕ → ℝ) :
    bernoulliExpectation q (insert i s) f =
      (1 - q i) * bernoulliExpectation q s f +
        q i * bernoulliExpectation q s (fun n => f (n + 1)) := by
  unfold bernoulliExpectation
  rw [Finset.sum_powerset_insert hi]
  simp only [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha
    have hia : i ∉ a := fun h => hi (Finset.mem_powerset.mp ha h)
    simp [bernoulliWeight, Finset.prod_insert hi, hia, mul_assoc]
  · apply Finset.sum_congr rfl
    intro a ha
    have hia : i ∉ a := fun h => hi (Finset.mem_powerset.mp ha h)
    rw [Finset.card_insert_of_notMem hia]
    have hw : bernoulliWeight q (insert i s) (insert i a) =
        q i * bernoulliWeight q s a := by
      unfold bernoulliWeight
      rw [Finset.prod_insert hi]
      simp only [Finset.mem_insert_self, if_true]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := by rintro rfl; exact hi hj
      simp [hji]
    rw [hw]
    ring

@[simp] theorem bernoulliExpectation_one {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) (s : Finset ι) : bernoulliExpectation q s (fun _ => 1) = 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [bernoulliExpectation_insert q hi]
    simpa using show (1 - q i) * bernoulliExpectation q s (fun _ => 1) +
        q i * bernoulliExpectation q s (fun _ => 1) = 1 by rw [ih]; ring

theorem bernoulliExpectation_const {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) (s : Finset ι) (c : ℝ) :
    bernoulliExpectation q s (fun _ => c) = c := by
  simpa using bernoulliExpectation_mul q s c (fun _ => 1)

theorem bernoulliExpectation_id {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) (s : Finset ι) :
    bernoulliExpectation q s (fun n => (n : ℝ)) = ∑ i ∈ s, q i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [bernoulliExpectation_insert q hi]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [bernoulliExpectation_add, bernoulliExpectation_const, ih, Finset.sum_insert hi]
    ring

theorem continuous_bernoulliExpectation {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ℕ → ℝ) :
    Continuous (fun q : ι → ℝ => bernoulliExpectation q s f) := by
  unfold bernoulliExpectation bernoulliWeight
  apply continuous_finset_sum
  intro a ha
  apply Continuous.mul
  · apply continuous_finset_prod
    intro i hi
    split_ifs <;> fun_prop
  · exact continuous_const

/-- A discretely concave function remains discretely concave after adding an
independent number of Bernoulli successes. -/
theorem bernoulliExpectation_second_difference_nonpos {ι : Type*} [DecidableEq ι]
    {q : ι → ℝ} {s : Finset ι} {f : ℕ → ℝ}
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hf : ∀ n, f n + f (n + 2) ≤ 2 * f (n + 1)) :
    bernoulliExpectation q s f + bernoulliExpectation q s (fun n => f (n + 2)) ≤
      2 * bernoulliExpectation q s (fun n => f (n + 1)) := by
  rw [← bernoulliExpectation_add, ← bernoulliExpectation_mul]
  exact bernoulliExpectation_mono hq (fun n _ => hf n)

/-- The uniform matroid rank is discretely concave. -/
theorem min_nat_second_difference_nonpos (d n : ℕ) :
    min (d : ℝ) n + min (d : ℝ) (n + 2) ≤ 2 * min (d : ℝ) (n + 1) := by
  by_cases h : n + 1 ≤ d
  · have h₁ : (n : ℝ) ≤ d := by exact_mod_cast (show n ≤ d by omega)
    have h₂ : (n : ℝ) + 1 ≤ d := by exact_mod_cast h
    rw [min_eq_right h₁, min_eq_right h₂]
    have := min_le_right (d : ℝ) ((n : ℝ) + 2)
    linarith
  · have h₁ : (d : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (show d ≤ n + 1 by omega)
    have h₂ : (d : ℝ) ≤ (n : ℝ) + 2 := by linarith
    rw [min_eq_left h₁, min_eq_left h₂]
    have := min_le_left (d : ℝ) (n : ℝ)
    linarith

end GaussianPCA

namespace GaussianPCA

open scoped BigOperators
open Finset

theorem bernoulliExpectation_insert_pair {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) {s : Finset ι} {i j : ι} (hi : i ∉ s) (hj : j ∉ s)
    (hij : i ≠ j) (f : ℕ → ℝ) :
    bernoulliExpectation q (insert i (insert j s)) f =
      (1 - q i) * (1 - q j) * bernoulliExpectation q s f +
      ((1 - q i) * q j + q i * (1 - q j)) *
        bernoulliExpectation q s (fun n => f (n + 1)) +
      q i * q j * bernoulliExpectation q s (fun n => f (n + 2)) := by
  rw [bernoulliExpectation_insert q (by simp [hij, hi]),
      bernoulliExpectation_insert q hj,
      bernoulliExpectation_insert q hj]
  simp only [Nat.add_assoc]
  ring

end GaussianPCA
