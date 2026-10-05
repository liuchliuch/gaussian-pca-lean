import GaussianPCA.BinomialRank
open GaussianPCA
example : binomialRank 1 2 (1 / 2) = (3 : ℝ) / 4 := by
  norm_num [binomialRank, binomialExpectation]
example : binomialRank 1 3 (1 / 3) = (19 : ℝ) / 27 := by
  norm_num [binomialRank, binomialExpectation]
example : binomialRank 2 3 (2 / 3) = (46 : ℝ) / 27 := by
  norm_num [binomialRank, binomialExpectation]
example : finiteRankConstant 2 3 = (23 : ℝ) / 27 := by
  norm_num [finiteRankConstant, Nat.choose]
example (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (23 : ℝ) / 27 * min 2 (3 * p) ≤ binomialRank 2 3 p := by
  have h := finiteRankConstant_mul_min_le_binomialRank 2 3 (by decide) (by decide) hp0 hp1
  norm_num [finiteRankConstant, Nat.choose] at h
  exact h
