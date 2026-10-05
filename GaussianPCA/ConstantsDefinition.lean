import Mathlib.Analysis.SpecialFunctions.Stirling

open Real

namespace GaussianPCA

/-- The exact finite-rank uniform-matroid constant. -/
noncomputable def finiteRankConstant (d r : ℕ) : ℝ :=
  1 - (r.choose d : ℝ) * ((d : ℝ) / r) ^ d * (1 - (d : ℝ) / r) ^ (r + 1 - d)

/-- The Poisson mass responsible for the limiting loss. -/
noncomputable def poissonDefect (d : ℕ) : ℝ :=
  exp (-(d : ℝ)) * (d : ℝ) ^ d / (d.factorial : ℝ)

/-- The dimension-free constant of Theorem 2. -/
noncomputable def poissonConstant (d : ℕ) : ℝ := 1 - poissonDefect d

/-- The leading term of the inverse-constant asymptotic expansion. -/
noncomputable def stirlingLeading (d : ℕ) : ℝ := 1 / sqrt (2 * π * (d : ℝ))

end GaussianPCA
