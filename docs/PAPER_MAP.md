# Paper map and semantic review

**Source:** Minbo Gao, Zhengfeng Ji and Chenghua Liu,
[A Correlation-Gap Bound for Nonlinear Gaussian PCA, arXiv:2607.15035v1](https://arxiv.org/abs/2607.15035v1),
16 July 2026. [SOURCES.json](SOURCES.json) records the original PDF/source URLs,
version and verified SHA-256 hashes. The downloads are not bundled.

**Review outcome (4 October 2026):** the formal statements and definitions match
the paper's five numbered proved results, Theorem 2 and Lemmas 3–6. This is an
independent source-level correspondence review, separate from mechanical
validation. Conjecture 1 remains unproved. Historical claims about earlier
literature are not formalization targets.

## Definitions and quantifiers

For ambient dimension `n` and `1 ≤ d ≤ n`, the paper uses a centered Gaussian
law with a real symmetric positive-semidefinite covariance matrix `C`.
All eigenvalues, including zeros, are retained. The rank is the actual matrix
rank, proved equal to the number of strictly positive eigenvalues.

- `IsCenteredGaussian μ C` specifies the genuine one-dimensional Gaussian law
  of **every** linear projection. Together with `C.PosSemidef` this includes
  singular Gaussian laws. Probability, uniqueness, the spectral eigenbasis and
  equality with the independent-Gaussian spectral model are proved in
  [Gaussian.lean](../GaussianPCA/Gaussian.lean) and
  [Spectral.lean](../GaussianPCA/Spectral.lean), not assumed as structure fields.
- `topSum d a` maximizes over subsets of cardinality at most `d`.
  `exists_topSum_set_card_eq` proves equivalence to exactly `d` entries for the
  paper's nonnegative inputs, including ties, zeros and `d=n`.
- `covarianceEnergy` is the actual expectation of the retained top-square sum;
  `covarianceOpt` is its supremum over all orthogonal matrices. The basis is
  chosen outside the integral; only the coordinate subset is sample-adaptive.
  The row-coordinate convention is the transpose of the paper's column basis
  and gives the same feasible set.
- `covarianceKLEnergy` is the eigenbasis value, equal to the independent
  expectation of `topSum d (λᵢ Zᵢ²)` for standard Gaussian `Zᵢ`.
- `thresholdEnergy` is the infimum over real `τ ≥ 0` of
  `dτ + Σᵢ E max(λᵢ Zᵢ² − τ, 0)`.
- There is no normalization by dimension, trace or variance. Integrals range
  over the full unbounded Gaussian law, with integrability proved from Gaussian
  moments. Supremum/infimum uses establish nonemptiness and bounds.

## The five contracts

[Challenge.lean](../StatementContracts/Challenge.lean) records the explicit
paper-facing types. [Solution.lean](../StatementContracts/Solution.lean)
discharges them. Both use separately reviewed shared mathematical definitions.

### Theorem 2: `GaussianPCAContracts.paper_2`

[Main.lean](../GaussianPCA/Main.lean) proves:

- If `rank C ≤ d`, `OPT = KL = trace C`, including rank zero.
- Otherwise, `KL ≤ OPT ≤ c(d,rank C)⁻¹ KL ≤ γ(d)⁻¹ KL`.

[ConstantsDefinition.lean](../GaussianPCA/ConstantsDefinition.lean) defines the
exact constants:

- `c(d,r) = 1 − choose(r,d)(d/r)^d(1−d/r)^(r+1−d)`
- `γ(d) = 1 − exp(−d)d^d/d!`

[Constants.lean](../GaussianPCA/Constants.lean) proves `c ≥ γ > 0` in the required
range and the fixed-`d` limit. [ConstantsAsymptotics.lean](../GaussianPCA/ConstantsAsymptotics.lean)
proves, for every positive integer `d`,
`|γ(d)⁻¹ − 1 − (2πd)⁻¹ᐟ²| ≤ 2/d`. The contract includes both natural-index
`IsBigO` statements: the first-order remainder is `O(1/d)` and the inverse minus
one is `O(1/√d)`. A quantitative logarithmic Stirling estimate supplies the rate;
convergence alone is not used as a substitute.

### Lemma 3: `GaussianPCAContracts.paper_3`

[TopSum.lean](../GaussianPCA/TopSum.lean) proves the exact nonnegative-threshold
variational identity, with an exact-cardinality maximizing subset on the
paper's domain. The `d=n` case and equal entries are covered.

### Lemma 4: `GaussianPCAContracts.paper_4`

[CovarianceObjective.lean](../GaussianPCA/CovarianceObjective.lean) identifies the
actual-law objectives with the spectral model.
[Objective.lean](../GaussianPCA/Objective.lean) proves its threshold bound using
Gaussian marginals and convex stop-loss expectations from
[Gaussian.lean](../GaussianPCA/Gaussian.lean); `paper_4` combines these into the
every-basis and supremum statements. Integrability is established. Finite
Jensen with squared orthogonal entries proves the needed majorization
consequence. Rotated coordinates are not assumed independent.

### Lemma 5: `GaussianPCAContracts.paper_5`

[CorrelationGap.lean](../GaussianPCA/CorrelationGap.lean) proves the sharp bound
for arbitrary mutually independent measurable Bernoulli events on any
probability space, with marginal probabilities zero and one allowed. The
product-atom law, smoothing argument and binomial bound are proved in the
supporting modules. This replaces the paper's appeal to Kashaev–Santiago's
contention-resolution theorem; no such bound is an axiom or an extra premise.

### Lemma 6: `GaussianPCAContracts.paper_6`

[GaussianLayerApplication.lean](../GaussianPCA/GaussianLayerApplication.lean)
proves the spectral-model comparison; `paper_6` transports it to
`c(d,rank C) * thresholdEnergy ≤ KL`. The proof restricts Bernoulli level events
to positive eigenvalues and accounts for the zero coordinates. The layer-cake,
Tonelli and tail-integration lemmas are proved. The threshold minimization
argument works for antitone tails with jumps, so Gaussian atomlessness is
unnecessary; this strengthens the intermediate result without weakening the
paper's conclusion.

## Scope and limitations

The proof chain is Lemma 3 → Lemma 4, Lemma 5 + layer integration → Lemma 6,
then Lemmas 4 and 6 + positive constants → Theorem 2. KL feasibility and total
energy establish its lower bound and low-rank equality branch.

`MallatZeitouniConjecture` is only a proposition definition. It is not a theorem,
axiom, contract target or premise of the proved results. The guarantees concern
retained energy; subtracting from trace does not yield an equal-factor bound
on reconstruction error. Sharpness of the uniform-matroid relaxation does not
assert an attaining Gaussian covariance/rotation example.

The challenge has five deliberate proof placeholders and is isolated from
production and solution imports. Exact-statement and dependency comparison,
axiom audits and standard-kernel replay check the formal development. They do
not by themselves establish the translation from informal mathematics. See
[verification instructions](VERIFICATION.md) and the CI reports for mechanical
checks and the precise trust boundary.
