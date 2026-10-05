# Nonlinear Gaussian PCA in Lean

[![Lean checks](https://github.com/liuchliuch/gaussian-pca-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/liuchliuch/gaussian-pca-lean/actions/workflows/lean.yml)

Lean 4 formalization of [*A Correlation-Gap Bound for Nonlinear Gaussian PCA*](https://arxiv.org/abs/2607.15035v1).

Theorem 2 and Lemmas 3–6, for every centered finite-dimensional Gaussian law with positive-semidefinite covariance, including singular covariance and rank zero. The main theorem proves exact retained energy at small rank, finite-rank and dimension-free approximation bounds, and a first-order constant expansion with an O(1/d) remainder.

Conjecture 1 remains open and is recorded only as a proposition. The formalization does not claim a PCA algorithm, a same-factor reconstruction-error guarantee, or a Gaussian example attaining the relaxation factor.

## Build and verify

Lean **4.24.0**, Mathlib and every transitive Git dependency are pinned.
Install [elan](https://github.com/leanprover/elan), then run:

```sh
elan toolchain install leanprover/lean4:v4.24.0
lake exe cache get
lake build
python3 scripts/verify.py
```

The verification command rebuilds the complete project library, audits originating declarations and their transitive axioms, and runs the retained regressions. Pinned Mathlib caches may be reused. Do not update `lake-manifest.json` when reproducing this version.

## Statements and proofs

Five explicit contracts restate the proved paper results. Their solutions use the library proofs and do not import the specification placeholders.

The [official Comparator](https://github.com/leanprover/comparator) runs in a separate Linux CI job with Landrun and the upstream systemd restriction. It compares target types and fixed declaration dependencies, enforces the axiom policy, and replays the exported solution through Lean’s default kernel. Rejection controls test the checking path. See [verification instructions](docs/VERIFICATION.md) for commands, pins and scope.

## Read the formalization

- [Main theorem](GaussianPCA/Main.lean)
- [Paper correspondence](docs/PAPER_MAP.md)
- [Statement contracts](StatementContracts/Challenge.lean)
- [Contract proofs](StatementContracts/Solution.lean)

The source distribution contains the mathematical library, statement specifications, retained tests, pinned configuration and verification tools. Generated logs, dependencies and build caches are excluded; CI publishes its reports as workflow artifacts.

No project license has been selected. The cited paper and upstream dependencies retain their own licensing terms.
