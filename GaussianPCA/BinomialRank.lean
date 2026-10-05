import GaussianPCA.ConstantsDefinition
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-! # A sharp binomial rank estimate

The expectation is given recursively, so its use by the finite product-space
argument does not require a probabilistic representation theorem.
-/

noncomputable section

namespace GaussianPCA

/-- Expectation of a function of a binomial random variable. -/
def binomialExpectation : ℕ → ℝ → (ℕ → ℝ) → ℝ
  | 0, _, f => f 0
  | n + 1, p, f => (1 - p) * binomialExpectation n p f +
      p * binomialExpectation n p (fun k => f (k + 1))

/-- Expected rank of the rank-`d` uniform matroid on `n` independent,
identically distributed Bernoulli coordinates. -/
def binomialRank (d n : ℕ) (p : ℝ) : ℝ :=
  binomialExpectation n p (fun k => min (d : ℝ) (k : ℝ))

@[simp] theorem binomialExpectation_zero (p : ℝ) (f : ℕ → ℝ) :
    binomialExpectation 0 p f = f 0 := rfl

@[simp] theorem binomialExpectation_succ (n : ℕ) (p : ℝ) (f : ℕ → ℝ) :
    binomialExpectation (n + 1) p f = (1 - p) * binomialExpectation n p f +
      p * binomialExpectation n p (fun k => f (k + 1)) := rfl

@[simp] theorem binomialExpectation_const (n : ℕ) (p c : ℝ) :
    binomialExpectation n p (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [binomialExpectation_succ, ih]; ring

@[simp] theorem binomialExpectation_zero_probability (n : ℕ) (f : ℕ → ℝ) :
    binomialExpectation n 0 f = f 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa using ih

 theorem binomialExpectation_add (n : ℕ) (p : ℝ) (f g : ℕ → ℝ) :
    binomialExpectation n p (fun k => f k + g k) =
      binomialExpectation n p f + binomialExpectation n p g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [binomialExpectation_succ, ih]; ring

 theorem binomialExpectation_sub (n : ℕ) (p : ℝ) (f g : ℕ → ℝ) :
    binomialExpectation n p (fun k => f k - g k) =
      binomialExpectation n p f - binomialExpectation n p g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [binomialExpectation_succ, ih]; ring

 theorem binomialExpectation_mul_const (n : ℕ) (p c : ℝ) (f : ℕ → ℝ) :
    binomialExpectation n p (fun k => c * f k) = c * binomialExpectation n p f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [binomialExpectation_succ, ih]; ring

 theorem binomialExpectation_mono (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : ℕ → ℝ} (hfg : ∀ k, f k ≤ g k) :
    binomialExpectation n p f ≤ binomialExpectation n p g := by
  induction n generalizing f g with
  | zero => exact hfg 0
  | succ n ih =>
    exact add_le_add (mul_le_mul_of_nonneg_left (ih hfg) (sub_nonneg.mpr hp1))
      (mul_le_mul_of_nonneg_left (ih fun k => hfg (k + 1)) hp0)

 theorem binomialExpectation_mono_probability (n : ℕ) {p q : ℝ}
    (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq1 : q ≤ 1)
    {f : ℕ → ℝ} (hf : Monotone f) :
    binomialExpectation n p f ≤ binomialExpectation n q f := by
  induction n generalizing f with
  | zero => exact le_rfl
  | succ n ih =>
    have hf' : Monotone (fun k => f (k + 1)) := fun a b hab => hf (Nat.add_le_add_right hab 1)
    have h₀ := ih hf
    have h₁ := ih hf'
    have h₂ := binomialExpectation_mono n hp0 (hpq.trans hq1)
      (fun k => hf (Nat.le_succ k))
    simp only [binomialExpectation_succ]
    calc
      _ ≤ (1 - q) * binomialExpectation n p f +
          q * binomialExpectation n p (fun k => f (k + 1)) := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr h₂)]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr hq1))
        (mul_le_mul_of_nonneg_left h₁ (hp0.trans hpq))

 theorem binomialExpectation_anti_probability (n : ℕ) {p q : ℝ}
    (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq1 : q ≤ 1)
    {f : ℕ → ℝ} (hf : Antitone f) :
    binomialExpectation n q f ≤ binomialExpectation n p f := by
  have h := binomialExpectation_mono_probability n hp0 hpq hq1
    (show Monotone (fun k => (-1 : ℝ) * f k) from fun a b hab => by
      have := hf hab; linarith)
  rw [binomialExpectation_mul_const, binomialExpectation_mul_const] at h
  linarith

/-- Differentiation takes the forward difference of the payoff. -/
 theorem hasDerivAt_binomialExpectation (n : ℕ) (p : ℝ) (f : ℕ → ℝ) :
    HasDerivAt (fun q => binomialExpectation (n + 1) q f)
      ((n + 1 : ℕ) * binomialExpectation n p (fun k => f (k + 1) - f k)) p := by
  induction n generalizing f with
  | zero =>
    convert ((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).mul_const (f 0) |>.add
      ((hasDerivAt_id p).mul_const (f 1)) using 1
    simp [binomialExpectation]
    ring
  | succ n ih =>
    have h := (((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).mul (ih f)).add
      ((hasDerivAt_id p).mul (ih fun k => f (k + 1)))
    convert h using 1
    simp only [binomialExpectation_succ, Nat.cast_add, Nat.cast_one,
      binomialExpectation_sub, Pi.sub_apply, id_eq]
    ring

 theorem differentiable_binomialExpectation (n : ℕ) (f : ℕ → ℝ) :
    Differentiable ℝ (fun p => binomialExpectation n p f) := by
  cases n with
  | zero => exact differentiable_const _
  | succ n => exact fun p => (hasDerivAt_binomialExpectation n p f).differentiableAt

 theorem concaveOn_binomialExpectation (n : ℕ) {f : ℕ → ℝ}
    (hf : Antitone (fun k => f (k + 1) - f k)) :
    ConcaveOn ℝ (Set.Icc 0 1) (fun p => binomialExpectation n p f) := by
  cases n with
  | zero => exact concaveOn_const _ (convex_Icc _ _)
  | succ n =>
    apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _)
      (differentiable_binomialExpectation _ f).continuous.continuousOn
      (differentiable_binomialExpectation _ f).differentiableOn
    intro p hp q hq hpq
    rw [(hasDerivAt_binomialExpectation n q f).deriv,
      (hasDerivAt_binomialExpectation n p f).deriv]
    exact mul_le_mul_of_nonneg_left
      (binomialExpectation_anti_probability n (Set.mem_Icc.mp (interior_subset hp)).1
        hpq (Set.mem_Icc.mp (interior_subset hq)).2 hf) (by positivity)

 theorem binomialRank_mono (d n : ℕ) : MonotoneOn (binomialRank d n) (Set.Icc 0 1) := by
  intro p hp q hq hpq
  exact binomialExpectation_mono_probability n hp.1 hpq hq.2
    (fun a b hab => min_le_min_left _ (Nat.cast_le.mpr hab))

 theorem binomialRank_concave (d n : ℕ) : ConcaveOn ℝ (Set.Icc 0 1) (binomialRank d n) := by
  apply concaveOn_binomialExpectation
  intro a b hab
  have hab' : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
  simp only [Nat.cast_add, Nat.cast_one]
  rcases le_total (d : ℝ) a with hda | had
  · rw [min_eq_left hda, min_eq_left (by linarith : (d : ℝ) ≤ a + 1),
      min_eq_left (by linarith : (d : ℝ) ≤ b),
      min_eq_left (by linarith : (d : ℝ) ≤ b + 1)]
  · by_cases hdb : (d : ℝ) ≤ b
    · rw [min_eq_left hdb, min_eq_left (by linarith : (d : ℝ) ≤ b + 1)]
      simpa only [sub_self] using
        (sub_nonneg.mpr (min_le_min_left (d : ℝ) (by linarith : (a : ℝ) ≤ a + 1)))
    · have ha : (a : ℝ) + 1 ≤ d := by exact_mod_cast (show a + 1 ≤ d from by
        have : a < d := Nat.cast_lt.mp (lt_of_le_of_lt hab' (lt_of_not_ge hdb)); omega)
      have hb : (b : ℝ) + 1 ≤ d := by exact_mod_cast (show b + 1 ≤ d from by
        have : b < d := Nat.cast_lt.mp (lt_of_not_ge hdb); omega)
      rw [min_eq_right had, min_eq_right ha, min_eq_right (le_of_lt (lt_of_not_ge hdb)),
        min_eq_right hb]
      linarith

/-- The binomial size-bias identity. -/
theorem binomialExpectation_size_bias (n : ℕ) (p : ℝ) (f : ℕ → ℝ) :
    binomialExpectation (n + 1) p (fun k => (k : ℝ) * f k) =
      ((n + 1 : ℕ) : ℝ) * p * binomialExpectation n p (fun k => f (k + 1)) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [binomialExpectation_succ, ih]
    have hshift : (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * f (k + 1)) =
        (fun k : ℕ => (k : ℝ) * f (k + 1) + f (k + 1)) := by
      ext k; push_cast; ring
    rw [hshift, binomialExpectation_add, ih]
    simp only [binomialExpectation_succ, Nat.cast_add, Nat.cast_one]
    ring

/-- Explicit mass of a binomial random variable. -/
theorem binomialExpectation_singleton (n k : ℕ) (p : ℝ) :
    binomialExpectation n p (fun j => if j = k then 1 else 0) =
      (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
  induction n generalizing k with
  | zero => cases k <;> simp [Nat.choose]
  | succ n ih =>
    cases k with
    | zero =>
      have hz : (fun j : ℕ => if j + 1 = 0 then (1 : ℝ) else 0) = (fun _ => 0) := by
        ext j; simp
      rw [binomialExpectation_succ, hz, binomialExpectation_const, ih]
      simp [pow_succ]; ring
    | succ k =>
      have hs : (fun j : ℕ => if j + 1 = k + 1 then (1 : ℝ) else 0) =
          (fun j => if j = k then 1 else 0) := by ext j; simp
      rw [binomialExpectation_succ, hs, ih, ih]
      rcases lt_trichotomy k n with hkn | hkn | hkn
      · have hsub : n - k = n - (k + 1) + 1 := by omega
        rw [Nat.choose_succ_succ', Nat.cast_add, Nat.succ_sub_succ_eq_sub,
          hsub, pow_succ, pow_succ]
        ring
      · subst k
        simp [pow_succ, mul_comm]
      · have hnk : n < k + 1 := by omega
        have hnk' : n + 1 < k + 1 := by omega
        simp [Nat.choose_eq_zero_of_lt hkn, Nat.choose_eq_zero_of_lt hnk,
          Nat.choose_eq_zero_of_lt hnk']

/-- At an integral mean, the shortfall below the mean is one binomial mass. -/
theorem binomialRank_at_mean_aux (d n : ℕ) (_hd : 1 ≤ d) (p : ℝ)
    (hmean : ((n + 1 : ℕ) : ℝ) * p = d) :
    binomialRank d (n + 1) p = (d : ℝ) -
      (d : ℝ) * (1 - p) * binomialExpectation n p
        (fun k => if k + 1 = d then 1 else 0) := by
  let f : ℕ → ℝ := fun k => if k < d then 1 else 0
  have hrank : (fun k : ℕ => min (d : ℝ) (k : ℝ)) =
      (fun k => (d : ℝ) - ((d : ℝ) * f k - (k : ℝ) * f k)) := by
    ext k
    dsimp [f]
    split_ifs with h
    · rw [min_eq_right (by exact_mod_cast h.le)]; ring
    · rw [min_eq_left (by exact_mod_cast (Nat.le_of_not_gt h))]; ring
  have hdiff : (fun k => f k - f (k + 1)) =
      (fun k => if k + 1 = d then 1 else 0) := by
    ext k
    dsimp [f]
    split_ifs <;> norm_num at * <;> omega
  unfold binomialRank
  rw [hrank, binomialExpectation_sub, binomialExpectation_const,
    binomialExpectation_sub, binomialExpectation_mul_const,
    binomialExpectation_size_bias, hmean, binomialExpectation_succ,
    ← hdiff, binomialExpectation_sub]
  ring

/-- Below any positive comparison probability, concavity controls the ratio
of the rank expectation to the expected cardinality. -/
theorem binomialRank_scale (d n : ℕ) {p q : ℝ}
    (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (p / q) * binomialRank d n q ≤ binomialRank d n p := by
  have ht0 : 0 ≤ p / q := div_nonneg hp0 hq0.le
  have ht1 : p / q ≤ 1 := (div_le_one hq0).mpr hpq
  have h := (binomialRank_concave d n).2 (show (0 : ℝ) ∈ Set.Icc 0 1 by simp)
    (show q ∈ Set.Icc 0 1 from ⟨hq0.le, hq1⟩)
    (sub_nonneg.mpr ht1) ht0 (by ring : 1 - p / q + p / q = 1)
  have harg : (p / q) * q = p := div_mul_cancel₀ p hq0.ne'
  simpa only [smul_eq_mul, harg, binomialRank, binomialExpectation_zero_probability,
    Nat.cast_zero, min_eq_right (Nat.cast_nonneg d), mul_zero, zero_add] using h

/-- Exact evaluation at the integral mean. -/
theorem binomialRank_at_mean (d r : ℕ) (hd : 1 ≤ d) (hdr : d < r) :
    binomialRank d r ((d : ℝ) / r) = (d : ℝ) *
      (1 - (r.choose d : ℝ) * ((d : ℝ) / r) ^ d *
        (1 - (d : ℝ) / r) ^ (r + 1 - d)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  let p : ℝ := (d : ℝ) / (n + 1 : ℕ)
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hmean : ((n + 1 : ℕ) : ℝ) * p = d := by dsimp [p]; field_simp
  change binomialRank d (n + 1) p = _
  rw [binomialRank_at_mean_aux d n hd p hmean]
  have hind : (fun k : ℕ => if k + 1 = d then (1 : ℝ) else 0) =
      (fun k => if k = d - 1 then 1 else 0) := by
    ext k
    simp only [show k + 1 = d ↔ k = d - 1 by omega]
  rw [hind, binomialExpectation_singleton]
  have hchoose : ((n + 1 : ℕ) : ℝ) * (n.choose (d - 1) : ℝ) =
      ((n + 1).choose d : ℝ) * (d : ℝ) := by
    have h := Nat.succ_mul_choose_eq n (d - 1)
    have hdsub : d - 1 + 1 = d := by omega
    simpa only [Nat.succ_eq_add_one, hdsub, Nat.cast_mul] using
      congrArg (fun k : ℕ => (k : ℝ)) h
  have hc : (n.choose (d - 1) : ℝ) = ((n + 1).choose d : ℝ) * p := by
    apply mul_left_cancel₀ hd0
    calc
      (d : ℝ) * (n.choose (d - 1) : ℝ) =
          (((n + 1 : ℕ) : ℝ) * p) * (n.choose (d - 1) : ℝ) := by rw [hmean]
      _ = (((n + 1 : ℕ) : ℝ) * (n.choose (d - 1) : ℝ)) * p := by ring
      _ = (d : ℝ) * (((n + 1).choose d : ℝ) * p) := by rw [hchoose]; ring
  have hdsub : d = d - 1 + 1 := by omega
  have hnsub : n - (d - 1) = n + 1 - d := by omega
  have hsub : n + 1 + 1 - d = (n + 1 - d) + 1 := by omega
  change (d : ℝ) - (d : ℝ) * (1 - p) *
      ((n.choose (d - 1) : ℝ) * p ^ (d - 1) * (1 - p) ^ (n - (d - 1))) =
      (d : ℝ) * (1 - ((n + 1).choose d : ℝ) * p ^ d *
        (1 - p) ^ (n + 1 + 1 - d))
  rw [hc, hnsub, hsub, pow_succ, show p ^ d = p ^ (d - 1) * p by
    conv_lhs => rw [hdsub]; rw [pow_succ]]
  ring

/-- Sharp lower bound for the scalar binomial case. -/
theorem binomialRank_lower_bound (d r : ℕ) (hd : 1 ≤ d) (hdr : d < r)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - (r.choose d : ℝ) * ((d : ℝ) / r) ^ d *
      (1 - (d : ℝ) / r) ^ (r + 1 - d)) * min (d : ℝ) ((r : ℝ) * p) ≤
      binomialRank d r p := by
  let q : ℝ := (d : ℝ) / r
  let c : ℝ := 1 - (r.choose d : ℝ) * q ^ d * (1 - q) ^ (r + 1 - d)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hq0 : 0 < q := div_pos hdpos hrpos
  have hq1 : q ≤ 1 := (div_le_one hrpos).mpr (by exact_mod_cast hdr.le)
  have hq : (r : ℝ) * q = d := by dsimp [q]; field_simp
  have heq : binomialRank d r q = (d : ℝ) * c := binomialRank_at_mean d r hd hdr
  change c * min (d : ℝ) ((r : ℝ) * p) ≤ _
  rcases le_total p q with hpq | hqp
  · have hpd : (r : ℝ) * p ≤ d := by
      calc
        (r : ℝ) * p ≤ (r : ℝ) * q := mul_le_mul_of_nonneg_left hpq hrpos.le
        _ = d := hq
    rw [min_eq_right hpd]
    have h := binomialRank_scale d r hp0 hpq hq0 hq1
    rw [heq] at h
    have halg : (p / q) * ((d : ℝ) * c) = c * ((r : ℝ) * p) := by
      rw [← hq]
      field_simp [ne_of_gt hq0]
    rwa [halg] at h
  · have hdp : (d : ℝ) ≤ (r : ℝ) * p := by
      calc
        (d : ℝ) = (r : ℝ) * q := hq.symm
        _ ≤ (r : ℝ) * p := mul_le_mul_of_nonneg_left hqp hrpos.le
    rw [min_eq_left hdp]
    have h := binomialRank_mono d r ⟨hq0.le, hq1⟩ ⟨hp0, hp1⟩ hqp
    rw [heq] at h
    nlinarith

/-- The scalar binomial estimate in the notation of the paper. -/
theorem finiteRankConstant_mul_min_le_binomialRank (d r : ℕ)
    (hd : 1 ≤ d) (hdr : d < r) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    finiteRankConstant d r * min (d : ℝ) ((r : ℝ) * p) ≤ binomialRank d r p :=
  binomialRank_lower_bound d r hd hdr hp0 hp1

theorem binomialRank_eq_finiteRankConstant (d r : ℕ)
    (hd : 1 ≤ d) (hdr : d < r) :
    binomialRank d r ((d : ℝ) / r) = (d : ℝ) * finiteRankConstant d r :=
  binomialRank_at_mean d r hd hdr

end GaussianPCA
