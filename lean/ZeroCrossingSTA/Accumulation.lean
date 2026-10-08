import ZeroCrossingSTA.Cumulative

namespace ZeroCrossingSTA

/--
If two endpoint effective-input values have opposite q-oriented signs, then the
magnitude of the outgoing value is controlled by their difference.  This is the
key simplification used in the revised accumulation proof.
-/
theorem abs_left_le_abs_sub_of_opposite_effective_sign
    {q x y : ℝ}
    (hq : q = 1 ∨ q = -1)
    (hx : 0 ≤ q * x)
    (hy : q * y ≤ 0) :
    |x| ≤ |x - y| := by
  rcases hq with hq | hq
  · subst q
    simp only [one_mul] at hx hy
    rw [abs_of_nonneg hx]
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
    linarith
  · subst q
    have hx' : x ≤ 0 := by
      norm_num at hx ⊢
      linarith
    have hy' : 0 ≤ y := by
      norm_num at hy ⊢
      linarith
    rw [abs_of_nonpos hx']
    rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith

/-- Symmetric endpoint estimate. -/
theorem abs_right_le_abs_sub_of_opposite_effective_sign
    {q x y : ℝ}
    (hq : q = 1 ∨ q = -1)
    (hx : 0 ≤ q * x)
    (hy : q * y ≤ 0) :
    |y| ≤ |x - y| := by
  rcases hq with hq | hq
  · subst q
    simp only [one_mul] at hx hy
    have hy' : y ≤ 0 := hy
    rw [abs_of_nonpos hy']
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
    linarith
  · subst q
    have hx' : x ≤ 0 := by
      norm_num at hx ⊢
      linarith
    have hy' : 0 ≤ y := by
      norm_num at hy ⊢
      linarith
    rw [abs_of_nonneg hy']
    rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith

/--
Sequence-level core of Corollary 5.  No constant-q subsequence is needed: if the two
endpoint values converge to the same limit while carrying opposite q-oriented signs,
the common limit is zero.
-/
theorem common_limit_zero_of_opposite_effective_sign
    {q x y : ℕ → ℝ} {L : ℝ}
    (hq : ∀ n, q n = 1 ∨ q n = -1)
    (hxsign : ∀ n, 0 ≤ q n * x n)
    (hysign : ∀ n, q n * y n ≤ 0)
    (hxlim : Filter.Tendsto x Filter.atTop (nhds L))
    (hylim : Filter.Tendsto y Filter.atTop (nhds L)) :
    L = 0 := by
  have hdiff : Filter.Tendsto (fun n => x n - y n) Filter.atTop (nhds 0) := by
    convert hxlim.sub hylim using 1; ring_nf
  have habsdiff : Filter.Tendsto (fun n => |x n - y n|) Filter.atTop (nhds 0) := by
    simpa using hdiff.abs
  have habsx_le : ∀ n, |x n| ≤ |x n - y n| := fun n =>
    abs_left_le_abs_sub_of_opposite_effective_sign (hq n) (hxsign n) (hysign n)
  have habsx_nonneg : ∀ n, 0 ≤ |x n| := fun n => abs_nonneg _
  have habsxlim : Filter.Tendsto (fun n => |x n|) Filter.atTop (nhds 0) := by
    exact squeeze_zero habsx_nonneg habsx_le habsdiff
  have habsL : Filter.Tendsto (fun n => |x n|) Filter.atTop (nhds |L|) := by
    exact hxlim.abs
  have hL : |L| = 0 := tendsto_nhds_unique habsL habsxlim
  exact abs_eq_zero.mp hL

/--
Continuity form matching the paper: if t_i and s_i approach t*, continuity of z makes
both endpoint sequences converge to z(t*); the opposite-sign inequality therefore
forces z(t*) = 0.
-/
theorem continuous_effective_input_accumulation
    {z : ℝ → ℝ} {t s : ℕ → ℝ} {q : ℕ → ℝ} {tstar : ℝ}
    (hz : ContinuousAt z tstar)
    (ht : Filter.Tendsto t Filter.atTop (nhds tstar))
    (hs : Filter.Tendsto s Filter.atTop (nhds tstar))
    (hq : ∀ n, q n = 1 ∨ q n = -1)
    (htsign : ∀ n, 0 ≤ q n * z (t n))
    (hssign : ∀ n, q n * z (s n) ≤ 0) :
    z tstar = 0 := by
  have hzt : Filter.Tendsto (fun n => z (t n)) Filter.atTop (nhds (z tstar)) :=
    hz.tendsto.comp ht
  have hzs : Filter.Tendsto (fun n => z (s n)) Filter.atTop (nhds (z tstar)) :=
    hz.tendsto.comp hs
  exact common_limit_zero_of_opposite_effective_sign hq htsign hssign hzt hzs

/--
Algebraic last step of the paper: z_i = u_i + phi_i, z_i -> 0, and phi_i -> phi*
imply u_i -> -phi*.
-/
theorem control_converges_to_disturbance_compensation
    {u phi z : ℕ → ℝ} {phiStar : ℝ}
    (hrel : ∀ n, z n = u n + phi n)
    (hz : Filter.Tendsto z Filter.atTop (nhds 0))
    (hphi : Filter.Tendsto phi Filter.atTop (nhds phiStar)) :
    Filter.Tendsto u Filter.atTop (nhds (-phiStar)) := by
  have hdiff : Filter.Tendsto (fun n => z n - phi n) Filter.atTop (nhds (0 - phiStar)) :=
    hz.sub hphi
  have hu : u = fun n => z n - phi n := by
    funext n
    linarith [hrel n]
  rw [hu]
  simpa using hdiff

end ZeroCrossingSTA
