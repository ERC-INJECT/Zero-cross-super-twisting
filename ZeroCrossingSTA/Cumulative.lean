import ZeroCrossingSTA.Counting

namespace ZeroCrossingSTA

/--
Finite-family form of Corollary 3 (cumulative excursion estimate).
`J i` represents the integral contribution over the return segment of excursion `i`.
The disjointness/containment argument from the trajectory is encoded in `hglobal`.
-/
theorem cumulative_finite_family
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Aalpha J : ι → ℝ)
    {k1 rhs : ℝ}
    (hlocal : ∀ i ∈ s, k1 * Aalpha i ≤ J i)
    (hglobal : ∑ i ∈ s, J i ≤ rhs) :
    k1 * (∑ i ∈ s, Aalpha i) ≤ rhs := by
  calc
    k1 * (∑ i ∈ s, Aalpha i) = ∑ i ∈ s, k1 * Aalpha i := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, J i := by
      exact Finset.sum_le_sum (fun i hi => hlocal i hi)
    _ ≤ rhs := hglobal

/--
The paper's rho-version of the cumulative estimate.
-/
theorem cumulative_rho
    {sumA k1 k2 rhoBeta delta horizon integralBeta : ℝ}
    (hk1 : 0 < k1)
    (hk2 : 0 ≤ k2)
    (hintegral : integralBeta ≤ rhoBeta * horizon)
    (hgeneral : k1 * sumA ≤ k2 * integralBeta + delta * horizon) :
    sumA ≤ ((k2 * rhoBeta + delta) / k1) * horizon := by
  have hscaled : k2 * integralBeta ≤ k2 * (rhoBeta * horizon) :=
    mul_le_mul_of_nonneg_left hintegral hk2
  have hnum : k1 * sumA ≤ (k2 * rhoBeta + delta) * horizon := by
    calc
      k1 * sumA ≤ k2 * integralBeta + delta * horizon := hgeneral
      _ ≤ k2 * (rhoBeta * horizon) + delta * horizon := by linarith
      _ = (k2 * rhoBeta + delta) * horizon := by ring
  calc
    sumA ≤ ((k2 * rhoBeta + delta) * horizon) / k1 :=
      (le_div_iff₀ hk1).2 (by simpa [mul_comm] using hnum)
    _ = ((k2 * rhoBeta + delta) / k1) * horizon := by ring

/--
Lean version of the corrected infinite-family step: it is enough to bound every finite
subcollection.  This formulation avoids any hidden assumption that the chronological
order of an infinite family has a first element.
-/
theorem summable_of_uniform_finset_bound
    {ι : Type*} (b : ι → ℝ) {C : ℝ}
    (hb : ∀ i, 0 ≤ b i)
    (hfin : ∀ s : Finset ι, ∑ i ∈ s, b i ≤ C) :
    Summable b := by
  classical
  exact summable_of_sum_le hb hfin

/-- The same finite-subcollection hypothesis also bounds the infinite sum. -/
theorem tsum_le_of_uniform_finset_bound
    {ι : Type*} (b : ι → ℝ) {C : ℝ}
    (hb : ∀ i, 0 ≤ b i)
    (hfin : ∀ s : Finset ι, ∑ i ∈ s, b i ≤ C) :
    ∑' i, b i ≤ C := by
  classical
  exact Real.tsum_le_of_sum_le hb hfin

/-- Sequential partial-sum version, matching a chosen enumeration of excursions. -/
theorem summable_of_cumulative_partial_bound
    {b : ℕ → ℝ} {C : ℝ}
    (hb : ∀ n, 0 ≤ b n)
    (hpartial : ∀ N, ∑ i ∈ Finset.range N, b i ≤ C) :
    Summable b := by
  exact summable_of_sum_range_le hb hpartial

/-- Summability forces the excursion-power terms to vanish. -/
theorem cumulative_terms_tendsto_zero
    {b : ℕ → ℝ} {C : ℝ}
    (hb : ∀ n, 0 ≤ b n)
    (hpartial : ∀ N, ∑ i ∈ Finset.range N, b i ≤ C) :
    Filter.Tendsto b Filter.atTop (nhds 0) := by
  exact (summable_of_cumulative_partial_bound hb hpartial).tendsto_atTop_zero

end ZeroCrossingSTA
