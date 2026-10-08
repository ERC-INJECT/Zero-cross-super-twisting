import ZeroCrossingSTA.Threshold

namespace ZeroCrossingSTA

/--
A finite family of disjoint complete intervals, each of length at least Theta_eps,
has cardinality at most horizon/Theta_eps.  This is the real-valued inequality
underlying the floor bound in the paper.
-/
theorem count_real_bound
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (len : ι → ℝ) {ThetaE horizon : ℝ}
    (hTheta : 0 < ThetaE)
    (hlen : ∀ i ∈ s, ThetaE ≤ len i)
    (hsum : ∑ i ∈ s, len i ≤ horizon) :
    (s.card : ℝ) ≤ horizon / ThetaE := by
  apply (le_div_iff₀ hTheta).2
  calc
    (s.card : ℝ) * ThetaE = ∑ i ∈ s, ThetaE := by simp
    _ ≤ ∑ i ∈ s, len i := by
      exact Finset.sum_le_sum (fun i hi => hlen i hi)
    _ ≤ horizon := hsum

/-- Exact natural-floor form used in the manuscript. -/
theorem count_floor_bound
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (len : ι → ℝ) {ThetaE horizon : ℝ}
    (hTheta : 0 < ThetaE)
    (hlen : ∀ i ∈ s, ThetaE ≤ len i)
    (hsum : ∑ i ∈ s, len i ≤ horizon) :
    s.card ≤ ⌊horizon / ThetaE⌋₊ := by
  apply Nat.le_floor
  exact count_real_bound s len hTheta hlen hsum

end ZeroCrossingSTA
