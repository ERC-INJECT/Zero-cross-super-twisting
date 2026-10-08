import ZeroCrossingSTA.TimeBounds

namespace ZeroCrossingSTA

/--
Abstract monotonicity form of the prescribed-threshold corollary.
The explicit rpow monotonicity of tau, tau_a and tau_r is deliberately
separated as a proof obligation in `ProofObligations.lean`.
-/
theorem prescribed_threshold
    {tauF tauAF : ℝ → ℝ} {eps A Treturn Teps : ℝ}
    (hepsA : eps ≤ A)
    (htau : Monotone tauF)
    (htauA : Monotone tauAF)
    (hreturn : max (tauF A) (tauAF A) ≤ Treturn)
    (hfirst : Treturn ≤ Teps) :
    max (tauF eps) (tauAF eps) ≤ Teps := by
  have h1 : tauF eps ≤ tauF A := htau hepsA
  have h2 : tauAF eps ≤ tauAF A := htauA hepsA
  have hm : max (tauF eps) (tauAF eps) ≤ max (tauF A) (tauAF A) :=
    max_le_max h1 h2
  exact le_trans hm (le_trans hreturn hfirst)

/-- Threshold lower bound for a complete interval once rise monotonicity is available. -/
theorem threshold_complete_interval
    {tauRF tauF tauAF : ℝ → ℝ} {eps A Ttotal : ℝ}
    (hepsA : eps ≤ A)
    (hR : Monotone tauRF)
    (h1 : Monotone tauF)
    (h2 : Monotone tauAF)
    (hinterval : tauRF A + max (tauF A) (tauAF A) ≤ Ttotal) :
    tauRF eps + max (tauF eps) (tauAF eps) ≤ Ttotal := by
  have hr := hR hepsA
  have ht1 := h1 hepsA
  have ht2 := h2 hepsA
  have hm : max (tauF eps) (tauAF eps) ≤ max (tauF A) (tauAF A) :=
    max_le_max ht1 ht2
  linarith

end ZeroCrossingSTA
