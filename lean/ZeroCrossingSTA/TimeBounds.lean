import ZeroCrossingSTA.Basic

namespace ZeroCrossingSTA

lemma return_uniform_bound
    (p : Parameters) (e : ExcursionData p) {T : ℝ}
    (hchange : p.k1 * e.Aalpha ≤ e.M * T) :
    tau p e ≤ T := by
  unfold tau
  apply (div_le_iff₀ e.hM).2
  simpa [mul_comm] using hchange

lemma return_aM_bound
    (p : Parameters) (e : ExcursionData p) {T : ℝ}
    (hT : 0 ≤ T)
    (hquad : e.A ≤ (p.aM * e.M / 2) * T^2) :
    tauA p e ≤ T := by
  unfold tauA
  rw [Real.sqrt_le_iff]
  constructor
  · exact hT
  · have hden : 0 < p.aM * e.M := mul_pos p.haM e.hM
    have hdiv : 2 * e.A / (p.aM * e.M) ≤ T^2 := by
      apply (div_le_iff₀ hden).2
      nlinarith [hquad]
    exact hdiv

lemma rise_bound
    (p : Parameters) (e : ExcursionData p) {T : ℝ}
    (hT : 0 ≤ T)
    (hquad : e.A ≤ p.aM *
      (p.k1 * e.Aalpha * T + (e.M / 2) * T^2)) :
    tauR p e ≤ T := by
  unfold tauR
  let B : ℝ := p.k1 * e.Aalpha
  have hB : 0 ≤ B := by
    dsimp [B]
    exact le_of_lt (mul_pos p.hk1 e.hAalpha)
  have hdiv : e.A / p.aM ≤ B * T + (e.M / 2) * T^2 := by
    apply (div_le_iff₀ p.haM).2
    simpa [B, mul_comm, mul_left_comm, mul_assoc] using hquad
  have hM0 : 0 ≤ e.M := le_of_lt e.hM
  have h2M0 : 0 ≤ 2 * e.M := mul_nonneg (by norm_num) hM0
  have hmul :
      2 * e.M * (e.A / p.aM) ≤
        2 * e.M * (B * T + (e.M / 2) * T^2) :=
    mul_le_mul_of_nonneg_left hdiv h2M0
  have hsq :
      B^2 + 2 * e.M * e.A / p.aM ≤ (B + e.M * T)^2 := by
    calc
      B^2 + 2 * e.M * e.A / p.aM
          = B^2 + 2 * e.M * (e.A / p.aM) := by ring
      _ ≤ B^2 + 2 * e.M * (B * T + (e.M / 2) * T^2) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_left hmul (B^2))
      _ = (B + e.M * T)^2 := by ring
  have hrhs : 0 ≤ B + e.M * T :=
    add_nonneg hB (mul_nonneg hM0 hT)
  have hsqrt :
      Real.sqrt (B^2 + 2 * e.M * e.A / p.aM) ≤ B + e.M * T := by
    rw [Real.sqrt_le_iff]
    exact ⟨hrhs, hsq⟩
  have hsqrt' :
      Real.sqrt (p.k1^2 * e.Aalpha^2 + 2 * e.M * e.A / p.aM) ≤
        p.k1 * e.Aalpha + e.M * T := by
    simpa [B, mul_pow] using hsqrt
  apply (div_le_iff₀ e.hM).2
  have hsqrt'' :
      Real.sqrt (p.k1^2 * e.Aalpha^2 + 2 * e.M * e.A / p.aM) ≤
        e.M * T + p.k1 * e.Aalpha := by
    simpa [add_comm] using hsqrt'
  have hnum :
      Real.sqrt (p.k1^2 * e.Aalpha^2 + 2 * e.M * e.A / p.aM)
          - p.k1 * e.Aalpha ≤ e.M * T :=
    sub_le_iff_le_add.mpr hsqrt''
  simpa [mul_comm] using hnum

/-- Paper Theorem: both return bounds and the rise bound from the three certificates. -/
theorem excursion_time_bounds
    (p : Parameters) (e : ExcursionData p)
    (c : ExcursionCertificate p e) :
    max (tau p e) (tauA p e) ≤ c.Treturn ∧
    tauR p e ≤ c.Trise := by
  constructor
  · exact max_le
      (return_uniform_bound p e c.zChange)
      (return_aM_bound p e c.hTreturn c.returnQuadratic)
  · exact rise_bound p e c.hTrise c.riseQuadratic

/-- Complete interval version of the main theorem. -/
theorem complete_interval_bound
    (p : Parameters) (e : ExcursionData p)
    (c : ExcursionCertificate p e) {Ttotal : ℝ}
    (hdecomp : Ttotal = c.Trise + c.Treturn) :
    Theta p e ≤ Ttotal := by
  rcases excursion_time_bounds p e c with ⟨hret, hrise⟩
  unfold Theta
  rw [hdecomp]
  linarith

end ZeroCrossingSTA
