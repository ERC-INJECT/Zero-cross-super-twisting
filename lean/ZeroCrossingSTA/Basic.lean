import Mathlib

namespace ZeroCrossingSTA

noncomputable section

/-- Positive controller/plant constants used by the explicit time bounds. -/
structure Parameters where
  k1 : ℝ
  k2 : ℝ
  aM : ℝ
  delta : ℝ
  hk1 : 0 < k1
  hk2 : 0 < k2
  haM : 0 < aM
  hdelta : 0 ≤ delta

/--
Certificate data for one nonzero excursion.
`Aalpha` and `Abeta` stand for A^alpha and A^beta.  They are kept as
explicit fields so the algebraic theorem can be checked independently of
Mathlib's real-power API.
-/
structure ExcursionData (p : Parameters) where
  A : ℝ
  Aalpha : ℝ
  Abeta : ℝ
  M : ℝ
  hA : 0 < A
  hAalpha : 0 < Aalpha
  hAbeta : 0 ≤ Abeta
  hMdef : M = p.k2 * Abeta + p.delta
  hM : 0 < M


/-- Build the excursion data directly from the paper's real-power formulas. -/
noncomputable def ExcursionData.ofRpow
    (p : Parameters) (A alphaExp betaExp : ℝ) (hA : 0 < A) :
    ExcursionData p where
  A := A
  Aalpha := A ^ alphaExp
  Abeta := A ^ betaExp
  M := p.k2 * (A ^ betaExp) + p.delta
  hA := hA
  hAalpha := Real.rpow_pos_of_pos hA alphaExp
  hAbeta := le_of_lt (Real.rpow_pos_of_pos hA betaExp)
  hMdef := rfl
  hM := add_pos_of_pos_of_nonneg
    (mul_pos p.hk2 (Real.rpow_pos_of_pos hA betaExp)) p.hdelta

/-- Uniform-in-a return-time bound from the finite change in z. -/
def tau (p : Parameters) (e : ExcursionData p) : ℝ :=
  p.k1 * e.Aalpha / e.M

/-- Return-time bound using the known upper bound a_M. -/
def tauA (p : Parameters) (e : ExcursionData p) : ℝ :=
  Real.sqrt (2 * e.A / (p.aM * e.M))

/-- Rise-time lower bound. -/
def tauR (p : Parameters) (e : ExcursionData p) : ℝ :=
  (Real.sqrt (p.k1^2 * e.Aalpha^2 + 2 * e.M * e.A / p.aM)
    - p.k1 * e.Aalpha) / e.M

/-- Complete zero-crossing interval lower bound. -/
def Theta (p : Parameters) (e : ExcursionData p) : ℝ :=
  tauR p e + max (tau p e) (tauA p e)

lemma M_pos (p : Parameters) (e : ExcursionData p) : 0 < e.M := e.hM

lemma tau_nonneg (p : Parameters) (e : ExcursionData p) : 0 ≤ tau p e := by
  unfold tau
  exact le_of_lt (div_pos (mul_pos p.hk1 e.hAalpha) e.hM)

lemma tauA_nonneg (p : Parameters) (e : ExcursionData p) : 0 ≤ tauA p e := by
  unfold tauA
  exact Real.sqrt_nonneg _

/--
The three inequalities extracted in the paper proof from the trajectory dynamics.
These are the exact analytic certificates needed by the algebraic part of the main theorem.
-/
structure ExcursionCertificate (p : Parameters) (e : ExcursionData p) where
  Treturn : ℝ
  Trise : ℝ
  hTreturn : 0 ≤ Treturn
  hTrise : 0 ≤ Trise
  zChange : p.k1 * e.Aalpha ≤ e.M * Treturn
  returnQuadratic : e.A ≤ (p.aM * e.M / 2) * Treturn^2
  riseQuadratic :
    e.A ≤ p.aM * (p.k1 * e.Aalpha * Trise + (e.M / 2) * Trise^2)

end
end ZeroCrossingSTA
