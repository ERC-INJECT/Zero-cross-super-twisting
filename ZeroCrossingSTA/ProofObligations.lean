import ZeroCrossingSTA.Accumulation
import ZeroCrossingSTA.Exponents

namespace ZeroCrossingSTA

/-!
# Trajectory-level obligations corresponding to the manuscript

The files above kernel-check the algebraic consequences once the trajectory inequalities
have been established.  The following Props expose, rather than hide, the analytical
steps that would be required for a fully mechanized Filippov/absolutely-continuous
formalization of the closed-loop ODE/inclusion.

There are no `axiom` declarations and no `sorry` placeholders in this project.
-/

/-- Proposition 1: q-oriented sign of z at a sign-changing zero crossing. -/
def CrossingSignObligation
    (zAtCrossing q : ℝ) : Prop :=
  (q = 1 ∨ q = -1) ∧ 0 ≤ q * zAtCrossing

/-- Lemma 1: at an interior excursion maximum, w = 0 and q z = k1 A^alpha. -/
def MaximumRelationObligation
    (wAtMax zAtMax q k1 Aalpha : ℝ) : Prop :=
  wAtMax = 0 ∧ q * zAtMax = k1 * Aalpha

/-- Equation (integral-change): finite change required in z on the return segment. -/
def IntegralChangeObligation
    (k1 Aalpha M Treturn : ℝ) : Prop :=
  k1 * Aalpha ≤ M * Treturn

/-- a_M-dependent return-segment estimate. -/
def ReturnQuadraticObligation
    (A aM M Treturn : ℝ) : Prop :=
  A ≤ (aM * M / 2) * Treturn^2

/-- Rise-segment quadratic estimate. -/
def RiseQuadraticObligation
    (A aM k1 Aalpha M Trise : ℝ) : Prop :=
  A ≤ aM * (k1 * Aalpha * Trise + (M / 2) * Trise^2)

/--
Monotonicity needed by the threshold/counting corollaries.  The manuscript proves these
from alpha >= beta, beta in [0,1], and beta = 2 alpha - 1.  The explicit Real.rpow
formalization is left as a named obligation rather than silently assumed.
-/
def ExplicitBoundMonotonicityObligation
    (tauF tauAF tauRF : ℝ → ℝ) : Prop :=
  Monotone tauF ∧ Monotone tauAF ∧ Monotone tauRF

/--
Trajectory bookkeeping behind the cumulative estimate: for every finite subcollection,
the return segments are disjoint and contained in the compact observation interval.
-/
def CumulativeDisjointReturnSegmentsObligation
    {ι : Type*} (J : ι → ℝ) (rhs : ℝ) : Prop :=
  ∀ s : Finset ι, ∑ i ∈ s, J i ≤ rhs

end ZeroCrossingSTA
