# Paper-to-Lean map

Paper source checked: `IJRNC_2026(20261007-110312).tex`.

| Paper item | Lean file | Status |
|---|---|---|
| `alpha=1/(1-ell)`, `beta=(1+ell)/(1-ell)` | `Exponents.lean` | formalized |
| `beta=2 alpha-1`, endpoint values | `Exponents.lean` | formalized |
| explicit `tau`, `tau_a`, `tau_r`, `Theta` | `Basic.lean` | encoded |
| return bound from integral-change inequality | `TimeBounds.lean` | formalized |
| `a_M`-dependent quadratic return bound | `TimeBounds.lean` | formalized |
| rise quadratic -> explicit `tau_r` | `TimeBounds.lean` | formalized |
| complete interval lower bound | `TimeBounds.lean` | formalized |
| prescribed threshold corollary | `Threshold.lean` | formalized from monotonicity |
| finite counting inequality | `Counting.lean` | formalized |
| cumulative estimate for finite families | `Cumulative.lean` | formalized |
| bounded finite sums -> summability | `Cumulative.lean` | formalized |
| terms of a summable nonnegative series -> 0 | `Cumulative.lean` | formalized |
| `|z_i| <= |z_i-z(s_i)|` from endpoint signs | `Accumulation.lean` | formalized |
| continuity + opposite endpoint signs -> `z(t*)=0` | `Accumulation.lean` | formalized |
| `z_i=u_i+phi_i`, `z_i->0` -> `u_i->-phi*` | `Accumulation.lean` | formalized |
| crossing-sign proposition from AC dynamics | `ProofObligations.lean` | exposed analytical obligation |
| maximum relation `w=0`, `qz=k1 A^alpha` | `ProofObligations.lean` | exposed analytical obligation |
| trajectory integral/quadratic estimates | `ProofObligations.lean` | exposed analytical obligations |
| explicit Real.rpow monotonicity of all three bounds | `ProofObligations.lean` | exposed obligation |
| full Filippov solution theory | not included | outside current mechanization |
