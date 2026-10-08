# Mathematical re-check of manuscript version 2026-10-07 11:03

## Main theorem

The three core inequalities were re-derived from the manuscript assumptions:

1. `k1 A^alpha <= M(A) T_return`, giving `T_return >= tau(A)`.
2. `A <= a_M M(A) T_return^2 / 2`, giving `T_return >= tau_a(A)`.
3. `A <= a_M (k1 A^alpha T_rise + M(A) T_rise^2/2)`, whose positive
   quadratic root is exactly the printed `tau_r(A)`.

The sign reversal when multiplying a negative `q w` by `a(t) <= a_M` in the second
return-bound proof is correct.

## Scaling

For `delta=0`, `M(A)=k2 A^beta`; all three bounds scale as
`A^(alpha-beta)=A^(-ell/(1-ell))`, using `beta=2 alpha-1`.
For `ell=-1`, `beta=0`, all three scale as `sqrt(A)` for arbitrary `delta>=0`.

## Monotonicity used in the threshold/counting corollaries

- `tau(A)` is nondecreasing because its derivative has numerator proportional to
  `k2 (alpha-beta) A^beta + alpha delta >= 0`.
- `tau_a(A)` is nondecreasing because `A/M(A)` has derivative numerator
  `k2 (1-beta) A^beta + delta >= 0`.
- the manuscript's scaled-variable proof for `tau_r` is consistent: writing
  `tau_r(A)=A^(1-alpha)y(A)` gives
  `1/a_M = k1 y + 1/2 (k2 + delta A^(-beta)) y^2`; both factors are
  nondecreasing in the required direction.

## Cumulative and accumulation corollaries

The revised finite-partial-sum argument is mathematically sound.  A slightly stronger
formulation is preferable: prove the bound for every finite subcollection of complete
intervals, then pass to the infinite sum.  This avoids assuming that an arbitrary
infinite chronological family has a first interval.  The Lean project uses this stronger
finite-set formulation.

The revised effective-input proof is sound.  From
`q_i z(t_i)>=0` and `q_i z(s_i)<=0`, one has directly
`|z(t_i)| <= |z(t_i)-z(s_i)|`.  Since both times tend to `t_*` and `z` is continuous,
`z(t_i)->0` and then `z(t_*)=0`; no constant-`q_i` subsequence is needed.

## Minor wording only

In the Discussion/Conclusion, the phrase "finite accumulating sequence" is potentially
ambiguous.  "sequence accumulating in finite time" is clearer.  This does not affect any
result.

No mathematical error was found in the revised theorem/corollary chain.
