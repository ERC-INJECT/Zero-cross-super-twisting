# Lean 4 formalization of zero-crossing bounds for the homogeneous super-twisting algorithm

This repository provides supplementary material for the manuscript
**“Zero-Crossing Time Lower Bounds for the Homogeneous Super-Twisting Algorithm”**,
prepared for submission to the *International Journal of Robust and Nonlinear Control*.

## Scope

The Lean project checks the algebraic theorem chain underlying the following
results in the manuscript:

- relations between the homogeneous exponents `alpha` and `beta`;
- the two excursion-dependent return-time bounds `tau` and `tau_a`;
- the rise-time bound `tau_r` and complete-interval bound `Theta`;
- the prescribed-threshold and finite-count estimates;
- the cumulative estimate for finite collections of excursions;
- summability obtained from bounds on arbitrary finite subcollections;
- the algebraic step used in the accumulation argument;
- the limiting disturbance-compensation relation along an accumulating
  zero-crossing sequence.

The source files contain no `sorry` placeholders or user-declared `axiom`s.

## Scope of verification

**This is not a formal verification of the full closed-loop dynamics.** In
particular, the Filippov differential inclusion, existence of absolutely
continuous trajectories, and the trajectory-level integral and crossing-sign
arguments are not formalized from first principles. Their use in the Lean
proofs is made explicit through the assumptions and certificates in
`ZeroCrossingSTA/ProofObligations.lean`. These dynamical arguments are
established analytically in the manuscript.

The cumulative argument uses arbitrary finite subcollections of excursion
intervals. This avoids assuming that an accumulating family has a first
interval.

## Software and build instructions

- Lean 4.34.1
- Mathlib corresponding to the dependency pinned in `lake-manifest.json`

With Lean and Lake installed, run from the root of the extracted project:

```bash
lake exe cache get
lake build
```

The project was successfully built using Lean 4.34.1 and Mathlib. Retain
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` to reproduce the
specified dependency configuration. Running `lake update` is not necessary
for a normal reproduction build and may change the dependency lock file.

## Files

- `ZeroCrossingSTA/`: Lean source files.
- `ZeroCrossingSTA.lean`: root module.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: project and dependency configuration.
- `PAPER_MAP.md`: correspondence between the formalized statements and manuscript results.
- `AUDIT.md`: notes on verification scope and proof obligations.
