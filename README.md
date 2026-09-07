# Lean formalization of Bala's conjectures for OEIS A158690

This repository is a **Lean 4 + mathlib formalization handoff draft** of the proof that the
sequence A158690 satisfies Peter Bala's two congruence conjectures.

## Mathematical structure

The proof works for every integer formal power series

`G(y) = Σ c_m y^m`

whose exponential generating function is `G(exp(t)-1)`.  Its coefficients are

`b_n = Σ_{m≤n} c_m m! S(n,m)`.

The repository formalizes the arithmetic through this Stirling-transform formula:

1. `m! S(n,m)` is a finite integer combination of powers `j^n`.
2. `j^(n p^r) ≡ j^(n p^(r-1)) (mod p^r)`.
3. Therefore every integral Stirling transform satisfies Gauss congruences.
4. The coefficient action of `(1+y)d/dy` proves the congruence for every shift.
5. Modulo `k`, terms with sufficiently large `m` vanish because `k | m!`, leaving
   finitely many power sequences and hence eventual period `φ(k)`.

## Status

Fully machine-checked: `lake build` succeeds end to end, there is no `sorry`/`admit`/
`axiom`/`unsafe` anywhere in the proof path, and

```
#print axioms A158690.bala_conjecture_one
#print axioms A158690.bala_conjecture_two
```

(see `A158690/Audit.lean`) report only the standard `[propext, Classical.choice,
Quot.sound]`, with no project-local axioms.

The two points originally flagged as API-sensitive were genuinely missing from
mathlib, not just renamed, and both were proved from scratch:

- `Basic.lean`'s Stirling inclusion-exclusion identity, derived from mathlib's
  `Nat.pow_eq_sum_stirlingSecond_mul_descFactorial` via binomial orthogonality.
- `Periodicity.lean`'s general (non-coprime-base) eventual periodicity of `j^n mod k`,
  proved via prime-power decomposition (`ordProj`/`ordCompl`), Euler's theorem on the
  coprime part, and CRT recombination — mathlib only has the coprime-base case.

The EGF construction in `A158690.lean` was checked against the real sequence: the
first four terms computed from `a158690Coeff`/`balaSequence` (1, 1, 5, 55) match
OEIS A158690 exactly.

## Build

```bash
lake update
lake build
```

## Files

- `A158690/Basic.lean` — Stirling transform and inclusion-exclusion.
- `A158690/Gauss.lean` — prime-power Gauss congruence.
- `A158690/Shift.lean` — all shifted congruences.
- `A158690/Periodicity.lean` — eventual periodicity modulo `k`.
- `A158690/A158690.lean` — specialization to the A158690 formal series.

## GitHub Actions

Every push runs `lake build` using Lean and mathlib.
