# Claude handoff: compile and finish this Lean formalization

Goal: turn this repository into a fully machine-checked Lean 4 + mathlib formalization of the two Bala conjectures for OEIS A158690.

## Non-negotiable validation criteria

1. `lake build` exits with code 0.
2. There are no `sorry`, `admit`, `axiom`, `unsafe`, or placeholder theorem names in the proof path.
3. `#print axioms A158690.bala_conjecture_one` and `#print axioms A158690.bala_conjecture_two` report only standard logical/classical axioms expected from mathlib, and no project-local axioms.
4. The A158690 specialization is connected to the OEIS defining EGF, not merely to a separately defined Stirling-transform sequence.
5. Keep the mathematical proof equivalent to the accompanying paper: represent the EGF as `G(exp t - 1)` with integral coefficients; use the Stirling transform; prove eventual periodicity mod `k`; prove all shifted prime-power Gauss congruences.

## First known compile-sensitive points

- `A158690/Basic.lean`: the current inclusion-exclusion theorem name is likely not present in the pinned mathlib. Either find the current theorem or prove the formula directly.
- `A158690/Periodicity.lean`: `Nat.pow_add_totient_modeq_of_ge` is intentionally not trusted. Replace it by a complete proof of eventual periodicity of `j^n mod k` with period `Nat.totient k` for sufficiently large `n`, e.g. prime-power by prime-power plus CRT.
- `A158690/Shift.lean`: if the derivative/Stirling recurrence approach is awkward, replace it with the simpler direct identity `j^(N+i)=j^i*j^N` inside the inclusion-exclusion proof.
- `A158690/A158690.lean`: the negative power of a power series needs a proper unit/inverse treatment. Formalize `1-(1+X)^(-(2j-1))` using the inverse of the unit `1+X`, or define its coefficients by the binomial expansion and prove equivalence.

## Suggested commands

```bash
lake update
lake build
rg -n '\bsorry\b|\badmit\b|\baxiom\b|pow_add_totient_modeq_of_ge' .
```

After it builds, add a small audit file containing:

```lean
#print axioms A158690.bala_conjecture_one
#print axioms A158690.bala_conjecture_two
```

Commit only after both the build and audit pass.
