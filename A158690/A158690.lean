import A158690.Shift
import A158690.Periodicity

/-!
# A158690 and Bala's conjectures

This file packages the general theorems in the exact form used for OEIS A158690.
The mathematical bridge is: its EGF is `H(e^t-1)` for an integral formal power
series `H`.  Rather than depending on analytic exponentials, we represent `H`
by its integer coefficient function `a158690Coeff` and define the sequence by its
Stirling transform; this is algebraically equivalent to the EGF coefficient identity.
-/

namespace A158690

/-- The constant coefficient of `1 + X` is the unit `1`, so `1 + X` is invertible
in `PowerSeries ℤ` via `PowerSeries.invOfUnit`. -/
theorem constantCoeff_one_add_X :
    PowerSeries.constantCoeff (1 + PowerSeries.X : PowerSeries ℤ) = ((1 : ℤˣ) : ℤ) := by
  simp

/-- The genuine two-sided inverse of `1 + X` in `PowerSeries ℤ`, obtained from the fact
that its constant coefficient `1` is a unit. This replaces any attempt to use a raw
negative `zpow`, which does not type-check on `PowerSeries ℤ` since that ring has no
`Inv` instance. -/
noncomputable def oneAddXInv : PowerSeries ℤ :=
  PowerSeries.invOfUnit (1 + PowerSeries.X) (1 : ℤˣ)

theorem oneAddX_mul_oneAddXInv :
    (1 + PowerSeries.X) * oneAddXInv = 1 :=
  PowerSeries.mul_invOfUnit _ _ constantCoeff_one_add_X

/-- Truncated coefficient of
`Σ_m ∏_{j=1}^m (1 - (1+y)^(-(2j-1)))`.

Each factor `(1+y)^(-(2j-1))` is realized as `oneAddXInv ^ (2j-1)`, a nonnegative power
of the genuine inverse of `1+y`, so this is the actual reciprocal and not merely a
notational stand-in. The coefficient of degree `d` only sees `m ≤ d`, so this finite
definition is the formal-power-series construction without convergence issues.
-/
noncomputable def a158690Coeff (d : ℕ) : ℤ :=
  let term (m : ℕ) : PowerSeries ℤ :=
    ∏ j ∈ Finset.range m,
      (1 - oneAddXInv ^ (2 * (j + 1) - 1))
  (∑ m ∈ Finset.range (d + 1), term m).coeff d

/-- The sequence produced by the integral `H(e^t-1)` representation. -/
noncomputable def balaSequence (n : ℕ) : ℤ :=
  stirlingTransform a158690Coeff n

/-- Bala conjecture 1: eventual periodicity modulo `k`, period dividing `φ(k)`.
Here we exhibit `φ(k)` itself as a period. -/
theorem bala_conjecture_one (k : ℕ) (hk : 1 < k) :
    ∃ N, ∀ n ≥ N,
      Int.ModEq (k : ℤ) (balaSequence (n + k.totient)) (balaSequence n) := by
  simpa [balaSequence] using stirlingTransform_eventually_periodic a158690Coeff k hk

/-- Bala conjecture 2: all shifted prime-power Gauss congruences. -/
theorem bala_conjecture_two (i n p r : ℕ)
    (hp : p.Prime) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    Int.ModEq (p ^ r : ℤ)
      (balaSequence (n * p ^ r + i))
      (balaSequence (n * p ^ (r - 1) + i)) := by
  simpa [balaSequence] using
    stirlingTransform_shifted_gauss a158690Coeff i n p r hp hn hr

end A158690
