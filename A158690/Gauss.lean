import A158690.Basic
import Mathlib.NumberTheory.PowModTotient

/-!
# Gauss congruences

The arithmetic core of Bala's second conjecture.
-/

namespace A158690

open scoped BigOperators

/-- Elementary bound used in the `p ∣ j` case. -/
theorem le_prime_pow_pred (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) : r ≤ p ^ (r - 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  induction r using Nat.case_strong_induction_on with
  | hz => omega
  | hi r ih =>
      simp only [Nat.add_sub_cancel]
      by_cases h : r = 0
      · subst r; simp
      · have hr' : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr h
        have hir : r ≤ p ^ (r - 1) := ih r (by omega) hr'
        have hmul : p ^ (r - 1) * 2 ≤ p ^ (r - 1) * p := Nat.mul_le_mul_left _ hp2
        have hpow : p ^ (r - 1) * p = p ^ r := by
          rw [← pow_succ]; congr 1; omega
        omega

/-- The power congruence driving all Gauss congruences. -/
theorem power_gauss (j n p r : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    j ^ (n * p ^ r) ≡ j ^ (n * p ^ (r - 1)) [MOD p ^ r] := by
  by_cases hj : p ∣ j
  · rcases hj with ⟨q, rfl⟩
    have hbound : r ≤ n * p ^ (r - 1) := by
      have h1 := le_prime_pow_pred p r hp hr
      nlinarith
    have hdvd1 : p ^ r ∣ (p * q) ^ (n * p ^ (r - 1)) := by
      rw [mul_pow]
      exact dvd_mul_of_dvd_left (pow_dvd_pow p hbound) _
    have hbound2 : r ≤ n * p ^ r := by
      have hle : p ^ (r - 1) ≤ p ^ r := Nat.pow_le_pow_right hp.pos (by omega)
      have hle2 : n * p ^ (r - 1) ≤ n * p ^ r := Nat.mul_le_mul_left n hle
      omega
    have hdvd2 : p ^ r ∣ (p * q) ^ (n * p ^ r) := by
      rw [mul_pow]
      exact dvd_mul_of_dvd_left (pow_dvd_pow p hbound2) _
    exact (Nat.modEq_zero_iff_dvd.mpr hdvd2).trans (Nat.modEq_zero_iff_dvd.mpr hdvd1).symm
  · have hcop : j.Coprime (p ^ r) := by
      rw [Nat.coprime_pow_right_iff (by omega : 0 < r)]
      exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hj).symm
    have htot : (p ^ r).totient = p ^ (r - 1) * (p - 1) := by
      cases r with
      | zero => omega
      | succ s => simpa using Nat.totient_prime_pow_succ hp s
    have hpow : p ^ (r - 1) * p = p ^ r := by
      rw [← pow_succ]; congr 1; omega
    have heq : n * p ^ r = n * p ^ (r - 1) + n * (p ^ r).totient := by
      rw [htot, ← hpow]
      set X := p ^ (r - 1) with hXdef
      have hXp : X * p = X + X * (p - 1) := by
        have hp' : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
        conv_lhs => rw [← hp']
        ring
      calc n * (X * p) = n * (X + X * (p - 1)) := by rw [hXp]
        _ = n * X + n * (X * (p - 1)) := by ring
    rw [heq]
    have heuler : j ^ (p ^ r).totient ≡ 1 [MOD p ^ r] := Nat.ModEq.pow_totient hcop
    have heuler_n : j ^ ((p ^ r).totient * n) ≡ 1 [MOD p ^ r] := by
      have h2 := heuler.pow n
      simpa [pow_mul, one_pow] using h2
    have hfinal : j ^ (n * p ^ (r - 1)) * j ^ ((p ^ r).totient * n)
        ≡ j ^ (n * p ^ (r - 1)) * 1 [MOD p ^ r] :=
      Nat.ModEq.mul_left _ heuler_n
    calc j ^ (n * p ^ (r - 1) + n * (p ^ r).totient)
        = j ^ (n * p ^ (r - 1)) * j ^ ((p ^ r).totient * n) := by
          rw [← pow_add]; congr 1; ring
      _ ≡ j ^ (n * p ^ (r - 1)) * 1 [MOD p ^ r] := hfinal
      _ = j ^ (n * p ^ (r - 1)) := by ring

/-- `m! S(N,m)` satisfies the prime-power Gauss congruence. -/
theorem surjectionCount_gauss (m n p r : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    Int.ModEq (p ^ r : ℤ)
      (surjectionCount (n * p ^ r) m)
      (surjectionCount (n * p ^ (r - 1)) m) := by
  rw [surjectionCount_inclusionExclusion, surjectionCount_inclusionExclusion]
  apply Int.ModEq.sum
  intro j hj
  apply Int.ModEq.mul
  · exact Int.ModEq.refl _
  · exact_mod_cast power_gauss j n p r hp hn hr

/-- Every integral Stirling transform satisfies the (unshifted) Gauss congruences.

The sum for `n * p ^ (r - 1)` is padded with always-zero tail terms (since `stirlingSecond`
vanishes above its first argument) so both sides range over the same, larger index set; the
padded sum is then compared termwise against the `n * p ^ r` sum via `surjectionCount_gauss`. -/
theorem stirlingTransform_gauss (c : ℕ → ℤ) (n p r : ℕ)
    (hp : p.Prime) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    Int.ModEq (p ^ r : ℤ)
      (stirlingTransform c (n * p ^ r))
      (stirlingTransform c (n * p ^ (r - 1))) := by
  rw [stirlingTransform_eq_sum, stirlingTransform_eq_sum]
  have hN0N : n * p ^ (r - 1) ≤ n * p ^ r :=
    Nat.mul_le_mul_left n (Nat.pow_le_pow_right hp.pos (by omega))
  have hpad : ∑ m ∈ Finset.range (n * p ^ (r - 1) + 1), c m * surjectionCount (n * p ^ (r - 1)) m
      = ∑ m ∈ Finset.range (n * p ^ r + 1), c m * surjectionCount (n * p ^ (r - 1)) m := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : n * p ^ (r - 1) + 1 ≤ n * p ^ r + 1)]
    have htail : (∑ m ∈ Finset.Ico (n * p ^ (r - 1) + 1) (n * p ^ r + 1),
        c m * surjectionCount (n * p ^ (r - 1)) m) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hzero : Nat.stirlingSecond (n * p ^ (r - 1)) m = 0 :=
        Nat.stirlingSecond_eq_zero_of_lt (by
          have := (Finset.mem_Ico.mp hm).1
          omega)
      simp [surjectionCount, hzero]
    rw [htail, add_zero]
  rw [hpad]
  apply Int.ModEq.sum
  intro m _
  apply Int.ModEq.mul
  · exact Int.ModEq.refl _
  · exact surjectionCount_gauss m n p r hp hn hr

end A158690
