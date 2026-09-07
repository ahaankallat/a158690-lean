import Mathlib

/-!
# The Stirling-transform class behind A158690

For an integer coefficient sequence `c`, define

  b(n) = sum_{m <= n} c(m) m! S(n,m).

This is the coefficient sequence of `G(exp t - 1)` when
`G(y) = sum c(m) y^m`.
-/

namespace A158690

open scoped BigOperators

/-- The integral Stirling transform occurring in `G(exp t - 1)`. -/
def stirlingTransform (c : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (n + 1), c m * (Nat.factorial m : ℤ) * (Nat.stirlingSecond n m : ℤ)

/-- A convenient integer-valued version of `m! S(n,m)`. -/
def surjectionCount (n m : ℕ) : ℤ :=
  (Nat.factorial m : ℤ) * (Nat.stirlingSecond n m : ℤ)

@[simp] theorem surjectionCount_eq (n m : ℕ) :
    surjectionCount n m = (Nat.factorial m : ℤ) * (Nat.stirlingSecond n m : ℤ) := rfl

/-- The reversed alternating sum of binomial coefficients: `Σ_l (-1)^(k-l) C(k,l)` is `1`
when `k = 0` and `0` otherwise. Obtained from `Int.alternating_sum_range_choose` by
reflecting the summation index `l ↦ k - l`. -/
private theorem alternating_sum_range_choose_rev (k : ℕ) :
    (∑ l ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - l) * (Nat.choose k l : ℤ))
      = if k = 0 then 1 else 0 := by
  have hreflect := Finset.sum_range_reflect (fun x => (-1 : ℤ) ^ x * (Nat.choose k x : ℤ)) (k + 1)
  simp only [Nat.add_sub_cancel] at hreflect
  have hsymm : ∀ j ∈ Finset.range (k + 1),
      (-1 : ℤ) ^ (k - j) * (Nat.choose k (k - j) : ℤ)
        = (-1 : ℤ) ^ (k - j) * (Nat.choose k j : ℤ) := by
    intro j hj
    have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
    rw [Nat.choose_symm hjk]
  rw [Finset.sum_congr rfl hsymm] at hreflect
  rw [hreflect, Int.alternating_sum_range_choose]

/-- The double-binomial orthogonality relation driving the Stirling inclusion-exclusion
formula: `Σ_j (-1)^(m-j) C(m,j) C(j,i)` is `1` when `i = m` and `0` otherwise. Proved via
the subset-of-subset identity `Nat.choose_mul` and `alternating_sum_range_choose_rev`. -/
private theorem sum_choose_mul_choose_eq_ite (m i : ℕ) :
    (∑ j ∈ Finset.range (m + 1),
      (-1 : ℤ) ^ (m - j) * (Nat.choose m j : ℤ) * (Nat.choose j i : ℤ))
      = if i = m then 1 else 0 := by
  by_cases him : i ≤ m
  · rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le i) (by omega : i ≤ m + 1)]
    have hzero : (∑ j ∈ Finset.Ico 0 i,
        (-1 : ℤ) ^ (m - j) * (Nat.choose m j : ℤ) * (Nat.choose j i : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hji : j < i := (Finset.mem_Ico.mp hj).2
      rw [Nat.choose_eq_zero_of_lt hji]
      simp
    rw [hzero, zero_add]
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : m + 1 - i = (m - i) + 1 := by omega
    rw [hlen]
    have hterm : ∀ l ∈ Finset.range ((m - i) + 1),
        (-1 : ℤ) ^ (m - (i + l)) * (Nat.choose m (i + l) : ℤ) * (Nat.choose (i + l) i : ℤ)
          = (Nat.choose m i : ℤ) * ((-1 : ℤ) ^ ((m - i) - l) * (Nat.choose (m - i) l : ℤ)) := by
      intro l hl
      have hlmi : l ≤ m - i := by simpa [Nat.lt_succ_iff] using hl
      have hchoose : m.choose (i + l) * (i + l).choose i = m.choose i * (m - i).choose l := by
        have h := Nat.choose_mul (n := m) (k := i + l) (s := i) (Nat.le_add_right i l)
        simpa using h
      have hsub : m - (i + l) = (m - i) - l := by omega
      rw [hsub]
      have hcast : (Nat.choose m (i + l) : ℤ) * (Nat.choose (i + l) i : ℤ)
          = (Nat.choose m i : ℤ) * (Nat.choose (m - i) l : ℤ) := by
        exact_mod_cast hchoose
      have hgoal : (-1 : ℤ) ^ ((m - i) - l) *
          ((Nat.choose m (i + l) : ℤ) * (Nat.choose (i + l) i : ℤ))
          = (Nat.choose m i : ℤ) * ((-1 : ℤ) ^ ((m - i) - l) * (Nat.choose (m - i) l : ℤ)) := by
        rw [hcast]; ring
      linarith [hgoal]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, alternating_sum_range_choose_rev]
    by_cases hmi : m - i = 0
    · have hi : i = m := by omega
      simp [hi]
    · have hi : i ≠ m := by omega
      simp [hmi, hi]
  · have hne : i ≠ m := by omega
    rw [if_neg hne]
    apply Finset.sum_eq_zero
    intro j hj
    have hjm : j ≤ m := by simpa [Nat.lt_succ_iff] using hj
    have hji : j < i := by omega
    rw [Nat.choose_eq_zero_of_lt hji]
    simp

/-- The finite-difference / inclusion-exclusion expression for `m! S(n,m)`.

Derived from mathlib's `Nat.pow_eq_sum_stirlingSecond_mul_descFactorial` (every power is a
linear combination of descending factorials with Stirling-second coefficients) by expanding
each `j^n` in the target sum, swapping the order of summation, and collapsing via the
binomial-orthogonality relation `sum_choose_mul_choose_eq_ite`.
-/
theorem surjectionCount_inclusionExclusion (n m : ℕ) :
    surjectionCount n m =
      ∑ j ∈ Finset.range (m + 1),
        (-1 : ℤ) ^ (m - j) * (Nat.choose m j : ℤ) * (j : ℤ) ^ n := by
  rw [surjectionCount]
  have hpow : ∀ j : ℕ, (j : ℤ) ^ n =
      ∑ i ∈ Finset.range (n + 1),
        (Nat.stirlingSecond n i : ℤ) * (Nat.factorial i : ℤ) * (Nat.choose j i : ℤ) := by
    intro j
    have hnat := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial j n
    have hcast : (j : ℤ) ^ n =
        ∑ i ∈ Finset.range (n + 1),
          (Nat.stirlingSecond n i : ℤ) * (j.descFactorial i : ℤ) := by
      exact_mod_cast hnat
    rw [hcast]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  symm
  calc
    ∑ j ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - j) * (Nat.choose m j : ℤ) * (j : ℤ) ^ n
        = ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (n + 1),
            (-1 : ℤ) ^ (m - j) * (Nat.choose m j : ℤ) *
              ((Nat.stirlingSecond n i : ℤ) * (Nat.factorial i : ℤ) * (Nat.choose j i : ℤ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hpow j, Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
            (-1 : ℤ) ^ (m - j) * (Nat.choose m j : ℤ) *
              ((Nat.stirlingSecond n i : ℤ) * (Nat.factorial i : ℤ) * (Nat.choose j i : ℤ)) := by
        rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range (n + 1),
          (Nat.stirlingSecond n i : ℤ) * (Nat.factorial i : ℤ) *
            (∑ j ∈ Finset.range (m + 1),
              (-1 : ℤ) ^ (m - j) * (Nat.choose m j : ℤ) * (Nat.choose j i : ℤ)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ i ∈ Finset.range (n + 1),
          (Nat.stirlingSecond n i : ℤ) * (Nat.factorial i : ℤ) * (if i = m then 1 else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sum_choose_mul_choose_eq_ite]
    _ = (Nat.factorial m : ℤ) * (Nat.stirlingSecond n m : ℤ) := by
        by_cases hmn : m ≤ n
        · rw [Finset.sum_eq_single m]
          · simp; ring
          · intro i _ hine
            simp [hine]
          · intro hmr
            exact absurd (Finset.mem_range.mpr (by omega)) hmr
        · have hzero : Nat.stirlingSecond n m = 0 := Nat.stirlingSecond_eq_zero_of_lt (by omega)
          rw [hzero]
          push_cast
          rw [mul_zero]
          apply Finset.sum_eq_zero
          intro i hi
          have hine : i ≠ m := by
            intro heq; subst heq
            have hile : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
            omega
          simp [hine]

/-- Only terms `m ≤ n` occur in the Stirling transform. -/
theorem stirlingTransform_eq_sum (c : ℕ → ℤ) (n : ℕ) :
    stirlingTransform c n =
      ∑ m ∈ Finset.range (n + 1), c m * surjectionCount n m := by
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [surjectionCount]
  ring

end A158690
