import A158690.Gauss

/-!
# Shift stability

At the coefficient level, differentiating `G(e^t-1)` replaces `G` by
`(1+y) G'(y)`.  The operator below is its coefficient action.
-/

namespace A158690

/-- Coefficient action of `(1+y) d/dy`. -/
def shiftCoeff (c : ℕ → ℤ) (m : ℕ) : ℤ :=
  (m + 1 : ℤ) * c (m + 1) + (m : ℤ) * c m

/-- One EGF derivative shifts the associated Stirling transform by one.

Expands both sides into their `m! S(n,m)`-weighted sums and matches them using the Stirling
recurrence `S(n+1,m+1) = (m+1) S(n,m+1) + S(n,m)`. The boundary terms this recurrence produces
(`m = 0` on one side, `m = n+1` on the other) vanish because `stirlingSecond` is `0` outside the
range `0 ≤ m ≤ n`, which is what lets both sides be matched as sums over the same `range (n+1)`. -/
theorem stirlingTransform_shiftCoeff (c : ℕ → ℤ) (n : ℕ) :
    stirlingTransform (shiftCoeff c) n = stirlingTransform c (n + 1) := by
  have hLHS : stirlingTransform (shiftCoeff c) n
      = (∑ m ∈ Finset.range (n + 1),
          c (m + 1) * (Nat.factorial (m + 1) : ℤ) * (Nat.stirlingSecond n m : ℤ))
        + (∑ m ∈ Finset.range (n + 1),
          c m * (m : ℤ) * (Nat.factorial m : ℤ) * (Nat.stirlingSecond n m : ℤ)) := by
    rw [stirlingTransform, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    show shiftCoeff c m * (Nat.factorial m : ℤ) * (Nat.stirlingSecond n m : ℤ) = _
    rw [shiftCoeff]
    push_cast [Nat.factorial_succ]
    ring
  have hAB : (∑ i ∈ Finset.range (n + 1),
        c (i + 1) * ((i : ℤ) + 1) * (Nat.factorial (i + 1) : ℤ) * (Nat.stirlingSecond n (i + 1) : ℤ))
      = ∑ m ∈ Finset.range (n + 1),
          c m * (m : ℤ) * (Nat.factorial m : ℤ) * (Nat.stirlingSecond n m : ℤ) := by
    have hLcast : (∑ i ∈ Finset.range (n + 1),
        c (i + 1) * ((i : ℤ) + 1) * (Nat.factorial (i + 1) : ℤ) * (Nat.stirlingSecond n (i + 1) : ℤ))
        = ∑ i ∈ Finset.range (n + 1),
            (fun t => c t * (t : ℤ) * (Nat.factorial t : ℤ) * (Nat.stirlingSecond n t : ℤ)) (i + 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [hLcast]
    set g := fun t => c t * (t : ℤ) * (Nat.factorial t : ℤ) * (Nat.stirlingSecond n t : ℤ) with hgdef
    have hstep1 := Finset.sum_range_succ' g (n + 1)
    have hstep2 := Finset.sum_range_succ g (n + 1)
    have hg0 : g 0 = 0 := by simp [hgdef]
    have hgn1 : g (n + 1) = 0 := by
      simp only [hgdef, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n)]
      ring
    rw [hg0, add_zero] at hstep1
    rw [hgn1, add_zero] at hstep2
    rw [← hstep1, hstep2]
  have hRHS : stirlingTransform c (n + 1)
      = (∑ i ∈ Finset.range (n + 1),
          c (i + 1) * ((i : ℤ) + 1) * (Nat.factorial (i + 1) : ℤ) * (Nat.stirlingSecond n (i + 1) : ℤ))
        + (∑ i ∈ Finset.range (n + 1),
          c (i + 1) * (Nat.factorial (i + 1) : ℤ) * (Nat.stirlingSecond n i : ℤ)) := by
    rw [stirlingTransform]
    have hf0 : c 0 * (Nat.factorial 0 : ℤ) * (Nat.stirlingSecond (n + 1) 0 : ℤ) = 0 := by simp
    have hpull := Finset.sum_range_succ'
      (fun m => c m * (Nat.factorial m : ℤ) * (Nat.stirlingSecond (n + 1) m : ℤ)) (n + 1)
    rw [hf0, add_zero] at hpull
    rw [hpull, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hrec : (Nat.stirlingSecond (n + 1) (i + 1) : ℤ)
        = ((i : ℤ) + 1) * (Nat.stirlingSecond n (i + 1) : ℤ) + (Nat.stirlingSecond n i : ℤ) := by
      exact_mod_cast Nat.stirlingSecond_succ_succ n i
    rw [hrec]
    ring
  rw [hLHS, hRHS, hAB]
  ring

/-- Iterated coefficient operator corresponding to `i` derivatives. -/
def shiftCoeffIter (i : ℕ) (c : ℕ → ℤ) : ℕ → ℤ :=
  (shiftCoeff^[i]) c

/-- Iterating the previous lemma shifts the sequence by `i`. -/
theorem stirlingTransform_shiftCoeffIter (i : ℕ) (c : ℕ → ℤ) (n : ℕ) :
    stirlingTransform (shiftCoeffIter i c) n = stirlingTransform c (n + i) := by
  induction i generalizing c with
  | zero => simp [shiftCoeffIter]
  | succ i ih =>
      rw [shiftCoeffIter, Function.iterate_succ_apply, ← shiftCoeffIter]
      rw [ih (shiftCoeff c), stirlingTransform_shiftCoeff]
      congr 1

/-- All shifts satisfy Bala's Gauss congruence. -/
theorem stirlingTransform_shifted_gauss (c : ℕ → ℤ) (i n p r : ℕ)
    (hp : p.Prime) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    Int.ModEq (p ^ r : ℤ)
      (stirlingTransform c (n * p ^ r + i))
      (stirlingTransform c (n * p ^ (r - 1) + i)) := by
  rw [← stirlingTransform_shiftCoeffIter i c (n * p ^ r),
      ← stirlingTransform_shiftCoeffIter i c (n * p ^ (r - 1))]
  exact stirlingTransform_gauss (shiftCoeffIter i c) n p r hp hn hr

end A158690
