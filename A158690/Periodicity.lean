import A158690.Basic
import Mathlib.NumberTheory.PowModTotient

/-!
# Eventual periodicity modulo k

We prove the claimed period `φ(k)` directly.  The paper notes the stronger
Carmichael bound; mathlib's totient API makes the OEIS statement simpler to formalize.
-/

namespace A158690

open scoped BigOperators

/-- A sufficiently large factorial kills all higher Stirling-transform summands mod `k`. -/
theorem factorial_dvd_of_le {k M m : ℕ} (hk : k ∣ Nat.factorial M) (hMm : M ≤ m) :
    k ∣ Nat.factorial m := by
  exact dvd_trans hk (Nat.factorial_dvd_factorial hMm)

/-- Generic helper: if a base congruence with period `d` holds for all `n ≥ N`, then so does
the congruence with period `t * d`, for any multiplier `t`. This lets a single prime-power's
Euler period be stretched to any common multiple, in particular to `k.totient` itself. -/
private theorem modEq_period_mul {j m d N : ℕ} (h : ∀ n ≥ N, j ^ (n + d) ≡ j ^ n [MOD m]) :
    ∀ t, ∀ n ≥ N, j ^ (n + t * d) ≡ j ^ n [MOD m] := by
  intro t
  induction t with
  | zero => intro n _; simpa using Nat.ModEq.refl (j ^ n)
  | succ t iht =>
      intro n hn
      have heq : n + (t + 1) * d = (n + t * d) + d := by ring
      have step1 : j ^ (n + (t + 1) * d) ≡ j ^ (n + t * d) [MOD m] := by
        rw [heq]; exact h (n + t * d) (by omega)
      exact step1.trans (iht n hn)

/-- For fixed `j`, the power sequence is eventually periodic modulo `k` with period `φ(k)`.

Proved by peeling off one prime factor `p` of `k` at a time (via `ordProj`/`ordCompl`):
on the exact prime-power factor `p ^ e ‖ k`, the sequence is either eventually `≡ 0`
(if `p ∣ j`, once the exponent reaches `e`) or genuinely `φ(p^e)`-periodic from the start
(Euler's theorem, if `p` and `j` are coprime); the two coprime factors `p^e` and `k / p^e`
are then combined back into a single congruence mod `k` via CRT
(`Nat.modEq_and_modEq_iff_modEq_mul`), using that `φ(k) = φ(p^e) * φ(k/p^e)` is automatically
a common multiple of both component periods. -/
theorem pow_eventually_totient_periodic (j k : ℕ) (hk : 1 < k) :
    ∃ N, ∀ n ≥ N, j ^ (n + k.totient) ≡ j ^ n [MOD k] := by
  clear hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk0 : k = 0
    · subst hk0; exact ⟨0, fun n _ => by simp⟩
    by_cases hk1 : k = 1
    · subst hk1; exact ⟨0, fun n _ => Nat.modEq_one⟩
    obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
    set e := k.factorization p with hedef
    set k' := ordCompl[p] k with hk'def
    have he1 : 1 ≤ e := hp.factorization_pos_of_dvd hk0 hpk
    have hsplit : p ^ e * k' = k := Nat.ordProj_mul_ordCompl_eq_self k p
    have hcop : Nat.Coprime (p ^ e) k' := (Nat.coprime_ordCompl hp hk0).pow_left e
    have hpe2 : 2 ≤ p ^ e := by
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he1
    have hk'pos : 0 < k' := Nat.ordCompl_pos p hk0
    have hk'lt : k' < k := by
      calc k' = 1 * k' := (one_mul k').symm
        _ < p ^ e * k' := (Nat.mul_lt_mul_right hk'pos).mpr (by omega)
        _ = k := hsplit
    obtain ⟨N', hN'⟩ := ih k' hk'lt
    have htot : k.totient = (p ^ e).totient * k'.totient := by
      rw [← hsplit, Nat.totient_mul hcop]
    have hprime_pow : ∀ n ≥ e, j ^ (n + (p ^ e).totient) ≡ j ^ n [MOD p ^ e] := by
      intro n hn
      by_cases hj : p ∣ j
      · have hdvd1 : p ^ e ∣ j ^ n :=
          (pow_dvd_pow p hn).trans (pow_dvd_pow_of_dvd hj n)
        have hdvd2 : p ^ e ∣ j ^ (n + (p ^ e).totient) :=
          (pow_dvd_pow p (by omega)).trans (pow_dvd_pow_of_dvd hj (n + (p ^ e).totient))
        exact (Nat.modEq_zero_iff_dvd.mpr hdvd2).trans (Nat.modEq_zero_iff_dvd.mpr hdvd1).symm
      · have hcopj : j.Coprime (p ^ e) :=
          ((Nat.Prime.coprime_iff_not_dvd hp).2 hj).symm.pow_right e
        have heuler : j ^ (p ^ e).totient ≡ 1 [MOD p ^ e] := Nat.ModEq.pow_totient hcopj
        calc j ^ (n + (p ^ e).totient) = j ^ n * j ^ (p ^ e).totient := by rw [pow_add]
          _ ≡ j ^ n * 1 [MOD p ^ e] := Nat.ModEq.mul_left _ heuler
          _ = j ^ n := by ring
    refine ⟨max e N', fun n hn => ?_⟩
    have hnE : n ≥ e := le_trans (le_max_left _ _) hn
    have hnN' : n ≥ N' := le_trans (le_max_right _ _) hn
    have hmodpe : j ^ (n + k.totient) ≡ j ^ n [MOD p ^ e] := by
      rw [htot, mul_comm]
      exact modEq_period_mul hprime_pow k'.totient n hnE
    have hmodk' : j ^ (n + k.totient) ≡ j ^ n [MOD k'] := by
      rw [htot]
      exact modEq_period_mul hN' (p ^ e).totient n hnN'
    have hcombined := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hmodpe, hmodk'⟩
    rwa [hsplit] at hcombined

/-- Bala's first conjecture for every integral Stirling transform.

The sum for plain `n` is padded with always-zero tail terms (`stirlingSecond` vanishes above
its first argument) so both sides range over the same, larger index set `range (n+k.totient+1)`;
each padded term is then compared via `pow_eventually_totient_periodic`, after also disposing of
the high-`m` terms (`m ≥ M`) where `k ∣ m!` forces both sides to `≡ 0` outright. -/
theorem stirlingTransform_eventually_periodic (c : ℕ → ℤ) (k : ℕ) (hk : 1 < k) :
    ∃ N, ∀ n ≥ N,
      Int.ModEq (k : ℤ)
        (stirlingTransform c (n + k.totient))
        (stirlingTransform c n) := by
  classical
  obtain ⟨M, hM⟩ : ∃ M, k ∣ Nat.factorial M := by
    refine ⟨k, ?_⟩
    exact Nat.dvd_factorial (by omega) (by omega)
  choose Nj hNj using fun j : Fin M => pow_eventually_totient_periodic j k hk
  let N := Finset.univ.sup (fun j : Fin M => Nj j)
  refine ⟨max N M, ?_⟩
  intro n hn
  rw [stirlingTransform_eq_sum, stirlingTransform_eq_sum]
  have hpad : ∑ m ∈ Finset.range (n + 1), c m * surjectionCount n m
      = ∑ m ∈ Finset.range (n + k.totient + 1), c m * surjectionCount n m := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : n + 1 ≤ n + k.totient + 1)]
    have htail : (∑ m ∈ Finset.Ico (n + 1) (n + k.totient + 1), c m * surjectionCount n m) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hzero : Nat.stirlingSecond n m = 0 :=
        Nat.stirlingSecond_eq_zero_of_lt (by
          have := (Finset.mem_Ico.mp hm).1
          omega)
      simp [surjectionCount, hzero]
    rw [htail, add_zero]
  rw [hpad]
  apply Int.ModEq.sum
  intro m _
  by_cases hmM : M ≤ m
  · have hfac : k ∣ Nat.factorial m := factorial_dvd_of_le hM hmM
    have hfacZ : (k : ℤ) ∣ (Nat.factorial m : ℤ) := by exact_mod_cast hfac
    have hz1 : Int.ModEq (k : ℤ) (c m * surjectionCount (n + k.totient) m) 0 := by
      rw [Int.modEq_zero_iff_dvd, surjectionCount]
      exact Dvd.dvd.mul_left (hfacZ.mul_right _) (c m)
    have hz2 : Int.ModEq (k : ℤ) (c m * surjectionCount n m) 0 := by
      rw [Int.modEq_zero_iff_dvd, surjectionCount]
      exact Dvd.dvd.mul_left (hfacZ.mul_right _) (c m)
    exact hz1.trans hz2.symm
  · rw [surjectionCount_inclusionExclusion, surjectionCount_inclusionExclusion]
    apply Int.ModEq.mul
    · exact Int.ModEq.refl _
    · apply Int.ModEq.sum
      intro j hj
      apply Int.ModEq.mul
      · exact Int.ModEq.refl _
      · have hjm : j ≤ m := by simpa [Nat.lt_succ_iff] using hj
        have hjM : j < M := by omega
        have hnN : Nj ⟨j, hjM⟩ ≤ n := by
          have hsup : Nj ⟨j, hjM⟩ ≤ N :=
            Finset.le_sup (s := Finset.univ) (f := fun q : Fin M => Nj q) (by simp)
          omega
        exact_mod_cast hNj ⟨j, hjM⟩ n hnN

end A158690
