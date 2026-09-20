/-
# A scaling limit for the weighted mean square of the truncated Möbius divisor sum
## Lean 4 / Mathlib formalization exploration (first pass)

Companion to the manuscript (R. Menezes, Sep 19 2026):

  M(q,n) := ∑_{d ∣ q, d ≤ n} μ(d),        S(n) := ∑_{q > n} M(q,n)² / q².

This file proves **Theorem 1** end-to-end: the exact positive decomposition
`S(n) = ζ(2)⁻¹ ∑_{d>n} μ(d)²/J₂(d) + ζ(2) ∑_{d≤n} J₂(d) E_d(n)²` and the bound
`0 ≤ S(n) < (1 + 4ζ(2))/n`, including all supporting definitions and elementary
lemmas (Gram identity, Euler products for ζ(2)⁻¹ and μ²/J₂, tail bounds).
Theorems 2 and 3 remain `sorry`-ed statements: they depend on the
de la Bretèche–Dress–Tenenbaum (2020) inputs that are not in Mathlib.

### What comes from Mathlib vs what is custom

Mathlib provides:
  * `ArithmeticFunction.moebius` (notation `μ` after `open ArithmeticFunction`),
    as an `ArithmeticFunction ℤ`, with `μ n = 0` on non-squarefree `n`,
    multiplicativity on coprime arguments, and `∑ d ∈ n.divisors, μ d = 1 ↔ n = 1`
    (the μ ∗ ζ = δ identity).
  * `Nat.divisors`, `Nat.primeFactors`, `Nat.gcd`, `Nat.lcm`, `Squarefree`.
  * `riemannZeta : ℂ → ℂ` and `riemannZeta_two : riemannZeta 2 = π²/6`;
    we take the real part as `zeta2`.
  * `∑'` (tsum), `Tendsto`, `atTop`, `𝓝`, finite-sum rearrangement lemmas,
    Tonelli/Fubini for nonnegative series (`ENNReal` or summability machinery).

Custom to this file (not in Mathlib):
  * `truncMoebius M` — the truncated divisor sum itself.
  * `S` — the q⁻²-weighted moving-cutoff tail (an infinite real series).
  * `jordan2` — the second Jordan totient (Mathlib has `Nat.totient` = J₁ only).
  * `A`, `Ainf`, `E` — the partial / infinite Möbius-over-multiples sums.
  * `kappa`, `D`, `Cconst` — the block constants and the scaling-limit constant.
  * `calL` — the BDT logarithmic saving exp((log y)^{3/5}/(log log y)^{1/5}).
  * `DITconst` — the Dress–Iwaniec–Tenenbaum constant (opaque; its defining
    limit is deep analytic input).
  * `bdt_uniform_mean_square`, `bdt_global` — the de la Bretèche–Dress–Tenenbaum
    (2020) inputs, stated as `sorry`-ed theorems: they are NOT in Mathlib and
    are the hard analytic ingredient everything else is conditioned on.
-/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Data.Finset.NatDivisors

open ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta Filter Topology
open scoped BigOperators

-- `open Classical` so `if … then … else` may test any proposition inside
-- noncomputable definitions (coprimality conditions etc.).
open Classical

namespace TruncMoebius

/-! ## Basic arithmetic input: ζ(2) as a real number -/

/-- ζ(2) as a real number. Mathlib's `riemannZeta_two` identifies this with π²/6. -/
noncomputable def zeta2 : ℝ := (riemannZeta 2).re

theorem zeta2_eq : zeta2 = Real.pi ^ 2 / 6 := by
  have h : riemannZeta 2 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
    rw [riemannZeta_two]
    norm_cast
  rw [zeta2, h, Complex.ofReal_re]

/-! ## The truncated Möbius divisor sum and its weighted tail -/

/-- The truncated Möbius divisor sum `M(q,n) = ∑_{d ∣ q, d ≤ n} μ(d)`, as an integer.
Uses Mathlib's `ArithmeticFunction.moebius` and `Nat.divisors`. -/
noncomputable def M (q n : ℕ) : ℤ :=
  ∑ d ∈ q.divisors.filter (· ≤ n), μ d

/-- Paper, easy fact: `M(1,n) = 1` for `n ≥ 1` (only `d = 1` divides `1`). -/
theorem M_one (n : ℕ) (hn : 1 ≤ n) : M 1 n = 1 := by
  unfold M
  rw [Nat.divisors_one,
    Finset.filter_true_of_mem (fun x hx => by rw [Finset.mem_singleton] at hx; omega),
    Finset.sum_singleton]
  exact moebius_apply_one

/-- Paper, easy fact: complete divisor cancellation — for `1 < q ≤ n`,
`M(q,n) = ∑_{d ∣ q} μ(d) = 0`. Routine from Mathlib's μ ∗ ζ = δ identity
(`ArithmeticFunction.moebius_mul_zeta`). -/
theorem M_eq_zero_of_one_lt_le {q n : ℕ} (hq : 1 < q) (hqn : q ≤ n) : M q n = 0 := by
  have hfilter : q.divisors.filter (· ≤ n) = q.divisors := by
    apply Finset.filter_true_of_mem
    intro d hd
    exact (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)).trans hqn
  unfold M
  rw [hfilter]
  have h : ((μ * ζ : ArithmeticFunction ℤ) q : ℤ) = (1 : ArithmeticFunction ℤ) q := by
    rw [moebius_mul_coe_zeta]
  rw [ArithmeticFunction.mul_apply,
    ArithmeticFunction.one_apply_ne (show q ≠ 1 by omega),
    Nat.sum_divisorsAntidiagonal (fun x y => (μ x : ℤ) * (((ζ : ArithmeticFunction ℤ)) y : ℤ))] at h
  have hzeta : ∀ d ∈ q.divisors, ((ζ : ArithmeticFunction ℤ) (q / d) : ℤ) = 1 := by
    intro d hd
    have hdvd : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hne : q / d ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hdpos)
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hne, Nat.cast_one]
  have h' : ∑ d ∈ q.divisors, (μ d : ℤ)
      = ∑ d ∈ q.divisors, (μ d : ℤ) * ((ζ : ArithmeticFunction ℤ) (q / d) : ℤ) := by
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [hzeta d hd, mul_one]
  rw [h']
  exact h

/-- Pointwise bound: `|M(q,n)| ≤ n` (the sum has at most `n` terms, each in `{-1,0,1}`). -/
theorem M_abs_le (q n : ℕ) : |(M q n : ℝ)| ≤ n := by
  have h1 : |M q n| ≤ ((q.divisors.filter (· ≤ n)).card : ℤ) := by
    unfold M
    calc |∑ d ∈ q.divisors.filter (· ≤ n), μ d|
        ≤ ∑ d ∈ q.divisors.filter (· ≤ n), |(μ d : ℤ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ q.divisors.filter (· ≤ n), (1 : ℤ) :=
          Finset.sum_le_sum fun d _ => abs_moebius_le_one
      _ = ((q.divisors.filter (· ≤ n)).card : ℤ) := by simp
  have hsub : q.divisors.filter (· ≤ n) ⊆ Finset.Icc 1 n := by
    intro d hd
    rw [Finset.mem_filter] at hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd.1, hd.2⟩
  have hcard : (q.divisors.filter (· ≤ n)).card ≤ n := by
    calc (q.divisors.filter (· ≤ n)).card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hsub
      _ = n := by rw [Nat.card_Icc]; omega
  calc |(M q n : ℝ)| = ((|M q n| : ℤ) : ℝ) := (Int.cast_abs).symm
    _ ≤ ((q.divisors.filter (· ≤ n)).card : ℝ) := by exact_mod_cast h1
    _ ≤ (n : ℝ) := by exact_mod_cast hcard

/-- The summand of `S` is summable for each fixed `n` (comparison with `n²/q²`). -/
theorem summable_M_sq_div (n : ℕ) :
    Summable (fun q : ℕ => (M q n : ℝ) ^ 2 / (q : ℝ) ^ 2) := by
  have hbase : Summable (fun q : ℕ => (n : ℝ) ^ 2 / (q : ℝ) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h2 := Summable.mul_left ((n : ℝ) ^ 2) h
    convert h2 using 1
    ext q
    rw [mul_one_div]
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_) hbase
  by_cases hq : q = 0
  · simp [hq]
  · have hM : |(M q n : ℝ)| ≤ (n : ℝ) := M_abs_le q n
    have hsq : (M q n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have hh := pow_le_pow_left₀ (abs_nonneg _) hM 2
      rwa [sq_abs] at hh
    gcongr

/-- The q⁻²-weighted tail `S(n) = ∑_{q > n} M(q,n)²/q²`, a nonnegative real series.
The indicator form keeps the `tsum` over all of `ℕ` total. -/
noncomputable def S (n : ℕ) : ℝ :=
  ∑' q : ℕ, if n < q then (M q n : ℝ) ^ 2 / (q : ℝ) ^ 2 else 0

/-- The full Parseval/Gram sum `∑_{q ≥ 1} M(q,n)²/q² = 1 + S(n)` (paper eq. (2)).
The `q ≤ n` terms vanish by `M_eq_zero_of_one_lt_le`, apart from `q = 1`. -/
theorem parseval_eq_one_add_S (n : ℕ) (hn : 1 ≤ n) :
    ∑' q : ℕ, (M q n : ℝ) ^ 2 / (q : ℝ) ^ 2 = 1 + S n := by
  have hpoint : ∀ q : ℕ, (M q n : ℝ) ^ 2 / (q : ℝ) ^ 2 =
      (if n < q then (M q n : ℝ) ^ 2 / (q : ℝ) ^ 2 else 0) + (if q = 1 then 1 else 0) := by
    intro q
    by_cases hqn : n < q
    · have hq1 : q ≠ 1 := by omega
      simp [hqn, hq1]
    · have hg : (if n < q then (M q n : ℝ) ^ 2 / (q : ℝ) ^ 2 else 0) = 0 := by simp [hqn]
      rw [hg, zero_add]
      by_cases hq1 : q = 1
      · subst hq1
        rw [M_one n hn]
        norm_num
      · have hq0 : (M q n : ℝ) = 0 := by
          rcases eq_or_ne q 0 with rfl | h0
          · simp [M, Nat.divisors_zero]
          · have h1q : 1 < q := by omega
            have hm := M_eq_zero_of_one_lt_le h1q (by omega : q ≤ n)
            exact_mod_cast hm
        rw [hq0]
        simp [hq1]
  have hgsum : Summable (fun q : ℕ => if n < q then (M q n : ℝ) ^ 2 / (q : ℝ) ^ 2 else 0) := by
    refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) (summable_M_sq_div n)
    · by_cases h : n < q <;> simp [h] <;> positivity
    · by_cases h : n < q <;> simp [h] <;> positivity
  have hbsum : Summable (fun q : ℕ => if q = 1 then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := {1})
    intro q hq
    simp at hq
    simp [hq]
  have hadd := hgsum.tsum_add hbsum
  rw [tsum_congr (fun q => hpoint q), hadd]
  have hSg : S n = ∑' q : ℕ, (if n < q then (M q n : ℝ) ^ 2 / (q : ℝ) ^ 2 else 0) := rfl
  rw [hSg]
  have hb1 : ∑' q : ℕ, (if q = 1 then (1 : ℝ) else 0) = 1 := by
    rw [tsum_eq_single 1 (fun q hq => by simp [hq])]
    simp
  rw [hb1, add_comm]

/-! ## Theorem 1: the exact positive decomposition -/

/-- Second Jordan totient as a real number, `J₂(d) = d² ∏_{p ∣ d} (1 - p⁻²)`.
Mathlib has `Nat.totient` (J₁) but not the general Jordan totient, so this is custom.
Key bounds used in the paper: `d²/ζ(2) ≤ J₂(d) ≤ d²`. -/
noncomputable def jordan2 (d : ℕ) : ℝ :=
  d ^ 2 * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹ ^ 2)

/-- `A_d(x) = ∑_{k ≤ x, d ∣ k} μ(k)/k²` (paper eq. (7)). -/
noncomputable def A (d : ℕ) (x : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 x, if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0

/-- `A_d(∞)`, the completed absolutely convergent series. -/
noncomputable def Ainf (d : ℕ) : ℝ :=
  ∑' k : ℕ, if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0

/-- `E_d(n) = A_d(n) - A_d(∞)` (paper eq. (7)). -/
noncomputable def E (d : ℕ) (n : ℕ) : ℝ :=
  A d n - Ainf d


/-- A prime-power factor is nonzero: `1 - p⁻² ≠ 0` for `p` prime. -/
theorem one_sub_inv_sq_prime_ne_zero {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) - (p : ℝ)⁻¹ ^ 2 ≠ 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlt : (p : ℝ)⁻¹ ^ 2 < 1 := by
    have h1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    have h2 : (p : ℝ)⁻¹ ^ 2 < (1 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ h1 (by positivity) (n := 2) (by norm_num)
    simpa using h2
  exact sub_ne_zero.mpr (ne_of_gt hlt)

/-- `μ(n)/n²` as a real arithmetic function, for the Euler-product machinery. -/
noncomputable def moebiusDivSq : ArithmeticFunction ℝ :=
  ⟨fun n => (μ n : ℝ) / (n : ℝ) ^ 2, by simp⟩

@[simp] theorem moebiusDivSq_apply (n : ℕ) :
    moebiusDivSq n = (μ n : ℝ) / (n : ℝ) ^ 2 := rfl

theorem moebiusDivSq_isMultiplicative : moebiusDivSq.IsMultiplicative := by
  constructor
  · rw [moebiusDivSq_apply]; simp
  · intro m n hmn
    rw [moebiusDivSq_apply, moebiusDivSq_apply, moebiusDivSq_apply,
      isMultiplicative_moebius.map_mul_of_coprime hmn]
    push_cast
    rw [mul_pow, div_mul_div_comm]

theorem summable_norm_moebiusDivSq : Summable fun n => ‖moebiusDivSq n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (Real.summable_one_div_nat_pow.mpr one_lt_two)
  rw [moebiusDivSq_apply, Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  by_cases h0 : n = 0
  · subst h0; simp
  · have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero h0) 2
    have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    gcongr

/-- The Möbius-over-coprime series as a real arithmetic function. -/
noncomputable def moebiusCoprime (d : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m.Coprime d then (μ m : ℝ) / (m : ℝ) ^ 2 else 0, by split_ifs <;> simp⟩

@[simp] theorem moebiusCoprime_apply (d m : ℕ) :
    moebiusCoprime d m = if m.Coprime d then (μ m : ℝ) / (m : ℝ) ^ 2 else 0 := rfl

theorem moebiusCoprime_isMultiplicative (d : ℕ) : (moebiusCoprime d).IsMultiplicative := by
  constructor
  · rw [moebiusCoprime_apply, if_pos (Nat.coprime_one_left d)]; simp
  · intro m n hmn
    by_cases hmd : m.Coprime d <;> by_cases hnd : n.Coprime d
    · rw [moebiusCoprime_apply, if_pos (Nat.coprime_mul_iff_left.mpr ⟨hmd, hnd⟩),
        moebiusCoprime_apply, if_pos hmd, moebiusCoprime_apply, if_pos hnd,
        isMultiplicative_moebius.map_mul_of_coprime hmn]
      push_cast
      rw [mul_pow, div_mul_div_comm]
    · rw [moebiusCoprime_apply, if_neg (fun h => hnd (Nat.coprime_mul_iff_left.mp h).2),
        moebiusCoprime_apply, if_pos hmd, moebiusCoprime_apply, if_neg hnd, mul_zero]
    · rw [moebiusCoprime_apply, if_neg (fun h => hmd (Nat.coprime_mul_iff_left.mp h).1),
        moebiusCoprime_apply, if_neg hmd, moebiusCoprime_apply, if_pos hnd, zero_mul]
    · rw [moebiusCoprime_apply, if_neg (fun h => hmd (Nat.coprime_mul_iff_left.mp h).1),
        moebiusCoprime_apply, if_neg hmd, moebiusCoprime_apply, if_neg hnd, mul_zero]

theorem summable_norm_moebiusCoprime (d : ℕ) :
    Summable fun m => ‖moebiusCoprime d m‖ := by
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    summable_norm_moebiusDivSq
  by_cases h : m.Coprime d
  · rw [moebiusCoprime_apply, if_pos h, moebiusDivSq_apply]
  · rw [moebiusCoprime_apply, if_neg h, norm_zero]
    exact norm_nonneg _

/-- The local factor of the `μ/n²` Euler product at a prime: `1 - p⁻²`. -/
theorem tsum_moebiusDivSq_prime_pow (p : Nat.Primes) :
    ∑' e : ℕ, moebiusDivSq ((p : ℕ) ^ e) = 1 - ((p : ℕ) : ℝ)⁻¹ ^ 2 := by
  have hvan : ∀ e : ℕ, e ∉ ({0, 1} : Finset ℕ) → moebiusDivSq ((p : ℕ) ^ e) = 0 := by
    intro e he
    have h2 : 2 ≤ e := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
      omega
    have hnsq : ¬ Squarefree ((p : ℕ) ^ e) := by
      intro hsq
      have hpdvd : (p : ℕ) * (p : ℕ) ∣ (p : ℕ) ^ e := by
        rw [← pow_two]; exact pow_dvd_pow _ h2
      have hu : IsUnit (p : ℕ) := hsq _ hpdvd
      rw [Nat.isUnit_iff] at hu
      have h2le := Nat.Prime.two_le p.2
      omega
    rw [moebiusDivSq_apply, moebius_eq_zero_of_not_squarefree hnsq]
    simp
  rw [tsum_eq_sum hvan, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  have h0 : moebiusDivSq ((p : ℕ) ^ 0) = 1 := by
    rw [pow_zero, moebiusDivSq_apply]; simp
  have h1 : moebiusDivSq ((p : ℕ) ^ 1) = -1 / ((p : ℕ) : ℝ) ^ 2 := by
    rw [pow_one, moebiusDivSq_apply, moebius_apply_prime p.2]
    push_cast; ring
  rw [h0, h1, inv_pow, inv_eq_one_div]
  ring

/-- The local factor of the coprime-restricted series: `1` if `p ∣ d`, else `1 - p⁻²`. -/
theorem tsum_moebiusCoprime_prime_pow (d : ℕ) (p : Nat.Primes) :
    ∑' e : ℕ, moebiusCoprime d ((p : ℕ) ^ e)
      = if (p : ℕ) ∣ d then 1 else 1 - ((p : ℕ) : ℝ)⁻¹ ^ 2 := by
  by_cases hpd : (p : ℕ) ∣ d
  · rw [if_pos hpd, tsum_eq_single 0]
    · rw [pow_zero, moebiusCoprime_apply, if_pos (Nat.coprime_one_left d)]
      simp
    · intro e he
      have hpe : (p : ℕ) ∣ (p : ℕ) ^ e := dvd_pow_self _ he
      have hnot : ¬ ((p : ℕ) ^ e).Coprime d := by
        intro hco
        exact ((Nat.Prime.coprime_iff_not_dvd p.2).mp (Nat.Coprime.coprime_dvd_left hpe hco)) hpd
      rw [moebiusCoprime_apply, if_neg hnot]
  · rw [if_neg hpd]
    have hvan : ∀ e : ℕ, e ∉ ({0, 1} : Finset ℕ) →
        moebiusCoprime d ((p : ℕ) ^ e) = 0 := by
      intro e he
      have h2 : 2 ≤ e := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
        omega
      have hnsq : ¬ Squarefree ((p : ℕ) ^ e) := by
        intro hsq
        have hpdvd : (p : ℕ) * (p : ℕ) ∣ (p : ℕ) ^ e := by
          rw [← pow_two]; exact pow_dvd_pow _ h2
        have hu : IsUnit (p : ℕ) := hsq _ hpdvd
        rw [Nat.isUnit_iff] at hu
        have h2le := Nat.Prime.two_le p.2
        omega
      rw [moebiusCoprime_apply, moebius_eq_zero_of_not_squarefree hnsq]
      split_ifs <;> simp
    rw [tsum_eq_sum hvan, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    have hcp : (p : ℕ).Coprime d := (Nat.Prime.coprime_iff_not_dvd p.2).mpr hpd
    have h0 : moebiusCoprime d ((p : ℕ) ^ 0) = 1 := by
      rw [pow_zero, moebiusCoprime_apply, if_pos (Nat.coprime_one_left d)]
      simp
    have h1 : moebiusCoprime d ((p : ℕ) ^ 1) = -1 / ((p : ℕ) : ℝ) ^ 2 := by
      rw [pow_one, moebiusCoprime_apply, if_pos hcp, moebius_apply_prime p.2]
      push_cast; ring
    rw [h0, h1, inv_pow, inv_eq_one_div]
    ring

-- The L-series of `μ` at `s = 2`, identified with the real series `∑' μ(n)/n²`.
open scoped LSeries.notation in
theorem LSeries_moebius_two_eq :
    LSeries ↗μ 2 = ((∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  show (∑' n : ℕ, LSeries.term ↗μ 2 n) = _
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  have hcp : ∀ z : ℂ, z ^ (2 : ℂ) = z ^ 2 := fun z => by
    have h2 : ((2 : ℕ) : ℂ) = (2 : ℂ) := by norm_num
    rw [← h2, Complex.cpow_natCast]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  · simp only [LSeries.term_def, hn, if_false, hcp]
    norm_cast

-- `∑' μ(n)/n² = 1/ζ(2)`, in multiplicative form.
open scoped LSeries.notation in
theorem moebius_tsum_mul_zeta2 :
    (∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ 2) * zeta2 = 1 := by
  have hre : 1 < (2 : ℂ).re := by simp
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hre
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hre, LSeries_moebius_two_eq] at h
  have hrz : riemannZeta 2 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
    rw [riemannZeta_two]; norm_cast
  rw [hrz, ← Complex.ofReal_mul] at h
  have h' : Real.pi ^ 2 / 6 * (∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ 2) = 1 := by
    exact_mod_cast h
  rw [zeta2_eq, mul_comm]
  exact h'

/-- The full Euler product `∏_p (1 - p⁻²) = 1/ζ(2)`. -/
theorem tprod_one_sub_inv_sq_primes :
    ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2) = zeta2⁻¹ := by
  have hEP := moebiusDivSq_isMultiplicative.eulerProduct_tprod summable_norm_moebiusDivSq
  simp only [tsum_moebiusDivSq_prime_pow] at hEP
  simp only [moebiusDivSq_apply] at hEP
  rw [hEP]
  exact eq_inv_of_mul_eq_one_left moebius_tsum_mul_zeta2

theorem multipliable_one_sub_inv_sq_primes :
    Multipliable fun p : Nat.Primes => 1 - ((p : ℕ) : ℝ)⁻¹ ^ 2 :=
  (multipliable_congr (fun p => tsum_moebiusDivSq_prime_pow p)).mp
    (moebiusDivSq_isMultiplicative.eulerProduct_hasProd
      summable_norm_moebiusDivSq).multipliable

/-- The coprime-restricted series as a prime product. -/
theorem tsum_moebiusCoprime (d : ℕ) :
    ∑' m : ℕ, moebiusCoprime d m
      = ∏' p : Nat.Primes, if (p : ℕ) ∣ d then 1 else 1 - ((p : ℕ) : ℝ)⁻¹ ^ 2 := by
  rw [← (moebiusCoprime_isMultiplicative d).eulerProduct_tprod
    (summable_norm_moebiusCoprime d)]
  exact tprod_congr fun p => tsum_moebiusCoprime_prime_pow d p

/-- The primes dividing `d`, as a `Finset Nat.Primes` (nominally typed, to keep
tprod/prod rewriting inside `Nat.Primes`). -/
def primesDvd (d : ℕ) : Finset Nat.Primes :=
  d.primeFactors.subtype (fun p : ℕ => Nat.Prime p)

/-- Split the coprime-restricted prime product into the full product and the `p ∣ d` part. -/
theorem tprod_split (d : ℕ) (hd0 : d ≠ 0) :
    ∏' p : Nat.Primes, (if (p : ℕ) ∣ d then (1 : ℝ) else 1 - ((p : ℕ) : ℝ)⁻¹ ^ 2)
      = (∏' p : Nat.Primes, (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2))
        * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹ ^ 2)⁻¹ := by
  have hFGH : ∀ p : Nat.Primes,
      (if (p : ℕ) ∣ d then (1 : ℝ) else 1 - ((p : ℕ) : ℝ)⁻¹ ^ 2)
        = (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2)
          * (if (p : ℕ) ∣ d then (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2)⁻¹ else 1) := by
    intro p
    by_cases hpd : (p : ℕ) ∣ d
    · rw [if_pos hpd, if_pos hpd, mul_inv_cancel₀ (one_sub_inv_sq_prime_ne_zero p.2)]
    · rw [if_neg hpd, if_neg hpd, mul_one]
  have hH : Multipliable fun p : Nat.Primes =>
      if (p : ℕ) ∣ d then (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2)⁻¹ else 1 := by
    refine multipliable_of_ne_finset_one
      (s := (d.primeFactors.subtype (fun p : ℕ => Nat.Prime p) : Finset Nat.Primes)) ?_
    intro b hb
    have hnd : ¬ (b : ℕ) ∣ d := by
      intro hdiv
      exact hb (Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨b.2, hdiv, hd0⟩))
    rw [if_neg hnd]
  have hmul : (∏' p : Nat.Primes, (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2) *
        (if (p : ℕ) ∣ d then (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2)⁻¹ else 1))
      = (∏' p : Nat.Primes, (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2)) *
        ∏' p : Nat.Primes, if (p : ℕ) ∣ d then (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2)⁻¹ else 1 :=
    Multipliable.tprod_mul multipliable_one_sub_inv_sq_primes hH
  rw [show (fun p : Nat.Primes => if (p : ℕ) ∣ d then (1 : ℝ) else 1 - ((p : ℕ) : ℝ)⁻¹ ^ 2)
        = (fun p : Nat.Primes => (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2) *
            (if (p : ℕ) ∣ d then (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2)⁻¹ else 1)) from funext hFGH, hmul]
  congr 1
  rw [tprod_eq_prod (f := fun p : Nat.Primes => if (p : ℕ) ∣ d then (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2)⁻¹ else 1)
    (s := primesDvd d) ?_]
  · have hbridge : (∏ b ∈ d.primeFactors.subtype (fun p : ℕ => Nat.Prime p),
        if (b : ℕ) ∣ d then (1 - ((b : ℕ) : ℝ)⁻¹ ^ 2)⁻¹ else 1)
      = ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹ ^ 2)⁻¹ := by
      rw [Finset.prod_subtype_of_mem
        (fun p : ℕ => if p ∣ d then (1 - (p : ℝ)⁻¹ ^ 2)⁻¹ else 1)
        (fun p hp => Nat.prime_of_mem_primeFactors hp)]
      refine Finset.prod_congr rfl fun p hp => ?_
      show (if p ∣ d then (1 - (p : ℝ)⁻¹ ^ 2)⁻¹ else 1) = (1 - (p : ℝ)⁻¹ ^ 2)⁻¹
      rw [if_pos (Nat.mem_primeFactors.mp hp).2.1]
    exact hbridge
  · intro b hb
    have hnd : ¬ (b : ℕ) ∣ d := by
      intro hdiv
      exact hb (Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨b.2, hdiv, hd0⟩))
    show (if (b : ℕ) ∣ d then (1 - ((b : ℕ) : ℝ)⁻¹ ^ 2)⁻¹ else 1) = 1
    rw [if_neg hnd]

/-- Factoring `A_d(∞)` over the multiples `k = d·m`: for squarefree `d`,
`A_d(∞) = (μ(d)/d²) · ∑_{(m,d)=1} μ(m)/m²`. -/
theorem Ainf_eq_factor (d : ℕ) (hd : Squarefree d) :
    Ainf d = (μ d : ℝ) / (d : ℝ) ^ 2 * ∑' m : ℕ, moebiusCoprime d m := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have h1 : Ainf d = ∑' k : ℕ, Set.indicator {k : ℕ | d ∣ k}
      (fun k => (μ k : ℝ) / (k : ℝ) ^ 2) k := by
    show (∑' k : ℕ, if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0) = _
    refine tsum_congr fun k => ?_
    by_cases hk : d ∣ k
    · rw [Set.indicator_of_mem (show k ∈ {k : ℕ | d ∣ k} from hk), if_pos hk]
    · rw [Set.indicator_of_notMem (show k ∉ {k : ℕ | d ∣ k} from hk), if_neg hk]
  rw [h1, ← tsum_subtype]
  let e : ℕ ≃ ↥{k : ℕ | d ∣ k} :=
    { toFun := fun m => ⟨d * m, dvd_mul_right d m⟩
      invFun := fun k => (k : ℕ) / d
      left_inv := fun m => Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hd0)
      right_inv := fun k => Subtype.ext (Nat.mul_div_cancel' k.2) }
  rw [← Equiv.tsum_eq e, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  show (μ (d * m) : ℝ) / ((d * m : ℕ) : ℝ) ^ 2
      = (μ d : ℝ) / (d : ℝ) ^ 2 * moebiusCoprime d m
  by_cases hcm : m.Coprime d
  · rw [moebiusCoprime_apply, if_pos hcm, isMultiplicative_moebius.map_mul_of_coprime hcm.symm]
    push_cast
    rw [mul_pow, div_mul_div_comm]
  · rw [moebiusCoprime_apply, if_neg hcm, mul_zero]
    have hnsq : ¬ Squarefree (d * m) := by
      intro hsq
      obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd (n := d.gcd m)
        (by rw [Nat.gcd_comm]; exact hcm)
      have hpd : p ∣ d := hpdvd.trans (Nat.gcd_dvd_left d m)
      have hpm : p ∣ m := hpdvd.trans (Nat.gcd_dvd_right d m)
      have hu : IsUnit p := hsq p (mul_dvd_mul hpd hpm)
      rw [Nat.isUnit_iff] at hu
      have h2le := Nat.Prime.two_le hpp
      omega
    rw [moebius_eq_zero_of_not_squarefree hnsq]
    simp

/-- Paper eq. (10): for squarefree `d`, `A_d(∞) = μ(d)/(ζ(2) J₂(d))`.
Needs the Euler product `∑_{(m,d)=1} μ(m)/m² = ∏_{p ∤ d} (1 - p⁻²)`;
Mathlib's L-series Euler-product machinery covers multiplicative Dirichlet
series, so this is moderate but should be reachable. -/
theorem Ainf_eq (d : ℕ) (hd : Squarefree d) :
    Ainf d = (μ d : ℝ) / (zeta2 * jordan2 d) := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have hfull : (∏' p : Nat.Primes, (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2)) = zeta2⁻¹ :=
    tprod_one_sub_inv_sq_primes
  rw [Ainf_eq_factor d hd, tsum_moebiusCoprime d, tprod_split d hd0, hfull]
  simp only [jordan2, Finset.prod_inv_distrib]
  have hz2 : zeta2 ≠ 0 := by rw [zeta2_eq]; positivity
  have hP : ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹ ^ 2) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact one_sub_inv_sq_prime_ne_zero (Nat.prime_of_mem_primeFactors hp)
  have hd2 : (d : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hd0)
  field_simp

/-- `1 - p⁻² > 0` at a prime (elementary). -/
theorem one_sub_inv_sq_prime_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - (p : ℝ)⁻¹ ^ 2 := by
  have h2 := Nat.Prime.two_le hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
  have hinv : (p : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2
  have hnn : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hsq : (p : ℝ)⁻¹ ^ 2 ≤ (2⁻¹ : ℝ) ^ 2 := by gcongr
  have h4 : (2⁻¹ : ℝ) ^ 2 = 1 / 4 := by norm_num
  linarith

/-- `J₂(1) = 1`. -/
theorem jordan2_one : jordan2 1 = 1 := by
  simp [jordan2]

/-- `J₂` is multiplicative on coprime arguments. -/
theorem jordan2_mul_coprime {m n : ℕ} (hmn : m.Coprime n) :
    jordan2 (m * n) = jordan2 m * jordan2 n := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn
    subst hmn
    simp [jordan2]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn
    subst hmn
    simp [jordan2]
  rw [jordan2, jordan2, jordan2, Nat.Coprime.primeFactors_mul hmn]
  have hdisj : Disjoint m.primeFactors n.primeFactors := by
    rw [Finset.disjoint_left]
    intro p hpm hpn
    have hpp := Nat.prime_of_mem_primeFactors hpm
    have h1 : p ∣ 1 := by
      have hg := Nat.dvd_gcd (Nat.mem_primeFactors.mp hpm).2.1
        (Nat.mem_primeFactors.mp hpn).2.1
      rwa [Nat.Coprime.gcd_eq_one hmn] at hg
    exact Nat.Prime.not_dvd_one hpp h1
  rw [Finset.prod_union hdisj]
  push_cast
  ring

/-- The prime-factors product in `J₂` is positive. -/
theorem prod_primeFactors_pos (d : ℕ) :
    0 < ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹ ^ 2) := by
  refine Finset.prod_induction _ (fun x => 0 < x) (fun a b ha hb => mul_pos ha hb) one_pos
    fun p hp => one_sub_inv_sq_prime_pos (Nat.prime_of_mem_primeFactors hp)

/-- `J₂(d) ≥ d²/ζ(2)`: the partial product dominates the full Euler product. -/
theorem jordan2_ge (d : ℕ) (hd : d ≠ 0) : (d : ℝ) ^ 2 / zeta2 ≤ jordan2 d := by
  have hHm : Multipliable fun p : Nat.Primes =>
      if (p : ℕ) ∣ d then (1 : ℝ) else 1 - ((p : ℕ) : ℝ)⁻¹ ^ 2 :=
    (multipliable_congr (fun p => tsum_moebiusCoprime_prime_pow d p)).mp
      ((moebiusCoprime_isMultiplicative d).eulerProduct_hasProd
        (summable_norm_moebiusCoprime d)).multipliable
  have hT : (∏' p : Nat.Primes, if (p : ℕ) ∣ d then (1 : ℝ) else 1 - ((p : ℕ) : ℝ)⁻¹ ^ 2)
      ≤ 1 := by
    refine le_of_tendsto hHm.hasProd (Filter.Eventually.of_forall fun s => ?_)
    refine Finset.prod_le_one₀ (fun p _ => ?_) fun p _ => ?_
    · by_cases hpd : (p : ℕ) ∣ d
      · rw [if_pos hpd]
        exact zero_le_one
      · rw [if_neg hpd]
        exact le_of_lt (one_sub_inv_sq_prime_pos p.2)
    · by_cases hpd : (p : ℕ) ∣ d
      · rw [if_pos hpd]
      · rw [if_neg hpd]
        have hnn : (0 : ℝ) ≤ ((p : ℕ) : ℝ)⁻¹ ^ 2 := by positivity
        linarith
  rw [tprod_split d hd, tprod_one_sub_inv_sq_primes, Finset.prod_inv_distrib] at hT
  have hP := prod_primeFactors_pos d
  have hPz : (∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹ ^ 2)) ≠ 0 := ne_of_gt hP
  have hle : zeta2⁻¹ ≤ ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹ ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_right hT (le_of_lt hP)
    rwa [mul_assoc, inv_mul_cancel₀ hPz, mul_one, one_mul] at h1
  rw [jordan2, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)

/-- `J₂(d) ≤ d²`: every factor `1 - p⁻² ≤ 1`. -/
theorem jordan2_le (d : ℕ) : jordan2 d ≤ (d : ℝ) ^ 2 := by
  rw [jordan2]
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · have hle1 : ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹ ^ 2) ≤ 1 := by
      refine Finset.prod_le_one₀
        (fun p hp => le_of_lt (one_sub_inv_sq_prime_pos (Nat.prime_of_mem_primeFactors hp)))
        fun p hp => ?_
      have hnn : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ 2 := by positivity
      linarith
    calc (d : ℝ) ^ 2 * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹ ^ 2)
          ≤ (d : ℝ) ^ 2 * 1 := mul_le_mul_of_nonneg_left hle1 (sq_nonneg _)
      _ = (d : ℝ) ^ 2 := mul_one _

/-- The arithmetic function `d ↦ μ(d)²/J₂(d)`, whose series sums to `ζ(2)`. -/
noncomputable def moebiusSqDivJ2 : ArithmeticFunction ℝ :=
  ⟨fun d => (μ d : ℝ) ^ 2 / jordan2 d, by simp [jordan2]⟩

@[simp] theorem moebiusSqDivJ2_apply (d : ℕ) :
    moebiusSqDivJ2 d = (μ d : ℝ) ^ 2 / jordan2 d := rfl

theorem moebiusSqDivJ2_isMultiplicative : moebiusSqDivJ2.IsMultiplicative := by
  constructor
  · rw [moebiusSqDivJ2_apply]
    simp [jordan2]
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp [moebiusSqDivJ2_apply, jordan2]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [moebiusSqDivJ2_apply, jordan2]
    rw [moebiusSqDivJ2_apply, moebiusSqDivJ2_apply, moebiusSqDivJ2_apply,
      isMultiplicative_moebius.map_mul_of_coprime hmn, jordan2_mul_coprime hmn]
    push_cast
    ring

theorem summable_norm_moebiusSqDivJ2 : Summable fun d => ‖moebiusSqDivJ2 d‖ := by
  have hz2 : 0 < zeta2 := by rw [zeta2_eq]; positivity
  refine Summable.of_nonneg_of_le (fun d => norm_nonneg _) (fun d => ?_)
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left zeta2)
  rcases eq_or_ne d 0 with rfl | hd
  · simp [moebiusSqDivJ2_apply, jordan2]
  · have hJ := jordan2_ge d hd
    have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hd) 2
    have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    have hμ2 : (μ d : ℝ) ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [hμ, abs_nonneg (μ d : ℝ)]
    have hJ2 : (0 : ℝ) < (d : ℝ) ^ 2 / zeta2 := div_pos hd2 hz2
    rw [moebiusSqDivJ2_apply, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (μ d : ℝ) ^ 2),
      abs_of_nonneg (le_trans (le_of_lt hJ2) hJ)]
    calc (μ d : ℝ) ^ 2 / jordan2 d ≤ 1 / ((d : ℝ) ^ 2 / zeta2) :=
          div_le_div₀ zero_le_one hμ2 hJ2 hJ
      _ = zeta2 * (1 / (d : ℝ) ^ 2) := by rw [one_div_div, mul_one_div]

/-- The local factor of the `μ²/J₂` Euler product at a prime: `1 + 1/(p²-1) = (1 - p⁻²)⁻¹`. -/
theorem tsum_moebiusSqDivJ2_prime_pow (p : Nat.Primes) :
    ∑' e : ℕ, moebiusSqDivJ2 ((p : ℕ) ^ e) = 1 / (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2) := by
  have hvan : ∀ e : ℕ, e ∉ ({0, 1} : Finset ℕ) → moebiusSqDivJ2 ((p : ℕ) ^ e) = 0 := by
    intro e he
    have h2 : 2 ≤ e := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
      omega
    have hnsq : ¬ Squarefree ((p : ℕ) ^ e) := by
      intro hsq
      have hpdvd : (p : ℕ) * (p : ℕ) ∣ (p : ℕ) ^ e := by
        rw [← pow_two]
        exact pow_dvd_pow _ h2
      have hu : IsUnit (p : ℕ) := hsq _ hpdvd
      rw [Nat.isUnit_iff] at hu
      have h2le := Nat.Prime.two_le p.2
      omega
    rw [moebiusSqDivJ2_apply, moebius_eq_zero_of_not_squarefree hnsq]
    simp
  rw [tsum_eq_sum hvan, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  have h0 : moebiusSqDivJ2 ((p : ℕ) ^ 0) = 1 := by
    rw [pow_zero, moebiusSqDivJ2_apply]
    simp [jordan2]
  have h1 : moebiusSqDivJ2 ((p : ℕ) ^ 1) = 1 / (((p : ℕ) : ℝ) ^ 2 - 1) := by
    rw [pow_one, moebiusSqDivJ2_apply, moebius_apply_prime p.2]
    have hJ : jordan2 p = ((p : ℕ) : ℝ) ^ 2 - 1 := by
      rw [jordan2, Nat.Prime.primeFactors p.2, Finset.prod_singleton]
      have h2 := Nat.Prime.two_le p.2
      have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by
        have hpos : (0 : ℕ) < p := by omega
        exact_mod_cast hpos.ne'
      field_simp
    rw [hJ]
    norm_num
  rw [h0, h1]
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast Nat.Prime.two_le p.2
  have hx0 : ((p : ℕ) : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hp2)
  have hx1 : ((p : ℕ) : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith [hp2]
  field_simp
  ring

/-- `∑_d μ(d)²/J₂(d) = ζ(2)`: the Euler product `∏_p (1 + 1/(p²-1)) = ∏_p (1-p⁻²)⁻¹`. -/
theorem tsum_moebiusSqDivJ2 : ∑' d : ℕ, moebiusSqDivJ2 d = zeta2 := by
  have h1 : ∑' d : ℕ, moebiusSqDivJ2 d
      = ∏' p : Nat.Primes, 1 / (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2) := by
    rw [← moebiusSqDivJ2_isMultiplicative.eulerProduct_tprod summable_norm_moebiusSqDivJ2]
    exact tprod_congr fun p => tsum_moebiusSqDivJ2_prime_pow p
  have hA : Multipliable fun p : Nat.Primes => 1 / (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2) :=
    (multipliable_congr (fun p => tsum_moebiusSqDivJ2_prime_pow p)).mp
      (moebiusSqDivJ2_isMultiplicative.eulerProduct_hasProd summable_norm_moebiusSqDivJ2).multipliable
  have hmul := Multipliable.tprod_mul hA multipliable_one_sub_inv_sq_primes
  have hone : ∀ p : Nat.Primes,
      1 / (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2) * (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2) = 1 :=
    fun p => one_div_mul_cancel (one_sub_inv_sq_prime_ne_zero p.2)
  rw [tprod_congr hone] at hmul
  have h4 : (∏' p : Nat.Primes, (1 : ℝ)) = 1 := hasProd_one.tprod_eq
  rw [h4, tprod_one_sub_inv_sq_primes] at hmul
  have hA2 : (∏' p : Nat.Primes, 1 / (1 - ((p : ℕ) : ℝ)⁻¹ ^ 2)) = zeta2 := by
    have h := eq_inv_of_mul_eq_one_left hmul.symm
    rw [inv_inv] at h
    exact h
  rw [h1, hA2]

theorem zeta2_pos : 0 < zeta2 := by
  rw [zeta2_eq]
  positivity

theorem zeta2_ne_zero : zeta2 ≠ 0 := ne_of_gt zeta2_pos

/-- The Basel series: `∑' n, n⁻² = ζ(2)`. -/
theorem tsum_one_div_nat_sq : ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ = zeta2 := by
  have h := zeta_nat_eq_tsum_of_gt_one (k := 2) one_lt_two
  have hpt : ∀ n : ℕ, (1 : ℂ) / (n : ℂ) ^ 2 = ((((n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := fun n => by
    push_cast
    ring
  have h' : riemannZeta 2 = ∑' n : ℕ, 1 / (n : ℂ) ^ 2 := by exact_mod_cast h
  have h2 : (riemannZeta 2).re = ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
    rw [h', tsum_congr hpt, ← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [zeta2, ← h2]

theorem summable_one_div_nat_sq : Summable fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ :=
  ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two).congr
    (fun n => by rw [one_div])

/-- `J₂(p^k) = p^{2k} - p^{2(k-1)}` for `k ≥ 1`: the prime-power telescope step. -/
theorem jordan2_prime_pow_sub {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    jordan2 (p ^ k) = ((p ^ k : ℕ) : ℝ) ^ 2 - ((p ^ (k - 1) : ℕ) : ℝ) ^ 2 := by
  have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have h3 : (((p ^ k : ℕ) : ℝ) ^ 2) * (((p : ℕ) : ℝ)⁻¹) ^ 2 =
      ((p ^ (k - 1) : ℕ) : ℝ) ^ 2 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp only [Nat.succ_eq_add_one]
    rw [Nat.add_sub_cancel]
    have hc1 : ((p ^ (k + 1) : ℕ) : ℝ) = ((p : ℕ) : ℝ) ^ (k + 1) := by norm_cast
    have hc2 : ((p ^ k : ℕ) : ℝ) = ((p : ℕ) : ℝ) ^ k := by norm_cast
    rw [hc1, hc2, pow_succ]
    calc (((p : ℕ) : ℝ) ^ k * (p : ℕ) : ℝ) ^ 2 * ((p : ℕ) : ℝ)⁻¹ ^ 2
        = (((p : ℕ) : ℝ) ^ k) ^ 2 * (((p : ℕ) : ℝ) * ((p : ℕ) : ℝ)⁻¹) ^ 2 := by ring
      _ = (((p : ℕ) : ℝ) ^ k) ^ 2 := by rw [mul_inv_cancel₀ hp0, one_pow, mul_one]
  rw [jordan2, Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton, mul_sub, mul_one, h3]

theorem jordan2_sum_range_prime_pow {p : ℕ} (hp : p.Prime) :
    ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), jordan2 (p ^ k) = ((p ^ n : ℕ) : ℝ) ^ 2 := by
  intro n
  induction n with
  | zero => simp [jordan2_one]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih,
      jordan2_prime_pow_sub hp (by omega : n + 1 ≠ 0), Nat.add_sub_cancel]
    ring

theorem jordan2_divisors_prime_pow {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∑ d ∈ (p ^ n).divisors, jordan2 d = ((p ^ n : ℕ) : ℝ) ^ 2 := by
  rw [Nat.divisors_prime_pow hp n, Finset.sum_map]
  exact jordan2_sum_range_prime_pow hp n

/-- The Jordan identity: `∑_{d ∣ m} J₂(d) = m²`. -/
theorem jordan2_divisors_sum (m : ℕ) :
    ∑ d ∈ m.divisors, jordan2 d = (m : ℝ) ^ 2 := by
  induction m using Nat.recOnPrimePow with
  | zero => simp [Nat.divisors_zero]
  | one => simp [jordan2_one]
  | prime_pow_mul a p n hp hpa hn ih =>
    have hcop : Nat.Coprime (p ^ n) a := (hp.coprime_pow_of_not_dvd hpa).symm
    rw [Nat.divisors_mul, ← Finset.image_mul_product,
      Finset.sum_image (fun i hi j hj hij =>
        hcop.mul_injOn_divisors (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) hij),
      Finset.sum_product' (f := fun a b : ℕ => jordan2 (a * b))]
    rw [Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun y hy =>
      jordan2_mul_coprime
        ((hcop.coprime_dvd_left (Nat.mem_divisors.mp hx).1).coprime_dvd_right
          (Nat.mem_divisors.mp hy).1)))]
    rw [← Finset.sum_mul_sum, jordan2_divisors_prime_pow hp n, ih]
    push_cast
    ring

/-- Multiples subseries of the Basel series: `∑'_{q, L ∣ q} q⁻² = ζ(2)/L²`. -/
theorem tsum_dvd_indicator_inv_sq {L : ℕ} (hL : L ≠ 0) :
    ∑' q : ℕ, (if L ∣ q then ((q : ℝ) ^ 2)⁻¹ else 0) = zeta2 / (L : ℝ) ^ 2 := by
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL
  let e : ℕ ≃ ↥{q : ℕ | L ∣ q} :=
    { toFun := fun m => ⟨L * m, Nat.dvd_mul_right L m⟩
      invFun := fun q => q.1 / L
      left_inv := fun m => Nat.mul_div_cancel_left m hLpos
      right_inv := fun q => Subtype.ext (Nat.mul_div_cancel' q.2) }
  have hsub : (∑' q : ↥{q : ℕ | L ∣ q}, (((q : ℕ) : ℝ) ^ 2)⁻¹)
      = ∑' q : ℕ, (if L ∣ q then ((q : ℝ) ^ 2)⁻¹ else 0) := by
    rw [tsum_subtype {q : ℕ | L ∣ q} (fun q : ℕ => ((q : ℝ) ^ 2)⁻¹)]
    exact tsum_congr fun q => by
      by_cases hq : L ∣ q <;> simp [hq, Set.indicator]
  have hpt : ∀ m : ℕ, (((L * m : ℕ) : ℝ) ^ 2)⁻¹ =
      (L : ℝ)⁻¹ ^ 2 * (((m : ℝ) ^ 2)⁻¹) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      simp
    · push_cast
      rw [mul_pow, mul_inv, inv_pow]
  calc ∑' q : ℕ, (if L ∣ q then ((q : ℝ) ^ 2)⁻¹ else 0)
      = ∑' m : ℕ, (((L * m : ℕ) : ℝ) ^ 2)⁻¹ := by
        rw [← hsub, ← Equiv.tsum_eq e]
        exact tsum_congr fun m => rfl
    _ = ∑' m : ℕ, (L : ℝ)⁻¹ ^ 2 * (((m : ℝ) ^ 2)⁻¹) := tsum_congr hpt
    _ = (L : ℝ)⁻¹ ^ 2 * zeta2 := by rw [tsum_mul_left, tsum_one_div_nat_sq]
    _ = zeta2 / (L : ℝ) ^ 2 := by rw [div_eq_inv_mul, inv_pow]

/-- `M(q,n)` as a real sum over the cutoff interval, for `q ≠ 0`. -/
theorem M_cast (q n : ℕ) (hq : q ≠ 0) :
    (M q n : ℝ) = ∑ k ∈ Finset.Icc 1 n, if k ∣ q then (μ k : ℝ) else 0 := by
  have h1 : (M q n : ℝ) = ∑ d ∈ q.divisors.filter (· ≤ n), (μ d : ℝ) := by
    rw [M]
    push_cast
    rfl
  have hset : q.divisors.filter (· ≤ n) = (Finset.Icc 1 n).filter (· ∣ q) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hdvd, -⟩, hdn⟩
      have hd0 : d ≠ 0 := fun h => hq (by rwa [h, Nat.zero_dvd] at hdvd)
      exact ⟨⟨Nat.pos_of_ne_zero hd0, hdn⟩, hdvd⟩
    · rintro ⟨⟨-, hdn⟩, hdvd⟩
      exact ⟨⟨hdvd, hq⟩, hdn⟩
  rw [h1, hset, Finset.sum_filter]

/-- The `q⁻²`-weighted `M(q,n)²` as the double sum over `k, l ≤ n`. -/
theorem M_sq_weighted (q n : ℕ) :
    (M q n : ℝ) ^ 2 / (q : ℝ) ^ 2 =
      ∑ kl ∈ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n),
        (μ kl.1 : ℝ) * (μ kl.2 : ℝ) *
          (if kl.1 ∣ q ∧ kl.2 ∣ q then ((q : ℝ) ^ 2)⁻¹ else 0) := by
  rw [div_eq_mul_inv]
  by_cases hq : q = 0
  · subst hq
    simp [M, Nat.divisors_zero]
  rw [M_cast q n hq, pow_two, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  rw [← Finset.sum_product']
  apply Finset.sum_congr rfl
  intro kl hkl
  by_cases h1 : kl.1 ∣ q <;> by_cases h2 : kl.2 ∣ q <;> simp [h1, h2]

/-- lcm subseries evaluation: the joint-divisibility weight of a pair sums to
`ζ(2)/[k,l]²`. -/
theorem tsum_pair_indicator_inv_sq {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) :
    ∑' q : ℕ, (if k ∣ q ∧ l ∣ q then ((q : ℝ) ^ 2)⁻¹ else 0)
      = zeta2 / ((Nat.lcm k l : ℕ) : ℝ) ^ 2 := by
  have hconv : (fun q : ℕ => if k ∣ q ∧ l ∣ q then ((q : ℝ) ^ 2)⁻¹ else 0)
      = fun q : ℕ => if Nat.lcm k l ∣ q then ((q : ℝ) ^ 2)⁻¹ else 0 :=
    funext fun q => if_congr Nat.lcm_dvd_iff.symm rfl rfl
  rw [hconv]
  exact tsum_dvd_indicator_inv_sq (fun h => by
    rw [Nat.lcm_eq_zero_iff] at h
    rcases h with h | h <;> contradiction)

/-- The Gram identity, first form: `1 + S(n) = ζ(2) ∑_{k,l ≤ n} μ(k)μ(l)/[k,l]²`. -/
theorem gram_eq (n : ℕ) (hn : 1 ≤ n) :
    1 + S n = zeta2 * ∑ kl ∈ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n),
      (μ kl.1 : ℝ) * (μ kl.2 : ℝ) * (((Nat.lcm kl.1 kl.2 : ℕ) : ℝ) ^ 2)⁻¹ := by
  rw [← parseval_eq_one_add_S n hn]
  have hsumm : ∀ kl ∈ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n),
      Summable fun q : ℕ => (μ kl.1 : ℝ) * (μ kl.2 : ℝ) *
        (if kl.1 ∣ q ∧ kl.2 ∣ q then ((q : ℝ) ^ 2)⁻¹ else 0) := by
    intro kl hkl
    refine Summable.mul_left _ ((summable_one_div_nat_sq.indicator
      {q : ℕ | kl.1 ∣ q ∧ kl.2 ∣ q}).congr fun q => ?_)
    by_cases hq : kl.1 ∣ q ∧ kl.2 ∣ q <;> simp [Set.indicator, hq]
  rw [tsum_congr (fun q => M_sq_weighted q n), Summable.tsum_finsetSum hsumm,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro kl hkl
  have hk : kl.1 ≠ 0 := by
    have := (Finset.mem_product.mp hkl).1
    simp only [Finset.mem_Icc] at this
    omega
  have hl : kl.2 ≠ 0 := by
    have := (Finset.mem_product.mp hkl).2
    simp only [Finset.mem_Icc] at this
    omega
  rw [tsum_mul_left, tsum_pair_indicator_inv_sq hk hl, div_eq_inv_mul]
  ring

/-- `1/lcm(k,l)² = gcd(k,l)²/(kl)²` for nonzero `k, l`. -/
theorem inv_lcm_sq {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) :
    (((Nat.lcm k l : ℕ) : ℝ) ^ 2)⁻¹ =
      ((Nat.gcd k l : ℕ) : ℝ) ^ 2 / ((k : ℝ) * (l : ℝ)) ^ 2 := by
  have hg0 : (Nat.gcd k l : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast Nat.gcd_pos_of_pos_left l (Nat.pos_of_ne_zero hk))
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  have hkl : (Nat.gcd k l : ℝ) * (Nat.lcm k l : ℝ) = (k : ℝ) * (l : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm k l
  have hlcm : (Nat.lcm k l : ℝ) = (k : ℝ) * (l : ℝ) / (Nat.gcd k l : ℝ) := by
    rw [eq_div_iff hg0, mul_comm]
    exact hkl
  rw [hlcm]
  field_simp [hg0, hk0, hl0]
  try ring

/-- The Gram identity in Jordan form: the pair sum rearranges to
`∑_{d ≤ n} J₂(d) A_d(n)²`. -/
theorem gram_jordan (n : ℕ) :
    zeta2 * ∑ kl ∈ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n),
        (μ kl.1 : ℝ) * (μ kl.2 : ℝ) * (((Nat.lcm kl.1 kl.2 : ℕ) : ℝ) ^ 2)⁻¹
      = zeta2 * ∑ d ∈ Finset.Icc 1 n, jordan2 d * (A d n) ^ 2 := by
  have step1 : ∀ kl ∈ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n),
      (μ kl.1 : ℝ) * (μ kl.2 : ℝ) * (((Nat.lcm kl.1 kl.2 : ℕ) : ℝ) ^ 2)⁻¹
        = ∑ d ∈ Finset.Icc 1 n,
            (if d ∣ Nat.gcd kl.1 kl.2 then
              (μ kl.1 : ℝ) * (μ kl.2 : ℝ) / ((kl.1 : ℝ) ^ 2 * (kl.2 : ℝ) ^ 2) * jordan2 d
            else 0) := by
    intro kl hkl
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hkl
    obtain ⟨⟨hk1, hkn⟩, ⟨hl1, hln⟩⟩ := hkl
    have hk : kl.1 ≠ 0 := by omega
    have hl : kl.2 ≠ 0 := by omega
    have hg : Nat.gcd kl.1 kl.2 ≠ 0 := fun h => hk (Nat.gcd_eq_zero_iff.mp h).1
    have hgpos : 0 < Nat.gcd kl.1 kl.2 := Nat.pos_of_ne_zero hg
    have hset : (Finset.Icc 1 n).filter (· ∣ Nat.gcd kl.1 kl.2)
        = (Nat.gcd kl.1 kl.2).divisors := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd1, hdn⟩, hdvd⟩
        exact ⟨hdvd, hg⟩
      · rintro ⟨hdvd, -⟩
        have hd0 : d ≠ 0 := fun h => hg (by rwa [h, Nat.zero_dvd] at hdvd)
        have hdle : d ≤ n := (Nat.le_of_dvd hgpos hdvd).trans
          ((Nat.le_of_dvd hk1 (Nat.gcd_dvd_left kl.1 kl.2)).trans hkn)
        exact ⟨⟨Nat.pos_of_ne_zero hd0, hdle⟩, hdvd⟩
    rw [← Finset.sum_filter, hset, ← Finset.mul_sum, jordan2_divisors_sum,
      inv_lcm_sq hk hl, mul_pow]
    ring
  have step2 : ∀ d ∈ Finset.Icc 1 n,
      ∑ kl ∈ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n),
        (if d ∣ Nat.gcd kl.1 kl.2 then
          (μ kl.1 : ℝ) * (μ kl.2 : ℝ) / ((kl.1 : ℝ) ^ 2 * (kl.2 : ℝ) ^ 2) * jordan2 d
        else 0)
      = jordan2 d * (A d n) ^ 2 := by
    intro d hd
    have hpt : ∀ kl : ℕ × ℕ,
        (if d ∣ Nat.gcd kl.1 kl.2 then
          (μ kl.1 : ℝ) * (μ kl.2 : ℝ) / ((kl.1 : ℝ) ^ 2 * (kl.2 : ℝ) ^ 2) * jordan2 d
        else 0)
        = jordan2 d *
          (if d ∣ kl.1 ∧ d ∣ kl.2 then
            (μ kl.1 : ℝ) * (μ kl.2 : ℝ) / ((kl.1 : ℝ) ^ 2 * (kl.2 : ℝ) ^ 2)
          else 0) := by
      intro kl
      by_cases h1 : d ∣ kl.1 ∧ d ∣ kl.2
      · rw [if_pos (Nat.dvd_gcd_iff.mpr h1), if_pos h1, mul_comm]
      · rw [if_neg (fun h => h1 (Nat.dvd_gcd_iff.mp h)), if_neg h1, mul_zero]
    rw [Finset.sum_congr rfl (fun kl _ => hpt kl), ← Finset.mul_sum]
    congr 1
    have hfactor : ∀ k l : ℕ,
        (if d ∣ k ∧ d ∣ l then
          (μ k : ℝ) * (μ l : ℝ) / ((k : ℝ) ^ 2 * (l : ℝ) ^ 2) else 0)
        = (if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0) *
          (if d ∣ l then (μ l : ℝ) / (l : ℝ) ^ 2 else 0) := by
      intro k l
      by_cases h1 : d ∣ k <;> by_cases h2 : d ∣ l
      · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, div_mul_div_comm]
      · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg h2, mul_zero]
      · rw [if_neg (fun h => h1 h.1), if_neg h1, if_pos h2, zero_mul]
      · rw [if_neg (fun h => h1 h.1), if_neg h1, if_neg h2, zero_mul]
    rw [Finset.sum_product'
      (f := fun k l => if d ∣ k ∧ d ∣ l then
        (μ k : ℝ) * (μ l : ℝ) / ((k : ℝ) ^ 2 * (l : ℝ) ^ 2) else 0),
      Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => hfactor k l)),
      ← Finset.sum_mul_sum, ← pow_two]
    rfl
  congr 1
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  exact Finset.sum_congr rfl step2

/-- **Gram identity (paper eq. (8))**: `1 + S(n) = ζ(2) ∑_{d ≤ n} J₂(d) A_d(n)²`. -/
theorem gram_identity (n : ℕ) (hn : 1 ≤ n) :
    1 + S n = zeta2 * ∑ d ∈ Finset.Icc 1 n, jordan2 d * (A d n) ^ 2 :=
  (gram_eq n hn).trans (gram_jordan n)

/-- `J₂(d) ≥ 0` for all `d`. -/
theorem jordan2_nonneg (d : ℕ) : 0 ≤ jordan2 d :=
  mul_nonneg (sq_nonneg _) (le_of_lt (prod_primeFactors_pos d))

/-- `J₂(d) > 0` for `d ≠ 0`. -/
theorem jordan2_pos {d : ℕ} (hd : d ≠ 0) : 0 < jordan2 d :=
  mul_pos (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hd) 2) (prod_primeFactors_pos d)

/-- `A_d(∞) = 0` when `d` is not squarefree: every multiple of `d` has `μ = 0`. -/
theorem Ainf_eq_zero_of_not_squarefree {d : ℕ} (hd : ¬Squarefree d) : Ainf d = 0 := by
  rw [Ainf]
  have h : ∀ k : ℕ, (if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0) = 0 := by
    intro k
    by_cases hdk : d ∣ k
    · have hsk : ¬Squarefree k := fun hsk => hd (hsk.squarefree_of_dvd hdk)
      have hμ : (μ k : ℝ) = 0 := by
        exact_mod_cast moebius_eq_zero_of_not_squarefree hsk
      simp [hdk, hμ]
    · simp [hdk]
  rw [tsum_congr h]
  exact tsum_zero

/-- `J₂(d)·A_d(∞)² = ζ(2)⁻²·μ(d)²/J₂(d)` for all `d`. -/
theorem jordan2Ainf_sq (d : ℕ) :
    jordan2 d * (Ainf d) ^ 2 = zeta2⁻¹ ^ 2 * ((μ d : ℝ) ^ 2 / jordan2 d) := by
  by_cases hd : Squarefree d
  · have hd0 : d ≠ 0 := hd.ne_zero
    have hJ : jordan2 d ≠ 0 := ne_of_gt (jordan2_pos hd0)
    rw [Ainf_eq d hd]
    field_simp [hJ, zeta2_ne_zero]
    try ring
  · rw [Ainf_eq_zero_of_not_squarefree hd]
    have hμ : (μ d : ℝ) = 0 := by
      have h0 := moebius_eq_zero_of_not_squarefree hd
      exact_mod_cast h0
    simp [hμ]

/-- The total `ζ(2)∑_{d ≥ 1} J₂(d)A_d(∞)² = 1` (paper eq. (9)). -/
theorem total_one : zeta2 * ∑' d : ℕ, jordan2 d * (Ainf d) ^ 2 = 1 := by
  rw [tsum_congr (fun d => jordan2Ainf_sq d), tsum_mul_left,
    show (∑' d : ℕ, (μ d : ℝ) ^ 2 / jordan2 d) = zeta2 from by
      rw [← tsum_moebiusSqDivJ2]
      exact tsum_congr fun d => (moebiusSqDivJ2_apply d).symm,
    inv_pow]
  calc zeta2 * ((zeta2 ^ 2)⁻¹ * zeta2) = zeta2 ^ 2 * (zeta2 ^ 2)⁻¹ := by ring
    _ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 zeta2_ne_zero)

/-- `μ(d)·A_d(∞) = ζ(2)⁻¹·μ(d)²/J₂(d)` for all `d`. -/
theorem mu_Ainf_eq (d : ℕ) :
    (μ d : ℝ) * Ainf d = zeta2⁻¹ * ((μ d : ℝ) ^ 2 / jordan2 d) := by
  by_cases hd : Squarefree d
  · have hd0 : d ≠ 0 := hd.ne_zero
    have hJ : jordan2 d ≠ 0 := ne_of_gt (jordan2_pos hd0)
    have e : zeta2⁻¹ * ((μ d : ℝ) ^ 2 / jordan2 d)
        = (μ d : ℝ) ^ 2 / (zeta2 * jordan2 d) := by
      field_simp [hJ, zeta2_ne_zero]
      try ring
    rw [Ainf_eq d hd, e]
    ring
  · rw [Ainf_eq_zero_of_not_squarefree hd]
    have hμ : (μ d : ℝ) = 0 := by
      have h0 := moebius_eq_zero_of_not_squarefree hd
      exact_mod_cast h0
    simp [hμ]

/-- The signed total `∑_{d ≥ 1} μ(d)A_d(∞) = 1`. -/
theorem total_muAinf : ∑' d : ℕ, (μ d : ℝ) * Ainf d = 1 := by
  rw [tsum_congr (fun d => mu_Ainf_eq d), tsum_mul_left,
    show (∑' d : ℕ, (μ d : ℝ) ^ 2 / jordan2 d) = zeta2 from by
      rw [← tsum_moebiusSqDivJ2]
      exact tsum_congr fun d => (moebiusSqDivJ2_apply d).symm,
    inv_mul_cancel₀ zeta2_ne_zero]

theorem summable_mu_sq_div_jordan2 : Summable fun d : ℕ => (μ d : ℝ) ^ 2 / jordan2 d := by
  apply Summable.of_norm
  refine summable_norm_moebiusSqDivJ2.congr fun d => ?_
  simp only [Real.norm_eq_abs, moebiusSqDivJ2_apply]

theorem summable_muAinf : Summable fun d : ℕ => (μ d : ℝ) * Ainf d :=
  (summable_mu_sq_div_jordan2.mul_left zeta2⁻¹).congr fun d => (mu_Ainf_eq d).symm

/-- Splitting a real series over `ℕ` at the cutoff: total = `Icc 1 n` part + strict tail. -/
theorem tsum_split_Icc_tail {g : ℕ → ℝ} (hg : Summable g) (hg0 : g 0 = 0) (n : ℕ) :
    ∑' d : ℕ, g d = ∑ d ∈ Finset.Icc 1 n, g d + ∑' d : ℕ, (if n < d then g d else 0) := by
  have htail : (∑' d : ℕ, (if n < d then g d else 0)) = ∑' i : ℕ, g (i + (n + 1)) := by
    let e : ℕ ≃ ↥{d : ℕ | n < d} :=
      { toFun := fun i => ⟨i + (n + 1), by simp only [Set.mem_setOf_eq]; omega⟩
        invFun := fun d => d.1 - (n + 1)
        left_inv := fun i => by simp
        right_inv := fun d => by
          ext
          show d.1 - (n + 1) + (n + 1) = d.1
          have hd : n < d.1 := d.2
          omega }
    have hsub : (∑' d : ↥{d : ℕ | n < d}, g d.1)
        = ∑' d : ℕ, (if n < d then g d else 0) := by
      rw [tsum_subtype {d : ℕ | n < d} g]
      exact tsum_congr fun d => by by_cases hd : n < d <;> simp [Set.indicator, hd]
    rw [← hsub, ← Equiv.tsum_eq e]
    exact tsum_congr fun i => rfl
  have hsplit := (hg.sum_add_tsum_nat_add (n + 1)).symm
  have hfront : ∑ d ∈ Finset.range (n + 1), g d = ∑ d ∈ Finset.Icc 1 n, g d := by
    have hset : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext d
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert (by simp), hg0, zero_add]
  rw [hsplit, hfront, ← htail]

/-- The tail of the signed total separates (paper eq. (11)). -/
theorem tail_muAinf (n : ℕ) :
    ∑' d : ℕ, (if n < d then (μ d : ℝ) * Ainf d else 0)
      = zeta2⁻¹ * ∑' d : ℕ, (if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0) := by
  have h : ∀ d : ℕ, (if n < d then (μ d : ℝ) * Ainf d else 0)
      = zeta2⁻¹ * (if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0) := by
    intro d
    by_cases hd : n < d
    · rw [if_pos hd, if_pos hd, mu_Ainf_eq d]
    · rw [if_neg hd, if_neg hd, mul_zero]
  rw [tsum_congr h]
  exact tsum_mul_left

/-- `∑_{d ∣ k} μ(d) = δ_{k,1}` over `ℤ`. -/
theorem sum_divisors_moebius_int (k : ℕ) :
    ∑ d ∈ k.divisors, μ d = if k = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply, moebius_mul_coe_zeta,
    ArithmeticFunction.one_apply]

/-- `∑_{d ∣ k} μ(d) = δ_{k,1}` over `ℝ`. -/
theorem sum_divisors_moebius_real (k : ℕ) :
    ∑ d ∈ k.divisors, (μ d : ℝ) = if k = 1 then 1 else 0 := by
  have h := sum_divisors_moebius_int k
  by_cases hk : k = 1
  · subst hk
    simp [Nat.divisors_one, moebius_apply_one]
  · rw [if_neg hk] at h
    have h3 : ((∑ d ∈ k.divisors, μ d : ℤ) : ℝ) = 0 := by exact_mod_cast h
    rw [Int.cast_sum] at h3
    rw [if_neg hk]
    exact h3

/-- The partial signed sum collapses: `∑_{d ≤ n} μ(d)A_d(n) = 1`. -/
theorem sum_mu_A (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (μ d : ℝ) * A d n = 1 := by
  have step : ∑ d ∈ Finset.Icc 1 n, (μ d : ℝ) * A d n
      = ∑ k ∈ Finset.Icc 1 n, (μ k : ℝ) / (k : ℝ) ^ 2 *
          (∑ d ∈ Finset.Icc 1 n, if d ∣ k then (μ d : ℝ) else 0) := by
    rw [Finset.sum_congr rfl (fun d _ => by rw [A, Finset.mul_sum])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h : d ∣ k
    · rw [if_pos h, if_pos h, mul_comm]
    · rw [if_neg h, if_neg h, mul_zero, mul_zero]
  rw [step, Finset.sum_congr rfl (fun k hk => by
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
    have hset : (Finset.Icc 1 n).filter (· ∣ k) = k.divisors := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd1, -⟩, hdvd⟩
        exact ⟨hdvd, by omega⟩
      · rintro ⟨hdvd, hk0⟩
        have hd0 : d ≠ 0 := fun h0 => hk0 (by rwa [h0, Nat.zero_dvd] at hdvd)
        exact ⟨⟨Nat.pos_of_ne_zero hd0,
          (Nat.le_of_dvd (by omega) hdvd).trans hkn⟩, hdvd⟩
    show (μ k : ℝ) / (k : ℝ) ^ 2 * (∑ d ∈ Finset.Icc 1 n, if d ∣ k then (μ d : ℝ) else 0)
      = (μ k : ℝ) / (k : ℝ) ^ 2 * (if k = 1 then 1 else 0)
    rw [← Finset.sum_filter, hset, sum_divisors_moebius_real k]),
    Finset.sum_congr rfl (fun k _ => by
      show (μ k : ℝ) / (k : ℝ) ^ 2 * (if k = 1 then 1 else 0)
        = if k = 1 then (μ k : ℝ) / (k : ℝ) ^ 2 else 0
      by_cases hk1 : k = 1
      · rw [if_pos hk1, if_pos hk1, mul_one]
      · rw [if_neg hk1, if_neg hk1, mul_zero]),
    Finset.sum_ite_eq' (Finset.Icc 1 n) 1 (fun k => (μ k : ℝ) / (k : ℝ) ^ 2)]
  simp [Finset.mem_Icc, hn, moebius_apply_one]

/-- **Signed-sum evaluation (paper eqs. (10)-(12))**:
`2∑_{d ≤ n} μ(d)E_d(n) = (2/ζ(2))∑_{d > n} μ(d)²/J₂(d)`. -/
theorem signed_sum (n : ℕ) (hn : 1 ≤ n) :
    2 * ∑ d ∈ Finset.Icc 1 n, (μ d : ℝ) * E d n
      = 2 * zeta2⁻¹ * ∑' d : ℕ, (if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0) := by
  have hA0 : Ainf 0 = 0 := by
    rw [Ainf]
    have h : ∀ k : ℕ, (if 0 ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0) = 0 := by
      intro k
      by_cases hk : k = 0
      · subst hk
        norm_num
      · rw [if_neg (fun h0 => hk (Nat.zero_dvd.mp h0))]
    rw [tsum_congr h]
    exact tsum_zero
  have hsplit := tsum_split_Icc_tail summable_muAinf (by rw [hA0, mul_zero]) n
  have htot : ∑ d ∈ Finset.Icc 1 n, (μ d : ℝ) * Ainf d +
      ∑' d : ℕ, (if n < d then (μ d : ℝ) * Ainf d else 0) = 1 := by
    rw [← hsplit]
    exact total_muAinf
  rw [tail_muAinf n] at htot
  have hIcc : ∑ d ∈ Finset.Icc 1 n, (μ d : ℝ) * Ainf d
      = 1 - zeta2⁻¹ * ∑' d : ℕ, (if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0) := by
    linarith [htot]
  have hE : ∀ d, (μ d : ℝ) * E d n = (μ d : ℝ) * A d n - (μ d : ℝ) * Ainf d :=
    fun d => by rw [E]; ring
  rw [Finset.sum_congr rfl (fun d _ => hE d), Finset.sum_sub_distrib, sum_mu_A n hn,
    hIcc]
  ring


/-- Telescope tail bound: `∑_{d > m} d⁻² ≤ 1/m` for `m ≥ 1`. -/
theorem tsum_one_div_sq_tail_telescope (m : ℕ) (hm : 1 ≤ m) :
    ∑' d : ℕ, (if m < d then ((d : ℝ) ^ 2)⁻¹ else 0) ≤ 1 / (m : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hs : Summable fun d : ℕ => if m < d then ((d : ℝ) ^ 2)⁻¹ else 0 :=
    (summable_one_div_nat_sq.indicator {d : ℕ | m < d}).congr fun d => by
      by_cases h : m < d <;> simp [Set.indicator, h]
  have key : ∀ d : ℕ, m < d → ((d : ℝ) ^ 2)⁻¹ ≤ 1 / ((d : ℝ) - 1) - 1 / (d : ℝ) := by
    intro d hd
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 2 ≤ d)
    have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
    have e : 1 / ((d : ℝ) - 1) - 1 / (d : ℝ) = 1 / (((d : ℝ) - 1) * (d : ℝ)) := by
      field_simp [ne_of_gt hd1, ne_of_gt hd0]
      try ring
    rw [e, sq, ← one_div]
    exact one_div_le_one_div_of_le (mul_pos hd1 hd0) (by nlinarith [hd0])
  have hpartial : ∀ N : ℕ, ∑ d ∈ Finset.range N, (if m < d then ((d : ℝ) ^ 2)⁻¹ else 0)
      ≤ 1 / (m : ℝ) := by
    intro N
    by_cases hN : N ≤ m + 1
    · have hz : ∑ d ∈ Finset.range N, (if m < d then ((d : ℝ) ^ 2)⁻¹ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        rw [Finset.mem_range] at hd
        rw [if_neg (by omega : ¬ m < d)]
      rw [hz]
      exact le_of_lt (one_div_pos.mpr hm0)
    · have hN' : m + 1 ≤ N := by omega
      have h1 : ∑ d ∈ Finset.range N, (if m < d then ((d : ℝ) ^ 2)⁻¹ else 0)
          ≤ ∑ d ∈ Finset.range N, (if m < d then (1 / ((d : ℝ) - 1) - 1 / (d : ℝ)) else 0) :=
        Finset.sum_le_sum fun d _ => by
          by_cases hmd : m < d
          · rw [if_pos hmd, if_pos hmd]
            exact key d hmd
          · rw [if_neg hmd, if_neg hmd]
      have hIco : ∑ d ∈ Finset.range N, (if m < d then (1 / ((d : ℝ) - 1) - 1 / (d : ℝ)) else 0)
          = ∑ d ∈ Finset.Ico (m + 1) N, (1 / ((d : ℝ) - 1) - 1 / (d : ℝ)) := by
        have hsub : Finset.Ico (m + 1) N ⊆ Finset.range N := by
          intro x hx
          rw [Finset.mem_Ico] at hx
          rw [Finset.mem_range]
          omega
        have hzero : ∀ x ∈ Finset.range N, x ∉ Finset.Ico (m + 1) N →
            (if m < x then (1 / ((x : ℝ) - 1) - 1 / (x : ℝ)) else 0) = 0 := by
          intro x hx1 hx2
          rw [Finset.mem_range] at hx1
          have hx3 : x < m + 1 := by
            by_contra hc
            apply hx2
            rw [Finset.mem_Ico]
            exact ⟨by omega, hx1⟩
          rw [if_neg (by omega : ¬ m < x)]
        rw [← Finset.sum_subset hsub hzero]
        exact Finset.sum_congr rfl fun d hd => by
          rw [Finset.mem_Ico] at hd
          rw [if_pos (by omega : m < d)]
      have h2 : ∑ d ∈ Finset.range N, (if m < d then (1 / ((d : ℝ) - 1) - 1 / (d : ℝ)) else 0)
          = 1 / (m : ℝ) - 1 / ((N - 1 : ℕ) : ℝ) := by
        rw [hIco, Finset.sum_Ico_eq_sum_range]
        rw [Finset.sum_congr rfl (fun i _ => show
          (1 / (((m + 1 + i : ℕ) : ℝ) - 1) - 1 / ((m + 1 + i : ℕ) : ℝ))
            = (fun j : ℕ => 1 / (((m + j : ℕ)) : ℝ)) i
              - (fun j : ℕ => 1 / (((m + j : ℕ)) : ℝ)) (i + 1) from by
          have e1 : (((m + 1 + i : ℕ) : ℝ)) - 1 = ((m + i : ℕ) : ℝ) := by push_cast; ring
          have e2 : ((m + 1 + i : ℕ) : ℝ) = ((m + i + 1 : ℕ) : ℝ) := by push_cast; ring
          rw [e1, e2]
          rfl)]
        rw [Finset.sum_range_sub' (fun j : ℕ => 1 / (((m + j : ℕ)) : ℝ)) (N - (m + 1))]
        rw [Nat.add_zero, show m + (N - (m + 1)) = N - 1 from by omega]
      have h3 : 1 / (m : ℝ) - 1 / ((N - 1 : ℕ) : ℝ) ≤ 1 / (m : ℝ) := by
        have hN1 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - 1)
        exact sub_le_self _ (le_of_lt (one_div_pos.mpr hN1))
      exact (h1.trans (le_of_eq h2)).trans h3
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat (Filter.Eventually.of_forall hpartial)

/-- Strict tail bound: `∑_{d > n} d⁻² < 1/n` for `n ≥ 1`. -/
theorem tsum_one_div_sq_tail_strict (n : ℕ) (hn : 1 ≤ n) :
    ∑' d : ℕ, (if n < d then ((d : ℝ) ^ 2)⁻¹ else 0) < 1 / (n : ℝ) := by
  have hG0 : ((fun d : ℕ => ((d : ℝ) ^ 2)⁻¹) 0) = 0 := by simp
  have hGs : Summable fun d : ℕ => ((d : ℝ) ^ 2)⁻¹ := summable_one_div_nat_sq
  have split_n := tsum_split_Icc_tail hGs hG0 n
  have split_n1 := tsum_split_Icc_tail hGs hG0 (n + 1)
  have hsucc : ∑ d ∈ Finset.Icc 1 (n + 1), ((d : ℝ) ^ 2)⁻¹
      = ∑ d ∈ Finset.Icc 1 n, ((d : ℝ) ^ 2)⁻¹ + (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
    Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1) (fun d : ℕ => ((d : ℝ) ^ 2)⁻¹)
  have htail : ∑' d : ℕ, (if n < d then ((d : ℝ) ^ 2)⁻¹ else 0)
      = (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ + ∑' d : ℕ, (if n + 1 < d then ((d : ℝ) ^ 2)⁻¹ else 0) := by
    linarith [split_n, split_n1, hsucc]
  have hT := tsum_one_div_sq_tail_telescope (n + 1) (by omega)
  rw [htail]
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have key : (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ + 1 / ((n + 1 : ℕ) : ℝ) < 1 / (n : ℝ) := by
    have e : (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ + 1 / ((n + 1 : ℕ) : ℝ)
        = (((n + 1 : ℕ) : ℝ) + 1) / (((n + 1 : ℕ) : ℝ) ^ 2) := by
      field_simp [ne_of_gt hn1]
      try ring
    rw [e, div_lt_div_iff₀ (sq_pos_of_pos hn1) hn']
    have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hc]
    nlinarith [sq_nonneg ((n : ℝ))]
  have hT' : ∑' d : ℕ, (if n + 1 < d then ((d : ℝ) ^ 2)⁻¹ else 0)
      ≤ 1 / ((n + 1 : ℕ) : ℝ) := hT
  linarith [hT', key]

/-- `E_d(n)` is exactly the negative of the series tail above `n`. -/
theorem E_tail (d n : ℕ) :
    E d n = -(∑' k : ℕ, if n < k then (if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0) else 0) := by
  have hg0' : Summable fun k : ℕ => (μ k : ℝ) / (k : ℝ) ^ 2 :=
    Summable.of_norm (summable_norm_moebiusDivSq.congr fun k => by rw [moebiusDivSq_apply])
  have hg : Summable fun k : ℕ => if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0 :=
    (hg0'.indicator {k : ℕ | d ∣ k}).congr fun k => by
      by_cases h : d ∣ k <;> simp [Set.indicator, h]
  have hg0 : (fun k : ℕ => if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0) 0 = 0 := by
    by_cases h : d ∣ 0 <;> simp [h]
  have split := tsum_split_Icc_tail hg hg0 n
  rw [E]
  show (∑ k ∈ Finset.Icc 1 n, if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0)
    - (∑' k : ℕ, if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0)
    = -(∑' k : ℕ, if n < k then (if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0) else 0)
  linarith [split]

/-- **Error bound (paper, used in eq. (6))**: `|E_d(n)| ≤ 2/(dn)` for `1 ≤ d ≤ n`. -/
theorem E_abs_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hdn : d ≤ n) :
    |E d n| ≤ 2 / ((d : ℝ) * (n : ℝ)) := by
  have hg0' : Summable fun k : ℕ => (μ k : ℝ) / (k : ℝ) ^ 2 :=
    Summable.of_norm (summable_norm_moebiusDivSq.congr fun k => by rw [moebiusDivSq_apply])
  have hgT : Summable fun k : ℕ =>
      if n < k then (if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0) else 0 :=
    ((hg0'.indicator {k : ℕ | d ∣ k}).indicator {k : ℕ | n < k}).congr fun k => by
      by_cases h1 : n < k <;> by_cases h2 : d ∣ k <;> simp [Set.indicator, h1, h2]
  have hsum_norm : Summable fun k : ℕ =>
      ‖if n < k then (if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0) else 0‖ := hgT.abs
  have step2 : ∀ k : ℕ,
      ‖if n < k then (if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0) else 0‖
      ≤ if n < k then (if d ∣ k then ((k : ℝ) ^ 2)⁻¹ else 0) else 0 := by
    intro k
    by_cases hnk : n < k
    · rw [if_pos hnk, if_pos hnk]
      by_cases hdk : d ∣ k
      · rw [if_pos hdk, if_pos hdk]
        have hk0 : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos (by exact_mod_cast (by omega : 0 < k)) 2
        have hμ : |(μ k : ℝ)| ≤ 1 := by
          have h2 : |(μ k : ℤ)| ≤ 1 := by
            rw [ArithmeticFunction.abs_moebius]
            split_ifs <;> norm_num
          calc |(μ k : ℝ)| = ((|(μ k : ℤ)| : ℤ) : ℝ) := by rw [Int.cast_abs]
            _ ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h2
            _ = 1 := by norm_num
        rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg ((k : ℝ))),
          show ((k : ℝ) ^ 2)⁻¹ = 1 / (k : ℝ) ^ 2 from (one_div _).symm]
        exact (div_le_div_iff_of_pos_right hk0).mpr hμ
      · rw [if_neg hdk, if_neg hdk]
        simp
    · rw [if_neg hnk, if_neg hnk]
      simp
  have hdom : Summable fun k : ℕ =>
      if n < k then (if d ∣ k then ((k : ℝ) ^ 2)⁻¹ else 0) else 0 :=
    ((summable_one_div_nat_sq.indicator {k : ℕ | d ∣ k}).indicator {k : ℕ | n < k}).congr
      fun k => by by_cases h1 : n < k <;> by_cases h2 : d ∣ k <;> simp [Set.indicator, h1, h2]
  have hinj : Function.Injective (fun m : ℕ => d * m) := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h
  have hsupp : Function.support (fun k : ℕ =>
        if n < k then (if d ∣ k then ((k : ℝ) ^ 2)⁻¹ else 0) else 0)
      ⊆ Set.range (fun m : ℕ => d * m) := by
    intro k hk
    rw [Function.mem_support] at hk
    have hdk : d ∣ k := by
      by_contra hnd
      apply hk
      by_cases hnk : n < k
      · rw [if_pos hnk, if_neg hnd]
      · rw [if_neg hnk]
    exact ⟨k / d, Nat.mul_div_cancel' hdk⟩
  have step4 : (∑' k : ℕ, if n < k then (if d ∣ k then ((k : ℝ) ^ 2)⁻¹ else 0) else 0)
      = ∑' m : ℕ, (if n < d * m then
          (if d ∣ d * m then (((d * m : ℕ) : ℝ) ^ 2)⁻¹ else 0) else 0) :=
    (Function.Injective.tsum_eq hinj hsupp).symm
  have step4' : ∀ m : ℕ, (if n < d * m then
        (if d ∣ d * m then (((d * m : ℕ) : ℝ) ^ 2)⁻¹ else 0) else 0)
      = if n < d * m then (((d * m : ℕ) : ℝ) ^ 2)⁻¹ else 0 := by
    intro m
    by_cases hnm : n < d * m
    · rw [if_pos hnm, if_pos hnm, if_pos (Nat.dvd_mul_right d m)]
    · rw [if_neg hnm, if_neg hnm]
  have step5 : ∀ m : ℕ, (if n < d * m then (((d * m : ℕ) : ℝ) ^ 2)⁻¹ else 0)
      = ((d : ℝ) ^ 2)⁻¹ * (if (n / d : ℕ) < m then ((m : ℝ) ^ 2)⁻¹ else 0) := by
    intro m
    have hcond : ((n / d : ℕ) < m) ↔ (n < d * m) := by
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < d), mul_comm]
    by_cases hm : (n / d : ℕ) < m
    · have hnm : n < d * m := hcond.mp hm
      rw [if_pos hnm, if_pos hm, Nat.cast_mul, mul_pow, mul_inv]
    · have hnm : ¬ n < d * m := fun h => hm (hcond.mpr h)
      rw [if_neg hnm, if_neg hm, mul_zero]
  have hnd1 : 1 ≤ n / d := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr (by omega)
  have hT2 := tsum_one_div_sq_tail_telescope (n / d) hnd1
  have hfin : ((d : ℝ) ^ 2)⁻¹ * (1 / ((n / d : ℕ) : ℝ)) ≤ 2 / ((d : ℝ) * (n : ℝ)) := by
    have key : (n : ℝ) ≤ 2 * (d : ℝ) * ((n / d : ℕ) : ℝ) := by
      have h2 : n < d * (n / d) + d := by
        have hmod := Nat.mod_lt n (by omega : 0 < d)
        have hdvm := Nat.div_add_mod n d
        omega
      have h3 : d ≤ d * (n / d) :=
        calc d = d * 1 := (mul_one d).symm
          _ ≤ d * (n / d) := Nat.mul_le_mul_left d hnd1
      have h4 : n ≤ 2 * (d * (n / d)) := by omega
      calc (n : ℝ) ≤ ((2 * (d * (n / d)) : ℕ) : ℝ) := by exact_mod_cast h4
        _ = 2 * (d : ℝ) * ((n / d : ℕ) : ℝ) := by push_cast; ring
    have hpos : (0 : ℝ) < ((n / d : ℕ) : ℝ) := by exact_mod_cast hnd1
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1d : 1 / ((n / d : ℕ) : ℝ) ≤ 2 * (d : ℝ) / (n : ℝ) := by
      rw [div_le_div_iff₀ hpos hnpos, one_mul]
      exact key
    calc ((d : ℝ) ^ 2)⁻¹ * (1 / ((n / d : ℕ) : ℝ))
        ≤ ((d : ℝ) ^ 2)⁻¹ * (2 * (d : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left h1d (inv_nonneg.mpr (sq_nonneg _))
      _ = 2 / ((d : ℝ) * (n : ℝ)) := by
          field_simp [ne_of_gt hdpos, ne_of_gt hnpos]
          try ring
  rw [E_tail, abs_neg, ← Real.norm_eq_abs]
  calc ‖∑' k : ℕ, if n < k then (if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0) else 0‖
      ≤ ∑' k : ℕ, ‖if n < k then (if d ∣ k then (μ k : ℝ) / (k : ℝ) ^ 2 else 0) else 0‖ :=
        norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' k : ℕ, (if n < k then (if d ∣ k then ((k : ℝ) ^ 2)⁻¹ else 0) else 0) :=
        hasSum_le step2 hsum_norm.hasSum hdom.hasSum
    _ = ∑' m : ℕ, (if n < d * m then (((d * m : ℕ) : ℝ) ^ 2)⁻¹ else 0) :=
        step4.trans (tsum_congr step4')
    _ = ((d : ℝ) ^ 2)⁻¹ * ∑' m : ℕ, (if (n / d : ℕ) < m then ((m : ℝ) ^ 2)⁻¹ else 0) := by
        rw [tsum_congr step5]
        exact tsum_mul_left
    _ ≤ ((d : ℝ) ^ 2)⁻¹ * (1 / ((n / d : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hT2 (inv_nonneg.mpr (sq_nonneg _))
    _ ≤ 2 / ((d : ℝ) * (n : ℝ)) := hfin


/-- `ζ(2)·J₂(d)·A_d(∞)·E_d(n) = μ(d)·E_d(n)` pointwise. -/
theorem zeta_jordan2AinfE (d n : ℕ) :
    zeta2 * (jordan2 d * Ainf d * E d n) = (μ d : ℝ) * E d n := by
  by_cases hd : Squarefree d
  · have hJ : jordan2 d ≠ 0 := ne_of_gt (jordan2_pos hd.ne_zero)
    rw [Ainf_eq d hd]
    field_simp [hJ, zeta2_ne_zero]
    try ring
  · rw [Ainf_eq_zero_of_not_squarefree hd]
    have hμ : (μ d : ℝ) = 0 := by exact_mod_cast moebius_eq_zero_of_not_squarefree hd
    simp [hμ]

theorem summable_jordan2Ainf_sq : Summable fun d : ℕ => jordan2 d * (Ainf d) ^ 2 :=
  (summable_mu_sq_div_jordan2.mul_left (zeta2⁻¹ ^ 2)).congr fun d => (jordan2Ainf_sq d).symm

/-- The `J₂A²`-tail is `ζ(2)⁻²` times the `μ²/J₂`-tail. -/
theorem tail_jordan2Ainf_sq (n : ℕ) :
    ∑' d : ℕ, (if n < d then jordan2 d * (Ainf d) ^ 2 else 0)
      = zeta2⁻¹ ^ 2 * ∑' d : ℕ, (if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0) := by
  have h : ∀ d : ℕ, (if n < d then jordan2 d * (Ainf d) ^ 2 else 0)
      = zeta2⁻¹ ^ 2 * (if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0) := by
    intro d
    by_cases hd : n < d
    · rw [if_pos hd, if_pos hd, jordan2Ainf_sq d]
    · rw [if_neg hd, if_neg hd, mul_zero]
  rw [tsum_congr h]
  exact tsum_mul_left

/-- **Theorem 1 (exact positive decomposition).**
`S(n) = (1/ζ(2)) ∑_{d > n} μ(d)²/J₂(d) + ζ(2) ∑_{d ≤ n} J₂(d) E_d(n)²`,
both terms nonnegative. -/
theorem S_decomposition (n : ℕ) (hn : 1 ≤ n) :
    S n = zeta2⁻¹ * (∑' d : ℕ, if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0)
        + zeta2 * ∑ d ∈ Finset.Icc 1 n, jordan2 d * (E d n) ^ 2 := by
  have hg0 : (fun d : ℕ => jordan2 d * (Ainf d) ^ 2) 0 = 0 := by simp [jordan2]
  have split := tsum_split_Icc_tail summable_jordan2Ainf_sq hg0 n
  have htotal : ∑' d : ℕ, jordan2 d * (Ainf d) ^ 2 = zeta2⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact total_one)
  have htJ := tail_jordan2Ainf_sq n
  have hexp : ∀ d : ℕ, jordan2 d * (A d n) ^ 2
      = jordan2 d * (Ainf d) ^ 2 + 2 * (jordan2 d * Ainf d * E d n)
        + jordan2 d * (E d n) ^ 2 := by
    intro d
    have hE : A d n = Ainf d + E d n := by rw [E]; ring
    rw [hE]
    ring
  have hsum_exp : ∑ d ∈ Finset.Icc 1 n, jordan2 d * (A d n) ^ 2
      = ∑ d ∈ Finset.Icc 1 n, jordan2 d * (Ainf d) ^ 2
        + 2 * ∑ d ∈ Finset.Icc 1 n, jordan2 d * Ainf d * E d n
        + ∑ d ∈ Finset.Icc 1 n, jordan2 d * (E d n) ^ 2 := by
    rw [Finset.sum_congr rfl (fun d _ => hexp d)]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hmid : zeta2 * ∑ d ∈ Finset.Icc 1 n, jordan2 d * Ainf d * E d n
      = ∑ d ∈ Finset.Icc 1 n, (μ d : ℝ) * E d n := by
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun d _ => zeta_jordan2AinfE d n)]
  have e1 : zeta2 * ∑ d ∈ Finset.Icc 1 n, jordan2 d * (Ainf d) ^ 2
      = 1 - zeta2⁻¹ * ∑' d : ℕ, (if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0) := by
    have e2 : ∑ d ∈ Finset.Icc 1 n, jordan2 d * (Ainf d) ^ 2
        = zeta2⁻¹
          - zeta2⁻¹ ^ 2 * ∑' d : ℕ, (if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0) := by
      linarith [split, htotal, htJ]
    rw [e2]
    field_simp [zeta2_ne_zero]
    try ring
  have e3 : zeta2 * ∑ d ∈ Finset.Icc 1 n, jordan2 d * (A d n) ^ 2
      = (1 - zeta2⁻¹ * ∑' d : ℕ, (if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0))
        + 2 * (∑ d ∈ Finset.Icc 1 n, (μ d : ℝ) * E d n)
        + zeta2 * ∑ d ∈ Finset.Icc 1 n, jordan2 d * (E d n) ^ 2 := by
    rw [hsum_exp]
    rw [show zeta2 * (∑ d ∈ Finset.Icc 1 n, jordan2 d * (Ainf d) ^ 2
        + 2 * ∑ d ∈ Finset.Icc 1 n, jordan2 d * Ainf d * E d n
        + ∑ d ∈ Finset.Icc 1 n, jordan2 d * (E d n) ^ 2)
      = zeta2 * ∑ d ∈ Finset.Icc 1 n, jordan2 d * (Ainf d) ^ 2
        + 2 * (zeta2 * ∑ d ∈ Finset.Icc 1 n, jordan2 d * Ainf d * E d n)
        + zeta2 * ∑ d ∈ Finset.Icc 1 n, jordan2 d * (E d n) ^ 2 from by ring]
    rw [e1, hmid]
  have hg := gram_identity n hn
  have hss := signed_sum n hn
  linarith [hg, e3, hss]

/-- **Theorem 1, corollary bound (paper eq. (6)).** `0 ≤ S(n) < (1 + 4ζ(2))/n`. -/
theorem S_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ S n ∧ S n < (1 + 4 * zeta2) / n := by
  constructor
  · show 0 ≤ ∑' q : ℕ, if n < q then (M q n : ℝ) ^ 2 / (q : ℝ) ^ 2 else 0
    exact tsum_nonneg fun q => by
      by_cases hq : n < q
      · rw [if_pos hq]
        exact div_nonneg (sq_nonneg _) (sq_nonneg _)
      · rw [if_neg hq]
  · rw [S_decomposition n hn]
    have habsμ : ∀ k : ℕ, |(μ k : ℝ)| ≤ 1 := by
      intro k
      have h2 : |(μ k : ℤ)| ≤ 1 := by
        rw [ArithmeticFunction.abs_moebius]
        split_ifs <;> norm_num
      calc |(μ k : ℝ)| = ((|(μ k : ℤ)| : ℤ) : ℝ) := by rw [Int.cast_abs]
        _ ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h2
        _ = 1 := by norm_num
    have hT2 : ∑' d : ℕ, (if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0)
        ≤ zeta2 * ∑' d : ℕ, (if n < d then ((d : ℝ) ^ 2)⁻¹ else 0) := by
      have hpt : ∀ d : ℕ, (if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0)
          ≤ zeta2 * (if n < d then ((d : ℝ) ^ 2)⁻¹ else 0) := by
        intro d
        by_cases hd : n < d
        · rw [if_pos hd, if_pos hd]
          have hd0 : d ≠ 0 := by omega
          have hJ := jordan2_pos hd0
          have hge := jordan2_ge d hd0
          have hμ2 : (μ d : ℝ) ^ 2 ≤ 1 := by
            have hμ := habsμ d
            nlinarith [(abs_le.mp hμ).1, (abs_le.mp hμ).2]
          have hge2 : (d : ℝ) ^ 2 ≤ zeta2 * jordan2 d := by
            have h3 := (div_le_iff₀ zeta2_pos).mp hge
            linarith [h3]
          rw [← div_eq_mul_inv, div_le_div_iff₀ hJ (pow_pos (show (0:ℝ) < (d:ℝ) by exact_mod_cast (by omega : 0 < d)) 2)]
          calc (μ d : ℝ) ^ 2 * (d : ℝ) ^ 2
              ≤ 1 * (d : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hμ2 (sq_nonneg _)
            _ = (d : ℝ) ^ 2 := one_mul _
            _ ≤ zeta2 * jordan2 d := hge2
        · rw [if_neg hd, if_neg hd, mul_zero]
      have hdom2 : Summable fun d : ℕ => (if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0) :=
        (summable_mu_sq_div_jordan2.indicator {d : ℕ | n < d}).congr fun d => by
          by_cases h : n < d <;> simp [Set.indicator, h]
      have hdom3 : Summable fun d : ℕ => zeta2 * (if n < d then ((d : ℝ) ^ 2)⁻¹ else 0) :=
        ((summable_one_div_nat_sq.indicator {d : ℕ | n < d}).congr fun d => by
          by_cases h : n < d <;> simp [Set.indicator, h]).mul_left zeta2
      calc ∑' d : ℕ, (if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0)
          ≤ ∑' d : ℕ, zeta2 * (if n < d then ((d : ℝ) ^ 2)⁻¹ else 0) :=
            hasSum_le hpt hdom2.hasSum hdom3.hasSum
        _ = zeta2 * ∑' d : ℕ, (if n < d then ((d : ℝ) ^ 2)⁻¹ else 0) := tsum_mul_left
    have hfirst : zeta2⁻¹ * (∑' d : ℕ, if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0)
        < 1 / (n : ℝ) :=
      calc zeta2⁻¹ * (∑' d : ℕ, if n < d then (μ d : ℝ) ^ 2 / jordan2 d else 0)
          ≤ zeta2⁻¹ * (zeta2 * ∑' d : ℕ, (if n < d then ((d : ℝ) ^ 2)⁻¹ else 0)) :=
            mul_le_mul_of_nonneg_left hT2 (inv_nonneg.mpr (le_of_lt zeta2_pos))
        _ = ∑' d : ℕ, (if n < d then ((d : ℝ) ^ 2)⁻¹ else 0) := by
            rw [← mul_assoc, inv_mul_cancel₀ zeta2_ne_zero, one_mul]
        _ < 1 / (n : ℝ) := tsum_one_div_sq_tail_strict n hn
    have hsecond : zeta2 * ∑ d ∈ Finset.Icc 1 n, jordan2 d * (E d n) ^ 2
        ≤ 4 * zeta2 / (n : ℝ) := by
      have hpt2 : ∀ d ∈ Finset.Icc 1 n, jordan2 d * (E d n) ^ 2
          ≤ (d : ℝ) ^ 2 * (2 / ((d : ℝ) * (n : ℝ))) ^ 2 := by
        intro d hdI
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
        have hdn2 : d ≤ n := (Finset.mem_Icc.mp hdI).2
        have hE := E_abs_le d n hd1 hn hdn2
        have hJ2 := jordan2_le d
        have hE2 : (E d n) ^ 2 ≤ (2 / ((d : ℝ) * (n : ℝ))) ^ 2 := by
          have h2 : (E d n) ^ 2 = |E d n| ^ 2 := (sq_abs (E d n)).symm
          rw [h2]
          exact pow_le_pow_left₀ (abs_nonneg _) hE 2
        calc jordan2 d * (E d n) ^ 2
            ≤ (d : ℝ) ^ 2 * (E d n) ^ 2 :=
              mul_le_mul_of_nonneg_right hJ2 (sq_nonneg _)
          _ ≤ (d : ℝ) ^ 2 * (2 / ((d : ℝ) * (n : ℝ))) ^ 2 :=
              mul_le_mul_of_nonneg_left hE2 (sq_nonneg _)
      calc zeta2 * ∑ d ∈ Finset.Icc 1 n, jordan2 d * (E d n) ^ 2
          ≤ zeta2 * ∑ d ∈ Finset.Icc 1 n, (d : ℝ) ^ 2 * (2 / ((d : ℝ) * (n : ℝ))) ^ 2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt2) (le_of_lt zeta2_pos)
        _ = zeta2 * ∑ d ∈ Finset.Icc 1 n, (4 / (n : ℝ) ^ 2) := by
            congr 1
            apply Finset.sum_congr rfl
            intro d hdI
            have hd0 : (d : ℝ) ≠ 0 := by
              have hdI' := Finset.mem_Icc.mp hdI
              exact_mod_cast (by omega : d ≠ 0)
            have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
            field_simp [hd0, hn0]
            try ring
        _ = zeta2 * ((n : ℝ) * (4 / (n : ℝ) ^ 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
        _ = 4 * zeta2 / (n : ℝ) := by
            have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
            field_simp [hn0]
            try ring
    have hcomb : (1 + 4 * zeta2) / (n : ℝ) = 1 / (n : ℝ) + 4 * zeta2 / (n : ℝ) := by ring
    rw [hcomb]
    exact add_lt_add_of_lt_of_le hfirst hsecond

/-- The elementary series-tail lemma used for the bound (paper Lemma).
Proof: `1/m² ≤ 2(1/m - 1/(m+1))` for `m ≥ 1`, then telescope the partial sums. -/
theorem tsum_one_div_sq_tail {x : ℝ} (hx : 1 ≤ x) :
    ∑' m : ℕ, (if (x : ℝ) < m then ((m : ℝ) ^ 2)⁻¹ else 0) ≤ 2 / x := by
  classical
  set M : ℕ := ⌊x⌋₊ + 1 with hMdef
  have hMx : (x : ℝ) < M := by
    rw [hMdef, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one x
  have hiff : ∀ m : ℕ, ((x : ℝ) < (m : ℝ)) ↔ M ≤ m := by
    intro m
    constructor
    · intro h
      by_contra hmc
      push_neg at hmc
      have h1 : m ≤ ⌊x⌋₊ := by omega
      have h2 : (m : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
      have h3 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx)
      linarith
    · intro h
      exact lt_of_lt_of_le hMx (by exact_mod_cast h)
  have hkey : ∀ m : ℕ, 1 ≤ m →
      ((m : ℝ) ^ 2)⁻¹ ≤ 2 * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) := by
    intro m hm1
    have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have e1 : 2 * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) = 2 / ((m : ℝ) * ((m : ℝ) + 1)) := by
      field_simp
      ring
    have hm1r : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    rw [e1, ← one_div ((m : ℝ) ^ 2), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hm1r]
  have hpart : ∀ K : ℕ,
      ∑ m ∈ Finset.range K, (if (x : ℝ) < m then ((m : ℝ) ^ 2)⁻¹ else 0) ≤ 2 / x := by
    intro K
    by_cases hMK : M ≤ K
    · have h1 : ∑ m ∈ Finset.range K, (if (x : ℝ) < m then ((m : ℝ) ^ 2)⁻¹ else 0)
          = ∑ m ∈ Finset.Ico M K, ((m : ℝ) ^ 2)⁻¹ := by
        have hsub : Finset.Ico M K ⊆ Finset.range K := by
          intro m hm
          rw [Finset.mem_Ico] at hm
          rw [Finset.mem_range]
          exact hm.2
        have hz : ∀ m ∈ Finset.range K, m ∉ Finset.Ico M K →
            (if (x : ℝ) < m then ((m : ℝ) ^ 2)⁻¹ else 0) = 0 := by
          intro m hm hnm
          rw [Finset.mem_range] at hm
          rw [Finset.mem_Ico] at hnm
          have hmM : m < M := by omega
          have hnot : ¬ (x : ℝ) < m := by
            rw [hiff m]
            omega
          simp [hnot]
        rw [← Finset.sum_subset hsub hz]
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mem_Ico] at hm
        have hxm : (x : ℝ) < m := (hiff m).mpr hm.1
        simp [hxm]
      rw [h1]
      have h4 : ∑ m ∈ Finset.Ico M K, (1 / (m : ℝ) - 1 / ((m : ℝ) + 1))
          = 1 / (M : ℝ) - 1 / (K : ℝ) := by
        rw [Finset.sum_Ico_eq_sum_range]
        have hcongr : ∀ j ∈ Finset.range (K - M),
            (1 / (((M + j : ℕ)) : ℝ) - 1 / ((((M + j : ℕ)) : ℝ) + 1))
              = (-1 / (((M + (j + 1) : ℕ)) : ℝ)) - (-1 / (((M + j : ℕ)) : ℝ)) := by
          intro j hj
          push_cast
          ring
        rw [Finset.sum_congr rfl hcongr,
          Finset.sum_range_sub (fun j : ℕ => -1 / (((M + j : ℕ)) : ℝ)) (K - M)]
        have hKM : M + (K - M) = K := by omega
        simp [hKM]
        ring
      calc ∑ m ∈ Finset.Ico M K, ((m : ℝ) ^ 2)⁻¹
          ≤ ∑ m ∈ Finset.Ico M K, 2 * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) := by
            apply Finset.sum_le_sum
            intro m hm
            rw [Finset.mem_Ico] at hm
            exact hkey m (by omega)
        _ = 2 * (1 / (M : ℝ) - 1 / (K : ℝ)) := by rw [← h4, ← Finset.mul_sum]
        _ ≤ 2 * (1 / (M : ℝ)) := by
            have hK0 : (0 : ℝ) ≤ 1 / (K : ℝ) := by positivity
            linarith
        _ ≤ 2 / x := by
            have hx0 : (0 : ℝ) < x := zero_lt_one.trans_le hx
            have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
              rw [hMdef]
              push_cast
              have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx)
              have : (1 : ℝ) ≤ x := hx
              linarith
            have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
            rw [mul_one_div, div_le_div_iff₀ hM0 hx0]
            nlinarith [le_of_lt hMx]
    · have hzero : ∑ m ∈ Finset.range K, (if (x : ℝ) < m then ((m : ℝ) ^ 2)⁻¹ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        rw [Finset.mem_range] at hm
        have hnot : ¬ (x : ℝ) < m := by
          rw [hiff m]
          omega
        simp [hnot]
      rw [hzero]
      positivity
  have hsumm : Summable (fun m : ℕ => if (x : ℝ) < m then ((m : ℝ) ^ 2)⁻¹ else 0) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
      ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two)
    · by_cases h : (x : ℝ) < m <;> simp [h] <;> positivity
    · by_cases h : (x : ℝ) < m
      · rw [if_pos h]
        exact (one_div ((m : ℝ) ^ 2)).symm.le
      · simp only [h, if_false]
        positivity
  have hh := hsumm.hasSum
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun m => by split_ifs <;> positivity)] at hh
  exact le_of_tendsto hh (Filter.Eventually.of_forall hpart)

/-! ## Theorem 2: the scaling limit n·S(n) → C -/

/-- The coprime-kernel constant `κ(A,B)` (paper eq. (11)).
No case split is needed: `μ` vanishes on non-squarefree arguments, so the
"0 otherwise" branch is automatic. Used in the paper only for coprime `A,B`. -/
noncomputable def kappa (A B : ℕ) : ℝ :=
  (μ A : ℝ) * (μ B : ℝ) / zeta2 * ∏ p ∈ (A * B).primeFactors, (p : ℝ) / (p + 1)

/-- The block constants `D_j = ∑_{a,b ≤ j} κ(a/(a,b), b/(a,b)) / [a,b]`
(paper eq. (9)), where `[a,b]` is the lcm. -/
noncomputable def D (j : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 j, ∑ b ∈ Finset.Icc 1 j,
    kappa (a / Nat.gcd a b) (b / Nat.gcd a b) / (Nat.lcm a b : ℝ)

/-- The scaling-limit constant `C = ∑_{j ≥ 1} D_j / (j(j+1))` (paper eq. (8)).
Absolutely convergent; the `j = 0` term is `0`. -/
noncomputable def Cconst : ℝ :=
  ∑' j : ℕ, D j / (j * (j + 1) : ℝ)

/-- Fixed-block limit (paper eq. (17)): for each fixed `j`,
`n ∑_{jn < q ≤ (j+1)n} M(q,n)²/q² → D_j/(j(j+1))`.
The input is the elementary squarefree-sieve mean of `μ(Am)μ(Bm)` (eq. (16));
the sieve itself (natural density of squarefree `m` coprime to a fixed modulus)
is elementary but not currently a named Mathlib result. -/
theorem block_limit (j : ℕ) (hj : 1 ≤ j) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) * ∑ q ∈ Finset.Ioc (j * n) ((j + 1) * n),
          (M q n : ℝ) ^ 2 / (q : ℝ) ^ 2)
      atTop (𝓝 (D j / (j * (j + 1) : ℝ))) := by
  sorry

/-- **Theorem 2 (scaling limit).** Unconditionally, `n·S(n) → C`.
The proof combines `block_limit` for fixed blocks with uniform tail tightness,
which uses the *global* BDT bound `S(x,z) ≪ x` (`bdt_global` below). -/
theorem scaling_limit :
    Tendsto (fun n : ℕ => (n : ℝ) * S n) atTop (𝓝 Cconst) := by
  sorry

/-- The closed double-series form of `C` (paper eq. (12), second formula):
`C = ∑_{(A,B)=1, squarefree} μ(A)μ(B)/max(A,B) · ∏_{p∣AB} 1/(p+1)`.
`μ` kills the non-squarefree pairs automatically; the coprimality restriction
is the explicit indicator. Rearrangement is justified by absolute convergence
(paper eq. (18)). -/
noncomputable def CconstClosed : ℝ :=
  ∑' p : ℕ × ℕ,
    if Nat.Coprime p.1 p.2 then
      (μ p.1 : ℝ) * (μ p.2 : ℝ) / (max p.1 p.2 : ℝ)
        * ∏ q ∈ (p.1 * p.2).primeFactors, ((q : ℝ) + 1)⁻¹
    else 0

theorem Cconst_eq_closed : Cconst = CconstClosed := by
  sorry

/-- Positivity lower bound (paper eq. (13)): `C ≥ 1/(2ζ(2)) = 3/π²`,
from `D_j ≥ 0` (each `D_j` is a limiting mean square) and `D₁ = κ(1,1) = 1/ζ(2)`. -/
theorem Cconst_lower_bound : 1 / (2 * zeta2) ≤ Cconst := by
  sorry

/-! ## Theorem 3: the quantitative block-tail law

This is where the genuinely external analytic input lives. We state the two
de la Bretèche–Dress–Tenenbaum (2020) results as `sorry`-ed theorems and
derive the tail law from them; nothing below them is in Mathlib. -/

/-- The Dress–Iwaniec–Tenenbaum constant (numerically ≈ 0.4407).
Its defining value is the limit of the lcm quadratic form
`z⁻¹ ∑_{d,e ≤ z} μ(d)μ(e)/[d,e]`; declaring it `opaque` keeps this file honest
about the fact that the constant is analytic input, not a computed definition. -/
opaque DITconst : ℝ

/-- The BDT logarithmic saving `ℒ(y) = exp((log y)^{3/5} / (log log y)^{1/5})`. -/
noncomputable def calL (y : ℝ) : ℝ :=
  Real.exp ((Real.log y) ^ (3 / 5 : ℝ) / (Real.log (Real.log y)) ^ (1 / 5 : ℝ))

/-- The BDT counting sum `S(x,z) = ∑_{q ≤ x} M(q,z)²` (paper eq. (3)),
as a real-valued function of real `x` via floor. -/
noncomputable def Scount (x : ℝ) (z : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (M q z : ℝ) ^ 2

/-- **External input 1** — de la Bretèche–Dress–Tenenbaum (2020), Thm 1.1:
for some absolute `c > 0`,
`S(x,z) = 𝔏 x + O(x / ℒ(3ξ)^c)` uniformly for `ξ ≤ z ≤ x/ξ`.
NOT in Mathlib; the hard analytic ingredient. Stated as an explicit-modulus
uniform bound. -/
theorem bdt_uniform_mean_square :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x : ℝ) (z : ℕ) (ξ : ℝ),
        1 ≤ ξ → ξ ≤ (z : ℝ) → (z : ℝ) ≤ x / ξ →
          |Scount x z - DITconst * x| ≤ K * x / calL (3 * ξ) ^ c := by
  sorry

/-- **External input 2** — BDT (2020), eq. (1.5): the global bound
`S(x,z) ≪ x` uniformly for all `x,z ≥ 1`. This is the tightness input for
Theorem 2 and the convergence input for the Stieltjes integral in Theorem 3.
NOT in Mathlib. -/
theorem bdt_global :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x z : ℕ), 1 ≤ x → 1 ≤ z → Scount x z ≤ K * x := by
  sorry

/-- The normalized block tail `R_n(J) = n ∑_{q > Jn} M(q,n)²/q²` (paper eq. (14)). -/
noncomputable def R (n : ℕ) (J : ℝ) : ℝ :=
  (n : ℝ) * ∑' q : ℕ, if (J * n : ℝ) < q then (M q n : ℝ) ^ 2 / (q : ℝ) ^ 2 else 0

/-- **Theorem 3 (quantitative block-tail law).** With `c > 0` the BDT exponent,
uniformly for `1 ≤ J ≤ n`: `R_n(J) = 𝔏/J + O(1/(J ℒ(3J)^c))`.
A direct Stieltjes/partial-summation corollary of `bdt_uniform_mean_square`;
Mathlib has the analytic infrastructure (integration by parts / Abel
summation) but the glue is real work. -/
theorem block_tail_law :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (n : ℕ) (J : ℝ), 1 ≤ n → 1 ≤ J → J ≤ (n : ℝ) →
        |R n J - DITconst / J| ≤ K / (J * calL (3 * J) ^ c) := by
  sorry

/-- The limiting block-constant tail (paper eq. (15)):
`∑_{j ≥ J} D_j/(j(j+1)) = 𝔏/J + O(1/(J ℒ(3J)^c))` as `J → ∞`.
Follows from `block_tail_law` plus `block_limit` by letting `n → ∞`. -/
theorem block_constant_tail :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ J : ℕ, 1 ≤ J →
        |(∑' j : ℕ, if J ≤ j then D j / (j * (j + 1) : ℝ) else 0)
          - DITconst / J| ≤ K / (J * calL (3 * J) ^ c) := by
  sorry

/-- Consequence recorded in the paper's remark: `D_J → 𝔏` as `J → ∞`. -/
theorem D_tendsto_DIT :
    Tendsto D atTop (𝓝 DITconst) := by
  sorry

/-! ## Ramaré's master identity (Remark) — the equivalent reformulation -/

/-- Ramaré's identity at `σ = 3/2`: `1 + S(n) = ζ(2) · S₁(n)` where
`S₁(n) = ∑_{d,e ≤ n} μ(d)μ(e)/[d,e]²`. This is finite-sum rearrangement of an
absolutely convergent series — elementary, and a good early formalization target. -/
noncomputable def S1 (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 n, ∑ e ∈ Finset.Icc 1 n,
    (μ d : ℝ) * (μ e : ℝ) / ((Nat.lcm d e : ℝ) ^ 2)

theorem ramare_parseval (n : ℕ) :
    1 + S n = zeta2 * S1 n := by
  sorry

/-- Theorem 2 restated through Ramaré's lens (paper eq. (19)):
`S₁(n) = 1/ζ(2) + (C/ζ(2))·(1/n) + o(1/n)`. -/
theorem S1_tail :
    (fun n : ℕ => S1 n - zeta2⁻¹ - Cconst / (zeta2 * n)) =o[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  sorry

/-- Equivalent form: `n · (S₁(n) - 1/ζ(2)) → C/ζ(2)`. -/
theorem S1_tail_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ) * (S1 n - zeta2⁻¹)) atTop (𝓝 (Cconst / zeta2)) := by
  sorry

end TruncMoebius
