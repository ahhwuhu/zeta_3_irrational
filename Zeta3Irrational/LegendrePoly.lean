import Mathlib

open scoped Nat
open BigOperators

namespace Polynomial

noncomputable abbrev legendre (n : ℕ) : ℝ[X] :=
  C (1 / n ! : ℝ) * derivative^[n] (X ^ n * (1 - X) ^ n)

lemma sub_pow{R : Type u_1} [CommRing R] (x : R) (y : R) (n : ℕ) :
    (x - y) ^ n = (Finset.range (n + 1)).sum fun (m : ℕ) => (n.choose m) • x ^ m * (- 1) ^ (n - m) * y ^ (n - m) := by
  rw [← Mathlib.Tactic.RingNF.add_neg, add_pow]
  apply Finset.sum_congr rfl
  intro m _
  field_simp
  have eq1 : (-y) ^ (n - m) = (-1) ^ (n - m) * y ^ (n - m) := by
    rw[neg_pow]
  rw[eq1]
  ring_nf

lemma sub_pow_special{R : Type u_1} [CommRing R] (x : R) (n : ℕ) :
    (x - x ^ 2) ^ n = (Finset.range (n + 1)).sum fun (m : ℕ) => (n.choose m) • (- 1) ^ m * x ^ (n + m) := by
  rw[← Mathlib.Tactic.RingNF.add_neg, add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro m hm
  rw[neg_pow, pow_two, mul_pow,← mul_assoc, mul_comm, mul_assoc, pow_mul_pow_sub, mul_assoc,
    ← pow_add, ← mul_assoc, nsmul_eq_mul, add_comm]
  rw[Finset.mem_range] at hm
  linarith

lemma Finsum_iterate_deriv {R : Type u_1} [CommRing R] {k : ℕ} {h : ℕ → ℕ} :
    derivative^[k] (∑ m in Finset.range (k + 1), (h m) • ((- 1) ^ m : R[X]) * X ^ (k + m)) =
    ∑ m in Finset.range (k + 1), (h m) • (- 1) ^ m * derivative^[k] (X ^ (k + m)) := by
  induction' k + 1 with n hn
  · simp only [Nat.zero_eq, Finset.range_zero, Finset.sum_empty, iterate_map_zero]
  · rw[Finset.sum_range, Finset.sum_range, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at *
    simp only [Fin.coe_castSucc, Fin.val_last, iterate_map_add, hn, add_right_inj]
    rw [nsmul_eq_mul, mul_assoc, ← nsmul_eq_mul, Polynomial.iterate_derivative_smul, nsmul_eq_mul,
      mul_assoc]
    have := Int.even_or_odd n
    rcases this with (hn1 | hn2)
    · simp_all only [nsmul_eq_mul, Int.even_coe_nat, Even.neg_pow, one_pow, one_mul]
    · simp_all only [nsmul_eq_mul, Int.odd_iff_not_even, Int.even_coe_nat, Nat.odd_iff_not_even,
      not_false_eq_true, Odd.neg_one_pow, neg_mul, one_mul, iterate_map_neg]

lemma legendre_eq_sum (n : ℕ) : legendre n = ∑ k in Finset.range (n + 1),
    C ((- 1) ^ k : ℝ) • (Nat.choose n k) * (Nat.choose (n + k) n) * X ^ k := by
  rw [legendre, ← mul_pow, mul_one_sub, ← pow_two, sub_pow_special, Finsum_iterate_deriv,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← mul_assoc, Polynomial.iterate_derivative_X_pow_eq_smul, Nat.descFactorial_eq_div
    (by omega), show n + x - n = x by omega, smul_eq_mul, nsmul_eq_mul, ← mul_assoc, mul_assoc,
    mul_comm]
  simp only [Int.reduceNeg, map_pow, map_neg, map_one]
  rw [Algebra.smul_def, algebraMap_eq, map_natCast, ← mul_assoc, ← mul_assoc, add_comm,
    Nat.add_choose]
  rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_comm]
  nth_rewrite 5 [mul_comm]
  congr 1
  nth_rewrite 2 [mul_comm]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  congr 1
  nth_rewrite 3 [mul_comm]
  congr 1
  apply Polynomial.ext
  intro m
  simp only [one_div, coeff_mul_C, coeff_natCast_ite, Nat.cast_ite, CharP.cast_eq_zero, ite_mul,
    zero_mul]
  if h : m = 0 then
    simp [h]
    rw [Nat.cast_div]
    · rw [← one_div, ← div_mul_eq_div_mul_one_div]
      norm_cast
      rw [Nat.cast_div]
      · exact Nat.factorial_mul_factorial_dvd_factorial_add x n
      · norm_cast
        apply mul_ne_zero (Nat.factorial_ne_zero x) (Nat.factorial_ne_zero n)
    · exact Nat.factorial_dvd_factorial (by omega)
    · norm_cast; exact Nat.factorial_ne_zero x
  else
    simp [h]

lemma legendre_eq_intpoly (n : ℕ) : ∃ a : ℕ → ℤ, legendre n = ∑ k in Finset.range (n + 1),
    (a k) • X ^ k := by
  simp_rw [legendre_eq_sum]
  use fun k => (- 1) ^ k * (Nat.choose n k) * (Nat.choose (n + k) n)
  apply Finset.sum_congr rfl
  intro x _
  simp

lemma deriv_one_sub_X {n i : ℕ} : (⇑derivative)^[i] ((1 - X) ^ n : ℝ[X]) =
    (-1) ^ i * (n.descFactorial i) • ((1 - X) ^ (n - i)) := by
  rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
    Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
    Polynomial.iterate_derivative_X_pow_eq_smul]
  rw [Algebra.smul_def, algebraMap_eq, map_natCast]
  simp

lemma legendre_eval_symm {n : ℕ} {x : ℝ} : eval x (legendre n) =
    (-1) ^ n * eval (1 - x) (legendre n) := by
  rw [mul_comm]
  simp only [eval_mul, one_div, eval_C]
  rw [mul_assoc]
  simp only [mul_eq_mul_left_iff, inv_eq_zero, Nat.cast_eq_zero]; left
  rw [Polynomial.iterate_derivative_mul]
  simp only [Nat.succ_eq_add_one, nsmul_eq_mul]
  rw [Polynomial.eval_finset_sum, Polynomial.eval_finset_sum, ← Finset.sum_flip, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.iterate_derivative_X_pow_eq_smul, eval_mul, eval_natCast,
    Algebra.smul_mul_assoc, eval_smul, eval_mul, eval_pow, eval_X, smul_eq_mul]
  simp only [Finset.mem_range, Nat.lt_add_one_iff] at hi
  rw [Nat.choose_symm hi, deriv_one_sub_X, deriv_one_sub_X]
  simp only [nsmul_eq_mul, eval_mul, eval_pow, eval_neg, eval_one, eval_natCast, eval_sub, eval_X,
    sub_sub_cancel]
  rw [mul_assoc]
  simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero]; left
  rw [show n - (n - i) = i by omega, ← mul_assoc, ← mul_assoc, mul_comm, ← mul_assoc]
  symm
  rw [← mul_assoc]
  nth_rewrite 4 [mul_comm]
  rw [← mul_assoc, ← mul_assoc, mul_assoc]
  congr 1
  rw [← pow_add, show i + n = n - i + 2 * i by omega, pow_add]
  simp

lemma n_derivative {a : ℝ} (n : ℕ): deriv^[n] (fun x ↦ 1 / (1 - a * x)) =
    (fun x ↦ (n) ! * (a ^ n) / (1 - a * x) ^ (n + 1)) := by
  induction' n with n hn
  · simp
  · rw [Function.iterate_succ_apply', hn]
    ext x
    if h : 1 - a * x = 0 then
      rw [h]
      simp only [differentiableAt_const, ne_eq, add_eq_zero, one_ne_zero, and_false, and_self,
        not_false_eq_true, zero_pow, div_zero]
      apply IsLocalExtr.deriv_eq_zero
      left

      sorry
    else
      -- rw [deriv_div]
      -- simp only [differentiableAt_const, deriv_mul, deriv_const', zero_mul, deriv_pow'', mul_zero,
      --   add_zero, zero_sub]
      sorry

lemma legendre_poly_eval_zero_eq_zero {m : ℕ} (h : m < n) :
    eval 0 ((⇑derivative)^[m] (X ^ n * (1 - X) ^ n) : ℝ[X]) = 0 := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finset_sum]
  apply Finset.sum_eq_zero
  intro x hx
  simp_all only [Nat.succ_eq_add_one, Finset.mem_range, nsmul_eq_mul, eval_mul, eval_natCast,
    mul_eq_zero, Nat.cast_eq_zero]
  right; left
  simp only [Polynomial.iterate_derivative_X_pow_eq_smul, eval_smul, eval_pow, eval_X, smul_eq_mul,
    mul_eq_zero, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt, pow_eq_zero_iff', ne_eq, true_and]
  right
  suffices n - (m - x) > 0 by linarith
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  rw [Nat.lt_add_one_iff] at hx
  calc
    m - x ≤ m := by simp
    _ < n := by exact h

lemma legendre_poly_eval_one_eq_zero {m : ℕ} (h : m < n) :
    eval 1 ((⇑derivative)^[m] (X ^ n * (1 - X) ^ n) : ℝ[X]) = 0 := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finset_sum]
  apply Finset.sum_eq_zero
  intro x hx
  simp_all only [Nat.succ_eq_add_one, Finset.mem_range, nsmul_eq_mul, eval_mul, eval_natCast,
    mul_eq_zero, Nat.cast_eq_zero]
  right; right
  rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
    Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
    Polynomial.iterate_derivative_X_pow_eq_smul]
  simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul, eval_pow,
    eval_neg, eval_one, eval_sub, eval_X, sub_self, smul_eq_mul, mul_eq_zero, Nat.cast_eq_zero,
    Nat.descFactorial_eq_zero_iff_lt, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, false_and,
    true_and, false_or]
  right
  suffices n - x > 0 by linarith
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  linarith

lemma integral_legendre_mul_smooth_eq_aux {n : ℕ} {a : ℝ} (m : ℕ) (h : m ≤ n) (ha : 0 < a ∧ a < 1):
    ∫ (x : ℝ) in (0)..1, eval x ((⇑derivative)^[n] (X ^ n * (1 - X) ^ n)) * (fun x ↦ 1 / (1 - a * x)) x =
    (-1) ^ m * ∫ (x : ℝ) in (0)..1, eval x ((⇑derivative)^[n - m] (X ^ n * (1 - X) ^ n)) *
    (deriv^[m] fun x ↦ 1 / (1 - a * x)) x := by
  induction' m with m hm
  · simp
  · have h₀ : m < n := by linarith
    have h₁ : n - (m + 1) < n := by omega
    rw [hm (LT.lt.le h₀), pow_add, pow_one, mul_assoc]
    congr
    symm
    rw [show n - m = n - (m + 1) + 1 by omega, Function.iterate_succ_apply']
    rw [neg_one_mul, neg_eq_iff_eq_neg, intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := fun x ↦ eval x ((⇑derivative)^[n - (m + 1)] (X ^ n * (1 - X) ^ n : ℝ[X])))
      (u' := fun x ↦ eval x (derivative ((⇑derivative)^[n - (m + 1)] (X ^ n * (1 - X) ^ n : ℝ[X]))))
      (v := fun x ↦ (deriv^[m] fun x ↦ 1 / (1 - a * x)) x)]
    · rw [legendre_poly_eval_one_eq_zero h₁, legendre_poly_eval_zero_eq_zero h₁]
      simp only [zero_mul, sub_self, zero_sub, Function.iterate_succ_apply']
    · simp_rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finset_sum]
      apply continuousOn_finset_sum
      intro i _
      simp_rw [Algebra.smul_def, eval_mul]
      apply ContinuousOn.mul
      · simp only [eq_natCast, eval_natCast, ge_iff_le, zero_le_one, Set.uIcc_of_le]
        apply continuousOn_const
      · apply ContinuousOn.mul
        · simp_rw [Polynomial.iterate_derivative_X_pow_eq_smul]
          simp only [eval_smul, eval_pow, eval_X, smul_eq_mul, ge_iff_le, zero_le_one,
            Set.uIcc_of_le]
          apply ContinuousOn.mul continuousOn_const (ContinuousOn.pow continuousOn_id _)
        · rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
            Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
            Polynomial.iterate_derivative_X_pow_eq_smul]
          simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul,
            eval_pow, eval_neg, eval_one, eval_sub, eval_X, smul_eq_mul, ge_iff_le, zero_le_one,
            Set.uIcc_of_le]
          refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul continuousOn_const ?_)
          apply ContinuousOn.pow (ContinuousOn.sub continuousOn_const continuousOn_id)
    · simp_rw [n_derivative]
      apply ContinuousOn.div continuousOn_const
      · apply ContinuousOn.pow (ContinuousOn.sub continuousOn_const (ContinuousOn.mul continuousOn_const continuousOn_id))
      · intro x hx
        simp only [ge_iff_le, zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hx
        suffices (1 - a * x) ^ (m + 1) > 0 by linarith
        apply pow_pos
        nlinarith
    · intro x _
      simp_rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finset_sum]
      simp only [Nat.succ_eq_add_one, nsmul_eq_mul, eval_mul, eval_natCast, map_sum, eval_finset_sum]
      apply HasDerivAt.sum
      intro i _
      simp only [derivative_mul, derivative_natCast, zero_mul, zero_add, eval_mul, eval_natCast,
        eval_add]
      apply HasDerivAt.const_mul
      apply HasDerivAt.mul
      · rw [Polynomial.iterate_derivative_X_pow_eq_smul]
        simp only [eval_smul, eval_pow, eval_X, smul_eq_mul, LinearMapClass.map_smul,
          derivative_X_pow, map_natCast, eval_mul, eval_natCast]
        apply HasDerivAt.const_mul
        apply hasDerivAt_pow
      · rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
          Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
          Polynomial.iterate_derivative_X_pow_eq_smul]
        simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul,
          eval_pow, eval_neg, eval_one, eval_sub, eval_X, smul_eq_mul, LinearMapClass.map_smul]
        apply HasDerivAt.const_mul
        simp only [derivative_mul, eval_add, eval_mul, eval_pow, eval_sub, eval_one, eval_X,
          eval_neg]
        have h1 : (derivative ((-1) ^ i : ℝ[X])) = 0 := by
          rw [show ((-1) ^ i : ℝ[X]) = C ((-1) ^ i) by simp, derivative_C]
        rw [h1, eval_zero, zero_mul, zero_add]
        apply HasDerivAt.const_mul
        rw [show (1 - X : ℝ[X]) ^ (n - i) = (X ^ (n - i) : ℝ[X]).comp (1 - X) by simp,
          Polynomial.derivative_comp_one_sub_X (p := X ^ (n - i)),
          Polynomial.derivative_X_pow]
        simp only [mul_comp, pow_comp, X_comp, eval_mul, map_natCast, natCast_comp, eval_neg,
          eval_mul, eval_natCast, eval_pow, eval_sub, eval_one, eval_X]
        rw [← mul_neg_one]
        apply HasDerivAt.pow
        apply HasDerivAt.const_sub
        apply hasDerivAt_id
    · intro x hx
      simp only [ge_iff_le, zero_le_one, min_eq_left, max_eq_right, Set.mem_Ioo] at hx
      have (x : ℝ) : deriv (deriv^[m] fun x ↦ 1 / (1 - a * x)) x = Function.eval x (deriv (deriv^[m] fun x ↦ 1 / (1 - a * x))) := by
        simp only [one_div, Function.eval]
      simp_rw [this]
      simp_rw [← Function.iterate_succ_apply', Nat.succ_eq_add_one, Function.eval, n_derivative]
      have : ↑(m + 1)! * a ^ (m + 1) / (1 - a * x) ^ (m + 1 + 1) =
          ((deriv (fun _ ↦ (↑m ! * a ^ m : ℝ)) x) * (1 - a * x) ^ (m + 1) - (↑m ! * a ^ m : ℝ) *
          deriv (fun x ↦ (1 - a * x) ^ (m + 1)) x) / ((1 - a * x) ^ (m + 1)) ^ 2:= by
        rw [div_eq_div_iff]
        · simp only [differentiableAt_const, deriv_mul, deriv_const', zero_mul, deriv_pow'',
          mul_zero, add_zero, zero_sub]
          rw [← neg_mul, deriv_pow'', deriv_const_sub , deriv_const_mul]
          · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, deriv_id'', mul_one,
              mul_neg, neg_mul, neg_neg]
            norm_cast
            rw [Nat.factorial_succ, ← pow_mul', Nat.cast_mul]
            ring
          · apply differentiableAt_id
          · apply DifferentiableAt.const_sub
            apply DifferentiableAt.const_mul differentiableAt_id
        · suffices (1 - a * x) ^ (m + 1 + 1) > 0 by linarith
          apply pow_pos
          nlinarith
        · suffices (1 - a * x) ^ (m + 1) > 0 by nlinarith
          apply pow_pos
          nlinarith
      rw [this]
      apply HasDerivAt.div
      · simp only [differentiableAt_const, deriv_mul, deriv_const', zero_mul, deriv_pow'',
        mul_zero, add_zero]
        apply hasDerivAt_const
      · simp only [hasDerivAt_deriv_iff]
        apply DifferentiableAt.pow
        apply DifferentiableAt.const_sub
        apply DifferentiableAt.const_mul differentiableAt_id
      · suffices (1 - a * x) ^ (m + 1) > 0 by linarith
        apply pow_pos
        nlinarith
    · simp_rw [← Function.iterate_succ_apply', Polynomial.iterate_derivative_mul, Polynomial.eval_finset_sum]
      simp only [Nat.succ_eq_add_one, nsmul_eq_mul, eval_mul, eval_natCast]
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      apply continuousOn_finset_sum
      intro i _
      apply ContinuousOn.mul continuousOn_const
      · apply ContinuousOn.mul
        · simp_rw [Polynomial.iterate_derivative_X_pow_eq_smul]
          simp only [eval_smul, eval_pow, eval_X, smul_eq_mul]
          apply ContinuousOn.mul continuousOn_const (ContinuousOn.pow continuousOn_id _)
        · rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
            Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
            Polynomial.iterate_derivative_X_pow_eq_smul]
          simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul,
            eval_pow, eval_neg, eval_one, eval_sub, eval_X, smul_eq_mul, ge_iff_le, zero_le_one,
            Set.uIcc_of_le]
          refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul continuousOn_const ?_)
          apply ContinuousOn.pow (ContinuousOn.sub continuousOn_const continuousOn_id)
    · have (x : ℝ) : deriv (deriv^[m] fun x ↦ 1 / (1 - a * x)) x = Function.eval x (deriv (deriv^[m] fun x ↦ 1 / (1 - a * x))) := by
        simp only [one_div, Function.eval]
      simp_rw [this]
      simp_rw [← Function.iterate_succ_apply', Nat.succ_eq_add_one, Function.eval]
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      simp_rw [n_derivative]
      apply ContinuousOn.div continuousOn_const
      · apply ContinuousOn.pow (ContinuousOn.sub continuousOn_const (ContinuousOn.mul continuousOn_const continuousOn_id))
      · intro x hx
        simp only [Set.mem_Icc] at hx
        suffices (1 - a * x) ^ (m + 1 + 1) > 0 by linarith
        apply pow_pos
        nlinarith

lemma integral_legendre_mul_smooth_eq {n : ℕ} {a : ℝ} (h : 0 < a ∧ a < 1):
  ∫ (x : ℝ) in (0)..1, eval x (legendre n) * (fun x ↦ 1 / (1 - a * x)) x =
  (- 1) ^ n / n ! * ∫ (x : ℝ) in (0)..1, x ^ n * (1 - x) ^ n * (deriv^[n] fun x ↦ 1 / (1 - a * x)) x := by
  simp only [eval_mul, one_div, eval_C]
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  rw [← mul_one_div, one_div]
  nth_rw 4 [mul_comm]
  rw [mul_assoc]
  congr
  obtain h := integral_legendre_mul_smooth_eq_aux (n := n) (a := a) (m := n) (by norm_num) h
  simp only [one_div, ge_iff_le, le_refl, tsub_eq_zero_of_le, Function.iterate_zero, id_eq,
    eval_mul, eval_pow, eval_X, eval_sub, eval_one] at h
  rw [h]
  simp_rw [← mul_assoc]

lemma legendre_integral_special {a : ℝ} (ha : 0 < a ∧ a < 1) : ∫ (x : ℝ) in (0)..1, eval x (legendre n) / (1 - a * x) =
    (-1) ^ n * ∫ (x : ℝ) in (0)..1, x ^ n * (1 - x) ^ n * a ^ n / (1 - a * x) ^ (n + 1) := by
  have : ∫ (x : ℝ) in (0)..1, eval x (legendre n) / (1 - a * x) =
    ∫ (x : ℝ) in (0)..1, eval x (legendre n) * (1 / (1 - a * x)) := by
    rw [intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
      MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    apply MeasureTheory.setIntegral_congr (by simp)
    intro _ _
    group
  rw [this, integral_legendre_mul_smooth_eq ha, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_of_le (by norm_num), ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr (by simp)
  intro x hx
  simp only
  rw [n_derivative]
  simp_all only [Set.mem_Ioo, Set.mem_Icc]
  rw [← mul_assoc, mul_div, mul_div, div_eq_div_iff]
  · rw [mul_assoc, mul_assoc, mul_assoc, mul_comm, mul_div]
    symm
    rw [eq_div_iff]
    · ring
    · norm_cast
      exact Nat.factorial_ne_zero n
  · suffices (1 - a * x) ^ (n + 1) > 0 by linarith
    apply pow_pos
    nlinarith
  · suffices (1 - a * x) ^ (n + 1) > 0 by linarith
    apply pow_pos
    nlinarith
