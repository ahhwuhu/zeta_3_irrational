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

-- lemma integral_legendre_mul_smooth_eq {n : ℕ} (f : ℝ → ℝ) :
--   ∫ (x : ℝ) in (0)..1, eval x (legendre n) * f x =
--   (- 1) ^ n / n ! * ∫ (x : ℝ) in (0)..1, x ^ n * (1 - x) ^ n * (Fderivative^[n] f) x := by
--   simp only [eval_mul, one_div, eval_C]
--   induction' n with n hn
--   · simp
--   · rw [← intervalIntegral.integral_const_mul]
--     sorry