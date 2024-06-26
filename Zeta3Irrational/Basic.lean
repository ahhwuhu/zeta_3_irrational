/-
A formal proof of the irrationality of Riemann-Zeta(3).
Author: Junqi Liu and Jujian Zhang.
-/
import Mathlib
import Zeta3Irrational.d

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
  intro x hx
  rw [← mul_assoc, Polynomial.iterate_derivative_X_pow_eq_smul, Nat.descFactorial_eq_div
    (show n  ≤ n + x by omega), show n + x - n = x by omega, smul_eq_mul,
    nsmul_eq_mul, ← mul_assoc, mul_assoc, mul_comm]
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
  -- have : (↑((x + n)! / (x ! * n !)) : ℝ[X]) = (↑((x + n)! / (x !))) * (↑(1 / n !) : ℝ[X]) := by
  --   push_cast
  --   sorry
  -- rw [this]
  -- congr 1
  -- rw [← algebraMap_eq, ← map_natCast (algebraMap ℝ ℝ[X])]
  sorry

lemma deriv_one_sub_X {n i : ℕ} : (⇑derivative)^[i] ((1 - X) ^ n : ℝ[X]) =
    (-1) ^ i * (n.descFactorial i) • ((1 - X) ^ (n - i)) := by
  rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
    Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
    Polynomial.iterate_derivative_X_pow_eq_smul]
  rw [Algebra.smul_def, algebraMap_eq, map_natCast]
  simp

lemma legendre_pos {n : ℕ} {x : ℝ} (hx : 0 < x ∧ x < 1) : eval x (legendre n) > 0 := by
  simp_all only [eval_mul, one_div, eval_C, gt_iff_lt]
  apply mul_pos
  · simp only [inv_pos, Nat.cast_pos]
    exact Nat.factorial_pos n
  · rw [Polynomial.iterate_derivative_mul]
    simp only [Nat.succ_eq_add_one, nsmul_eq_mul]
    rw [Polynomial.eval_finset_sum]
    sorry
    -- apply Finset.sum_pos _ (by simp)
    -- intro i hi
    -- simp only [Polynomial.iterate_derivative_X_pow_eq_smul, eval_mul, eval_natCast,
    --   Algebra.smul_mul_assoc, eval_smul, eval_mul, eval_pow, eval_X, smul_eq_mul]
    -- apply mul_pos
    -- · simp_all only [Finset.mem_range, Nat.cast_pos, Nat.lt_add_one_iff]
    --   exact Nat.choose_pos hi
    -- · apply mul_pos
    --   · rw [Nat.descFactorial_eq_div (by simp)]
    --     simp only [Finset.mem_range] at hi
    --     rw [show n - (n - i) = i by omega]
    --     sorry
    --   · simp_all only [Finset.mem_range, gt_iff_lt, pow_pos, mul_pos_iff_of_pos_left]
    --     rw [deriv_one_sub_X]
    --     simp only [nsmul_eq_mul, eval_mul, eval_natCast, eval_pow, eval_X]
    --     apply mul_pos
    --     · sorry
    --     · simp_all

lemma legendre_eval_symm {n : ℕ} {x : ℝ} (hx : 0 < x ∧ x < 1) : eval x (legendre n) =
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

end Polynomial

namespace Integral

noncomputable abbrev I (r s : ℕ) : ℝ :=
  - ∫ (x : ℝ) in (0)..1, (∫ (y : ℝ) in (0)..1, x ^ r * y ^ s / (1 - x * y))

noncomputable abbrev J (r s : ℕ) : ℝ :=
  - ∫ (x : ℝ) in (0)..1, (∫ (y : ℝ) in (0)..1, x ^ r * y ^ s * (x * y).log / (1 - x * y))

lemma zeta_3 : J 0 0 = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  sorry

lemma I_rr (h : 0 < r) : I r r = ∑' m : ℕ+ , 1 / ((m : ℝ) + r) ^ 3 := by
  sorry

lemma J_rr (r : ℕ) (h : 0 < r) :
    J r r = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 - 2 * ∑ m in Finset.range (r), 1 / ((m : ℝ) + 1) ^ 3 := by
  sorry

lemma I_rs (r s : ℕ) (h : r ≠ s) :
    I r s = ∑' m : ℕ , 1 / ((m : ℝ) + 1 + r) * 1 / ((m : ℝ) + 1 + s) := by
  sorry

lemma J_rs (r s : ℕ) (h : r ≠ s) :
    J r s = (∑ m in Finset.range (r), 1 / ((m : ℝ) + 1) ^ 2 - ∑ m in Finset.range (s), 1 / ((m : ℝ) + 1) ^ 2) / (r - s) := by
  sorry

end Integral

namespace Equality

lemma integral1 (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∫ (z : ℝ) in (0)..1, 1 / (1 - (1 - a) * z) = - a.log / (1 - a) := by
  rw[← sub_pos] at ha1
  have eq1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := 1 - a)
    (f := fun z ↦ (1 - z)⁻¹) (by positivity)
  have eq2 := intervalIntegral.mul_integral_comp_sub_mul (a := 0) (b := 1 - a) (f := fun x ↦ (x)⁻¹)
    (c := 1) (d := 1)
  have eq3 := integral_inv_of_pos (a := a) (b := 1) ha (by norm_num)
  simp only [mul_zero, mul_one, smul_eq_mul] at eq1
  simp only [one_div]
  rw [eq1, inv_mul_eq_div]
  field_simp
  simp only [one_div]
  simp only [one_mul, sub_sub_cancel, mul_zero, sub_zero] at eq2
  rw[eq2,eq3]
  simp

lemma integral_equality_help (s t: ℝ) (s0 : 0 < s) (s1 : s < 1) (t0 : 0 < t) (t1 : t < 1) :
    ∫ (u : ℝ) in (0)..1, 1 / ((1 - (1 - u) * s) * (1 - (1 - t) * u)) =
    ∫ (u : ℝ) in (0)..1, 1 / (1 - (1 - s) * t) * (s / (1 - (1 - u) * s) + (1 - t) / (1 - (1 - t) * u)) := by
  rw[← sub_pos] at s1
  obtain h1 := mul_lt_of_lt_one_right s1 t1
  have h2 : (1 - s) * t < 1 := by linarith
  have eq1 (u : ℝ) (hu : 0 < u) (hu1 : u < 1) : 1 / (1 - (1 - s) * t) * (s / (1 - (1 - u) * s) + (1 - t) / (1 - (1 - t) * u)) = 1 / ((1 - (1 - u) * s) * (1 - (1 - t) * u)) :=
    by
    have h4 : (1 - u) * s < 1 := by
      rw[← sub_pos] at hu1
      rw[sub_pos] at s1
      obtain h11 := mul_lt_of_lt_one_right hu1 s1
      linarith
    have h5 : (1 - t) * u < 1 := by
      rw[← sub_pos] at t1
      obtain h11 := mul_lt_of_lt_one_right t1 hu1
      linarith
    rw[div_add_div]
    · field_simp
      rw[div_eq_div_iff]
      · ring_nf
      · have _ : 0 < (1 - (1 - s) * t) * ((1 - (1 - u) * s) * (1 - (1 - t) * u)) := by
          rw[mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left] <;> linarith
        positivity
      · have _ : 0 < (1 - (1 - u) * s) * (1 - (1 - t) * u) := by
          rw[mul_pos_iff_of_pos_left] <;> linarith
        positivity
    · linarith
    · linarith
  rw[← intervalIntegral.integral_congr]
  intro a b
  simp
  rw[inv_eq_one_div, inv_eq_one_div, inv_eq_one_div, one_div_mul_one_div]
  simp at b
  rcases b with ⟨b1, b2⟩
  rw[← not_lt] at b1
  cases' eq_or_lt_of_not_lt b1 with b11 b12
  · rw[b11]
    field_simp
    rw[div_eq_one_iff_eq]
    ring_nf
    have _ : 0 < 1 - (1 - s) * t := by linarith
    positivity
  · rw[← not_lt] at b2
    cases' eq_or_lt_of_not_lt b2 with b21 b22
    · rw[← b21]
      field_simp
      rw[div_eq_one_iff_eq]
      ring_nf
      have _ : 0 < 1 - (1 - s) * t := by linarith
      positivity
    · obtain b00 := eq1 a b12 b22
      rw[b00, mul_comm]

lemma integral_equality (s t: ℝ) (s0 : 0 < s) (s1 : s < 1) (t0 : 0 < t) (t1 : t < 1) :
    ∫ (u : ℝ) in (0)..1, 1 /(1 - (1 - (1 - s) * t) * u) =
    ∫ (u : ℝ) in (0)..1, 1 /((1 - (1 - u) * s) * (1 - (1 - t) * u)) := by
  rw[← sub_pos] at s1
  obtain h1 := mul_lt_of_lt_one_right s1 t1
  have h2 : (1 - s) * t < 1 := by linarith
  have h3 := integral1 ((1 - s) * t) (Real.mul_pos s1 t0) h2
  have eq3 : ∫ (x : ℝ) in (0)..1, s / (1 - (1 - x) * s) = - (1 - s).log :=
    by
    have eq3_1 := intervalIntegral.integral_comp_sub_mul (a := 0) (b := 1) (c := 1) (d := 1) (f := fun z ↦ (s / (1 - z * s))) (by norm_num)
    have eq3_2 := intervalIntegral.integral_comp_add_mul (a := 0) (b := 1) (c := s) (d := 0) (f := fun z ↦ (1 / (1 - z))) (by positivity)
    have eq3_3 := intervalIntegral.mul_integral_comp_sub_mul (a := 0) (b := s) (f := fun x ↦ (x)⁻¹) (c := 1) (d := 1)
    have eq3_4 := integral_inv_of_pos (a := 1 - s) (b := 1) s1 (by norm_num)
    have comm1 := intervalIntegral.integral_comp_mul_right (a := 0) (b := 1) (c := s) (f := fun z ↦ s / (1 - z)) (by positivity)
    have comm2 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := s) (f := fun z ↦ s / (1 - z)) (by positivity)
    simp only [mul_zero, mul_one, smul_eq_mul] at eq3_1 eq3_2
    field_simp at eq3_1 eq3_2
    rw[mul_comm, ← intervalIntegral.integral_const_mul] at eq3_2
    simp only [mul_one_div, mul_comm] at eq3_2
    simp only [mul_zero, zero_mul, mul_one, one_mul, smul_eq_mul] at comm1 comm2
    rw[comm1, ← comm2, eq3_2] at eq3_1
    field_simp at eq3_3 eq3_4
    rw [eq3_3, eq3_4] at eq3_1
    rw[← Real.log_inv]
    field_simp
    exact eq3_1
  have eq4 : ∫ (x : ℝ) in (0)..1, (1 - t) / (1 - (1 - t) * x) = - t.log :=
    by
    rw[← sub_pos] at t1
    have eq4_1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := 1 - t) (f := fun z ↦ (1 - t) * (1 - z)⁻¹) (by positivity)
    have eq4_2 := intervalIntegral.mul_integral_comp_sub_mul (a := 0) (b := 1 - t) (f := fun x ↦ (x)⁻¹) (c := 1) (d := 1)
    have eq4_3 := integral_inv_of_pos (a := t) (b := 1) t0 (by norm_num)
    simp only [mul_zero, mul_one, smul_eq_mul] at eq4_1
    nth_rewrite 2 [intervalIntegral.integral_const_mul] at eq4_1
    rw[← mul_assoc] at eq4_1
    field_simp at eq4_1 eq4_2 eq4_3
    rw [eq4_2, eq4_3] at eq4_1
    rw[← Real.log_inv]
    field_simp
    exact eq4_1
  rw[integral_equality_help , intervalIntegral.integral_const_mul, h3, intervalIntegral.integral_add, eq3, eq4, ← neg_add, ← Real.log_mul]
  · field_simp
  · positivity
  · positivity
  · simp_rw [show ∀ (x : ℝ), s / (1 - (1 - x) * s) = s * 1 / (1 - (1 - x) * s) by intros; simp]
    apply IntervalIntegrable.continuousOn_mul (hg := continuousOn_const)
    apply intervalIntegral.intervalIntegrable_inv
    · intros x hx
      simp only [ge_iff_le, zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hx
      intro r
      rw [sub_eq_zero] at r
      have ineq3 : (1 - x) * s ≤ 1 * s := by
        apply mul_le_mul <;> linarith
      rw [one_mul] at ineq3
      linarith
    · apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul ?_ continuousOn_const
      apply ContinuousOn.sub continuousOn_const continuousOn_id
  · simp_rw [show ∀ (x : ℝ), (1 - t) / (1 - (1 - t) * x) = (1 - t) * 1 / (1 - (1 - t) * x) by simp]
    apply IntervalIntegrable.continuousOn_mul (hg := continuousOn_const)
    apply intervalIntegral.intervalIntegrable_inv
    · intro x hx
      simp at hx
      intro a
      rw [sub_eq_zero] at a
      have ineq : (1 - t) * x ≤ (1 - t) * 1 := by
        apply mul_le_mul <;> linarith
      rw [mul_one] at ineq
      linarith
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const continuousOn_id
  · exact s0
  · linarith
  · exact t0
  · exact t1



--- lemma n_derivative {a : ℝ} (n : ℕ) : derivative^[n + 1] (1 / (1 - a * X)) = (n + 1) ! * (a ^ (n + 1)) / (1 - a * X) ^ (n + 2) := by
---  rw [show n + 2 = (n + 1) + 1 by omega]
---  induction' n + 1 with n hn
---  · simp only [Nat.zero_eq, one_div, Function.iterate_zero, id_eq, Nat.factorial_zero,
---    Nat.cast_one, pow_zero, mul_one, zero_add, pow_one]
---  · rw[Function.iterate_succ_apply', hn]

end Equality

namespace Bound

lemma max_value {x : ℝ} (x0 : 0 < x) (x1 : x < 1) : √x * √(1 - x) ≤ ((1 / 2) : ℝ) := by
  rw [← Real.sqrt_mul, le_div_iff', ← show √4 = 2 by rw [Real.sqrt_eq_iff_sq_eq] <;> linarith,
    ← Real.sqrt_mul, Real.sqrt_le_one, show 4 * (x * (1 - x)) = 1 - (2 * x - 1)^2 by ring] <;>
  linarith [mul_self_nonneg (2 * x - 1)]

lemma nonneg {x : ℝ} (_ : 0 < x) (_ : x < 1) : (0 : ℝ) ≤ √x * √(1 -x) :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma bound_aux (x z : ℝ) (x0 : 0 < x) (x1 : x < 1) (z0 : 0 < z) (z1 : z < 1) :
    2 * √(1 - x) * √(x * z) ≤ 1 - (1 - z) * x := by
  rw [← sub_pos] at x1 z1
  have := mul_pos x0 z0
  rw [show 1 - (1 - z) * x = 1 - x + x * z by ring]
  calc
    _ ≤ (√(1 - x) - √(x * z)) * (√(1 - x) - √(x * z)) + 2 * √(1 - x) * √(x * z) :=
      by linarith [mul_self_nonneg (√(1 - x) - √(x * z))]
    _ = √(1 - x) * √(1 - x) + √(x * z) * √(x * z) := by ring
    _ = 1 - x + x * z := by rw [Real.mul_self_sqrt, Real.mul_self_sqrt] <;> linarith

lemma bound (x y z : ℝ) (x0 : 0 < x) (x1 : x < 1) (y0 : 0 < y) (y1 : y < 1) (z0 : 0 < z) (z1 : z < 1) :
    x * (1 -x) * y * (1 - y) * z * (1 - z) / ((1 - (1 - z) * x) * (1 - y * z)) < (1 / 30 : ℝ) := by
  have := mul_pos x0 z0
  have h1 : 2 * √(1 - x) * √(x * z) ≤ 1 - (1 - z) * x := by apply bound_aux <;> assumption
  have h2 : 2 * √(1 - y) * √((1 - z) * y) ≤ 1 - y * z := by
    convert bound_aux y (1 - z) y0 y1 (by linarith) (by linarith) using 2
    · rw [mul_comm]
    · ring
  rw [← sub_pos] at x1 y1 z1
  have : y * z < 1 := by apply mul_lt_of_lt_one_of_lt_of_pos <;> linarith
  have : 0 < √(1 - x) := Real.sqrt_pos_of_pos x1
  have : 0 < √(x * z) := Real.sqrt_pos_of_pos (by linarith)
  have : 0 < 1 - y * z := by linarith
  have : 0 ≤ x.sqrt * (1 - x).sqrt := nonneg (by assumption) (by linarith)
  have : 0 ≤ y.sqrt * (1 - y).sqrt := nonneg (by assumption) (by linarith)
  calc
    _ ≤ x * (1 -x) * y * (1 - y) * z * (1 - z) / (2 * √(1 - x) * √(x * z) * (1 - y * z)) := by
      refine div_le_div (by positivity) (le_refl _) (by positivity) ?_
      rwa [mul_le_mul_iff_of_pos_right]
      linarith
    _ ≤ x * (1 -x) * y * (1 - y) * z * (1 - z) / (2 * √(1 - x) * √(x * z) * 2 * √(1 - y) * √((1 - z) * y)) := by
      refine div_le_div (by positivity) (le_refl _) (by positivity) ?_
      rw [mul_assoc, mul_assoc]
      rw [mul_assoc] at h2
      exact mul_le_mul_of_nonneg_left h2 (le_of_lt <| by positivity)
    _ = √x * √(1 -x) * (√y * √(1 - y)) * (√z * √(1 - z)) / 4 := by
        rw [Real.sqrt_mul, Real.sqrt_mul]
        calc _
          _ = ((x * (1 - x)) * (y * (1 - y)) * (z * (1 - z))) / (4 * (√x * √(1 - x)) * (√y * √(1 - y)) * (√z * √(1 - z))) := by ring
          _ = (x / √x) * ((1 - x) / √(1 - x)) * (y / √y) * ((1 - y) / √(1 -y)) * (z / √z) * ((1 - z) / √(1 - z)) / 4 := by ring
          _ = _ := by simpa only [Real.div_sqrt] using (by ring)
        all_goals linarith
    _ ≤ (1 / 2) * (1 / 2) * (1 / 2) / 4 := by
      refine div_le_div (by norm_num)
        (mul_le_mul_of_le_of_le (mul_le_mul_of_le_of_le (max_value ?_ ?_) (max_value ?_ ?_) ?_ ?_)
          (max_value ?_ ?_) (mul_nonneg ?_ ?_) ?_) (by norm_num) (by norm_num) <;>
      linarith
    _ < (1 / 30 : ℝ) := by norm_num

end Bound

open Polynomial Integral Equality Bound

noncomputable abbrev JJ (n : ℕ) : ℝ :=
  - ∫ (x : ℝ) in (0)..1, (∫ (y : ℝ) in (0)..1,
    (legendre n).eval x * (legendre n).eval y * (x * y).log / (1 - x * y))

noncomputable abbrev fun1 (n : ℕ) : ℝ := (d (Finset.Icc 1 n)) ^ 3 * JJ n

lemma mul_lt_one_aux {x y : ℝ} (hx : x ∈ Set.Ioo 0 1) (hy : y ∈ Set.Ioo 0 1) : x * y < 1 := by
  simp_all only [Set.mem_Ioo]
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨_, hy2⟩ := hy
  calc x * y < x := by exact mul_lt_of_lt_one_right hx1 hy2
    _ < 1 := by exact hx2

lemma JJ_pos (n : ℕ) : 0 < JJ n := by
  simp only [JJ]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · apply IntervalIntegrable.neg
    sorry
  · intro x hx
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · apply IntervalIntegrable.neg
      apply IntervalIntegrable.continuousOn_mul
      · apply intervalIntegral.intervalIntegrable_inv
        · intro y hy
          have : x * y < 1 := by
            obtain ⟨hx1, hx2⟩ := hx
            simp_all only [ge_iff_le, zero_le_one, Set.uIcc_of_le, Set.mem_Icc]
            obtain ⟨hy1, hy2⟩ := hy
            calc x * y ≤ x := by rwa [mul_le_iff_le_one_right hx1]
              _ < 1 := by exact hx2
          linarith
        · apply ContinuousOn.sub continuousOn_const
          apply ContinuousOn.mul continuousOn_const continuousOn_id
      · apply ContinuousOn.mul
        · sorry
        · sorry
    · intro y hy
      simp only [Left.neg_pos_iff]
      apply mul_neg_of_neg_of_pos
      · apply mul_neg_of_pos_of_neg
        · simp only [Set.mem_Ioo] at hx hy
          exact mul_pos (legendre_pos hx) (legendre_pos hy)
        · refine Real.log_neg ?_ (mul_lt_one_aux hx hy)
          simp_all
      · rw [inv_pos, sub_pos]
        exact mul_lt_one_aux hx hy
    · norm_num
  · norm_num

lemma linear_int (n : ℕ) : ∃ a b : ℕ → ℤ,
    fun1 n = a n + b n * (d (Finset.Icc 1 n)) ^ 3  * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  sorry

lemma JJ_upper (n : ℕ) : JJ n < 2 * (1 / 30) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  simp only [JJ]
  sorry

lemma fun1_tendsto_zero : Filter.Tendsto (fun n ↦ fun1 n) ⊤ (nhds 0) := by
  sorry

lemma fin_d_neq_zero (n : ℕ) : d (Finset.Icc 1 n) > 0 := by
  suffices d (Finset.Icc 1 n) ≠ 0 by omega
  apply d_ne_zero
  simp only [Finset.mem_Icc, nonpos_iff_eq_zero, one_ne_zero, zero_le, and_true, not_false_eq_true]

theorem zeta_3_irratoinal : ¬ ∃ r : ℚ , (r : ℝ) = ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  by_contra! r
  cases' r with r hr
  let q := r.den
  let hq := Rat.den_nz r
  have prop1 := Filter.Tendsto.mul_const (b := (q : ℝ)) (fun1_tendsto_zero)
  rw [zero_mul] at prop1
  have prop2 : ∀ n : ℕ, fun1 n * q ≥ 1 := by
    intro n
    obtain ⟨a, b, h⟩ := linear_int n
    have : fun1 n * q > 0 := by
      delta fun1
      rw [mul_comm, ← mul_assoc]
      refine mul_pos ?_ (JJ_pos n)
      norm_cast
      simp only [CanonicallyOrderedCommSemiring.mul_pos]
      exact ⟨by omega, pow_pos (fin_d_neq_zero n) 3⟩
    rw [h, add_mul, mul_assoc, ← hr] at this ⊢
    simp only [ge_iff_le, q] at this ⊢
    norm_cast at this ⊢
    rw [Rat.mul_den_eq_num] at this ⊢
    norm_cast at this ⊢
  rw [Filter.tendsto_iff_forall_eventually_mem] at prop1
  specialize prop1 (Set.Ico (-1/2) (1/2))
  simp only [one_div, Ico_mem_nhds_iff, Set.mem_Ioo, inv_pos, Nat.ofNat_pos, and_true, Set.mem_Ico,
    Filter.eventually_top] at prop1
  rw [← one_div] at prop1
  have prop : (-1/2 : ℝ) < 0 := by
    rw [div_neg_iff]; right
    simp only [Left.neg_neg_iff, zero_lt_one, Nat.ofNat_pos, and_self]
  specialize prop2 0
  cases' ((prop1 prop) 0) with h1 h2
  linarith
