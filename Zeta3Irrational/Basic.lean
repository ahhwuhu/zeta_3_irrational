import Mathlib

open scoped Nat
open BigOperators

namespace Polynomial

noncomputable abbrev legendre (n : ℕ) : ℝ[X] :=
  C (1 / n ! : ℝ) * derivative^[n] (X ^ n * (1 - X) ^ n)


lemma sub_pow{R : Type u_1} [CommRing R] (x : R) (y : R) (n : ℕ) :
    (x - y) ^ n = (Finset.range (n + 1)).sum fun (m : ℕ) => (n.choose m) • x ^ m * (- 1) ^ (n - m) * y ^ (n - m) := by
    rw[← Mathlib.Tactic.RingNF.add_neg, add_pow]
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
    rw[neg_pow, pow_two, mul_pow,← mul_assoc, mul_comm, mul_assoc, pow_mul_pow_sub, mul_assoc,← pow_add, ← mul_assoc, nsmul_eq_mul, add_comm]
    rw[Finset.mem_range] at hm
    linarith

lemma Finsum_iterate_deriv {R : Type u_1} [CommRing R] {k : ℕ} {h : ℕ → ℕ} :
    derivative^[k] (∑ m in Finset.range (k + 1), (h m) • ((- 1) ^ m : R[X]) * X ^ (k + m)) = ∑ m in Finset.range (k + 1), (h m) • (- 1) ^ m * derivative^[k] (X ^ (k + m)) := by
    induction' k + 1 with n hn
    · simp only [Nat.zero_eq, Finset.range_zero, Finset.sum_empty, iterate_map_zero]
    · rw[Finset.sum_range, Finset.sum_range, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at *
      simp only [Fin.coe_castSucc, Fin.val_last, iterate_map_add, hn, add_right_inj]
      rw [nsmul_eq_mul, mul_assoc, ← nsmul_eq_mul, Polynomial.iterate_derivative_smul]
      sorry

lemma legendre_eq_sum (n : ℕ) :
    legendre n =
      ∑ k in Finset.range (n + 1),
        C ((- 1) ^ k : ℝ) • (Nat.choose n k) • (Nat.choose (n + k) n) * X ^ k := by
      rw[legendre]
      induction' n with n hn
      · simp
      · rw [Nat.succ_eq_add_one, show n + 1 + 1 = n + 2 by ring, ← mul_pow, mul_one_sub, ← pow_two, sub_pow_special, Finsum_iterate_deriv, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [← mul_assoc, Polynomial.iterate_derivative_X_pow_eq_smul, Nat.descFactorial_eq_div (show n + 1 ≤ n + 1 + x by omega), show n + 1 + x - (n + 1) = x by omega, smul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc, ← mul_assoc]
        sorry



end Polynomial

namespace Integral

noncomputable abbrev I (r s : ℕ) : ℝ := - ∫ (x : ℝ) in (0)..1, (∫ (y : ℝ) in (0)..1, x ^ r * y ^ s / (1 - x * y))

noncomputable abbrev J (r s : ℕ) : ℝ := - ∫ (x : ℝ) in (0)..1, (∫ (y : ℝ) in (0)..1, x ^ r * y ^ s * (x * y).log / (1 - x * y))

lemma zeta_3 : J 0 0 = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  sorry

lemma I_rr (h : 0 < r) : I r r = ∑' m : ℕ+ , 1 / ((m : ℝ) + r) ^ 3 := by
  sorry

lemma J_rr (r : ℕ) (h : 0 < r) : J r r= 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 - 2 * ∑ m in Finset.range (r), 1 / ((m : ℝ) + 1) ^ 3 := by
  sorry

lemma I_rs (r s : ℕ) (h : r ≠ s) : I r s = ∑' m : ℕ , 1 / ((m : ℝ) + 1 + r) * 1 / ((m : ℝ) + 1 + s) := by
  sorry

lemma J_rs (r s : ℕ) (h : r ≠ s) : J r s = (∑ m in Finset.range (r), 1 / ((m : ℝ) + 1) ^ 2 - ∑ m in Finset.range (s), 1 / ((m : ℝ) + 1) ^ 2) / (r - s) := by
  sorry

end Integral

namespace Equality

lemma integral1 (a : ℝ) (ha : 0 < a) (ha1 : a < 1) : ∫ (z : ℝ) in (0)..1, 1 / (1 - (1 - a) * z) = - a.log / (1 - a) := by
  rw[← sub_pos] at ha1
  have eq1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := 1 - a) (f := fun z ↦ (1 - z)⁻¹) (by positivity)
  have eq2 := intervalIntegral.mul_integral_comp_sub_mul (a := 0) (b := 1 - a) (f := fun x ↦ (x)⁻¹) (c := 1) (d := 1)
  have eq3 := integral_inv_of_pos (a := a) (b := 1) ha (by norm_num)
  simp only [mul_zero, mul_one, smul_eq_mul] at eq1
  simp only [one_div]
  rw [eq1, inv_mul_eq_div]
  field_simp
  simp only [one_div]
  simp only [one_mul, sub_sub_cancel, mul_zero, sub_zero] at eq2
  rw[eq2,eq3]
  simp

lemma integral_equality_help (s t: ℝ) (s0 : 0 < s) (s1 : s < 1) (t0 : 0 < t) (t1 : t < 1) : ∫ (u : ℝ) in (0)..1, 1 / ((1 - (1 - u) * s) * (1 - (1 - t) * u)) = ∫ (u : ℝ) in (0)..1, 1 / (1 - (1 - s) * t) * (s / (1 - (1 - u) * s) + (1 - t) / (1 - (1 - t) * u)) :=
      by
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
    ∫ (u : ℝ) in (0)..1, 1 /(1 - (1 - (1 - s) * t) * u) = ∫ (u : ℝ) in (0)..1, 1 /((1 - (1 - u) * s) * (1 - (1 - t) * u)) :=
    by
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
        (mul_le_mul_of_le_of_le (mul_le_mul_of_le_of_le (max_value ?_ ?_) (max_value ?_ ?_) ?_ ?_) (max_value ?_ ?_)
          (mul_nonneg ?_ ?_) ?_) (by norm_num) (by norm_num) <;>
      linarith
    _ < (1 / 30 : ℝ) := by norm_num

end Bound

open Polynomial Integral Equality Bound

noncomputable abbrev JJ (n : ℕ) : ℝ := - ∫ (x : ℝ) in (0)..1, (∫ (y : ℝ) in (0)..1, (legendre n).eval x * (legendre n).eval y * (x * y).log / (1 - x * y))

def d (s : Finset ℕ) : ℕ := s.lcm id

lemma JJ_pos (n : ℕ) : 0 < JJ n := by
  sorry

lemma JJ_int (n : ℕ) {a b: ℕ → ℤ} : JJ n * (d (Finset.range (n))) ^ 3 = a n + b n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 * (d (Finset.range (n))) ^ 3 := by
  sorry

lemma JJ_upper (n : ℕ) : JJ n < 2 * (1 / 30) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  sorry

def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

theorem zeta_3_irratoinal : ¬ ∃ r : ℚ , (r : ℝ) = ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  by_contra! r
  cases' r with r hr
  let p := r.num
  let q := r.den
  let hq := Rat.den_nz r
  let fun1 := fun n => JJ n
  have JJ_inf {n : ℕ} (hn : n > 0) : 0 < JJ n * (d (Finset.range (n))) ^ 3 * q := by
    rw[mul_assoc]
    apply mul_pos (JJ_pos n)
    exact
  sorry
