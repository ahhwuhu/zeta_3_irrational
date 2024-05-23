import Mathlib.Tactic
import Mathlib.Analysis.MeanInequalities
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.Data.Nat.Choose.Basic
import Mathlib
import Mathlib.Data.Real.Sqrt
import Init.Data.Nat.Basic
import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.SpecialFunctions.Log.Basic


open scoped Nat
open BigOperators

namespace Polynomial

noncomputable def legendre (n : ℕ) : ℝ[X] :=
  C (1 / n ! : ℝ) * derivative^[n] (X ^ n * (1 - X) ^ n)

noncomputable def legendre' (n : ℕ) : ℝ[X] :=
  ∑ k in Finset.range (n + 1), C ((- 1) ^ k : ℝ) * (Nat.choose n k) • (Nat.choose (n + k) n) • X ^ k

end Polynomial

/-
lemma J_00 : - ∫ x in 0..1, ∫ y in 0..1 , ln (x * y) / (1 - x * y) dy dx =  2 * ∑' i : ℕ , 1 / (n + 1) ^ 3  := by
  sorry
-/

lemma zeta_3 : - ∫ (x : ℝ) in (0)..1, (∫ (y : ℝ) in (0)..1, (x * y).log / (1 - x * y)) = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  sorry

lemma I_rr (r : ℕ) (h : 0 < r) : - ∫ (x : ℝ) in (0)..1, (∫ (y : ℝ) in (0)..1, x ^ r * y ^ r / (1 - x * y)) = ∑' m : ℕ+ , 1 / ((m : ℝ) + r) ^ 3 := by
  sorry

lemma J_rr (r : ℕ) (h : 0 < r) : - ∫ (x : ℝ) in (0)..1, (∫ (y : ℝ) in (0)..1, x ^ r * y ^ r * (x * y).log / (1 - x * y)) = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 - 2 * ∑ m in Finset.range (r), 1 / ((m : ℝ) + 1) ^ 3 := by
  sorry

lemma I_rs (r s : ℕ) (h : r ≠ s) : - ∫ (x : ℝ) in (0)..1, (∫ (y : ℝ) in (0)..1, x ^ r * y ^ s / (1 - x * y)) = ∑' m : ℕ , 1 / ((m : ℝ) + 1 + r) * 1 / ((m : ℝ) + 1 + s) := by
  sorry

lemma J_rs (r s : ℕ) (h : r ≠ s) : - ∫ (x : ℝ) in (0)..1, (∫ (y : ℝ) in (0)..1, x ^ r * y ^ s * (x * y).log / (1 - x * y)) = (∑ m in Finset.range (r), 1 / ((m : ℝ) + 1) ^ 2 - ∑ m in Finset.range (s), 1 / ((m : ℝ) + 1) ^ 2) / (r - s) := by
  sorry

lemma integral1 (a : ℝ) (ha : 0 < a) (ha1 : a < 1) : ∫ (z : ℝ) in (0)..1, 1 / (1 - (1 - a) * z) = - a.log / (1 - a) := by
  rw[← sub_pos] at ha1
  have eq1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := 1 - a)
    (f := fun z ↦ (1 - z)⁻¹) (by positivity)
  simp only [mul_zero, mul_one, smul_eq_mul] at eq1
  simp
  rw [eq1, inv_mul_eq_div]
  field_simp
  simp
  have eq2 := intervalIntegral.mul_integral_comp_sub_mul (a := 0) (b := 1 - a) (f := fun x ↦ (x)⁻¹) (c := 1) (d := 1)
  simp at eq2
  rw[eq2]
  have eq3 := integral_inv_of_pos (a := a) (b := 1) ha (by norm_num) 
  rw[eq3]
  simp

lemma integral_equality (s t : ℝ) (s0 : 0 < s) (s1 : s < 1) (t0 : 0 < t) (t1 : t < 1) :
     ∫ (u : ℝ) in (0)..1, 1 /(1 - (1 - (1 - s) * t) * u) = ∫ (u : ℝ) in (0)..1, 1 /((1 - (1 - u) * s) * (1 - (1 - t) * u)) := by
    sorry
    
  



lemma n_derivative {a : ℝ} (n : ℕ) : derivative^[n + 1] (1 / (1 - a * X)) = (n + 1) ! * (a ^ (n + 1)) / (1 - a * X) ^ (n + 2) := by
  sorry



lemma max_value {x : ℝ} (x0 : 0 < x) (x1 : x < 1) : √x * √(1 - x) ≤ ((1 / 2) : ℝ) := by
  rw [← Real.sqrt_mul, le_div_iff', ← show √4 = 2 by rw [Real.sqrt_eq_iff_sq_eq] <;> linarith,
    ← Real.sqrt_mul, Real.sqrt_le_one, show 4 * (x * (1 - x)) = 1 - (2 * x - 1)^2 by ring] <;>
  linarith [mul_self_nonneg (2 * x - 1)]

lemma nonneg {x : ℝ} (_ : 0 < x) (_ : x < 1) : (0 : ℝ) ≤ √x * √(1 -x) :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma bound (x y z : ℝ) (x0 : 0 < x) (x1 : x < 1) (y0 : 0 < y) (y1 : y < 1) (z0 : 0 < z) (z1 : z < 1) : x * (1 -x) * y * (1 - y) * z * (1 - z) / ((1 - (1 - z) * x) * (1 - y * z)) < (1 / 30 : ℝ) := by
  have h1 : 2 * √(1 - x) * √(x * z) ≤ 1 - (1 - z) * x := by
    have a : 1 - (1 - z) * x = 1 - x + x * z := by ring_nf
    rw[a]
    rw[← sub_pos] at x1
    let p := √(1 - x) - √(x * z)
    calc
      2 * √(1 - x) * √(x * z) ≤ p * p + 2 * √(1 - x) * √(x * z) := by linarith [mul_self_nonneg p]
      _ ≤ (√(1 - x) - √(x * z)) * (√(1 - x) - √(x * z)) + 2 * √(1 - x) * √(x * z) := by simp [p]
      _ = √(1 - x) * √(1 - x) + √(x * z) * √(x * z) := by ring_nf
      _ = 1 - x + √(x * z) * √(x * z) := by
        obtain _ := LT.lt.le x1
        rwa[Real.mul_self_sqrt]
      _ = 1 - x + x * z := by
        obtain _ := LT.lt.le (Right.mul_pos x0 z0)
        rwa[Real.mul_self_sqrt]
  have h2 : 2 * √(1 - y) * √((1 - z) * y) ≤ 1 - y * z := by
    have b : 1 - y * z  = 1 - y + (1 - z) * y:= by ring_nf
    rw[b]
    rw[← sub_pos] at y1 z1
    let p := √(1 - y) - √((1 - z) * y)
    calc
      2 * √(1 - y) * √((1 - z) * y) ≤ p * p + 2 * √(1 - y) * √((1 - z) * y) := by linarith [mul_self_nonneg p]
      _ ≤ (√(1 - y) - √((1 - z) * y)) * (√(1 - y) - √((1 - z) * y)) + 2 * √(1 - y) * √((1 - z) * y) := by simp [p]
      _ = √(1 - y) * √(1 - y) + √((1 - z) * y) * √((1 - z) * y) := by ring_nf
      _ = 1 - y + √((1 - z) * y) * √((1 - z) * y) := by
        obtain _ := LT.lt.le y1
        rwa[Real.mul_self_sqrt]
      _ = 1 - y + (1 - z) * y := by
        obtain _ := LT.lt.le (Right.mul_pos z1 y0)
        rwa[Real.mul_self_sqrt]
  calc
    x * (1 -x) * y * (1 - y) * z * (1 - z) / ((1 - (1 - z) * x) * (1 - y * z)) ≤ x * (1 -x) * y * (1 - y) * z * (1 - z) / (2 * √(1 - x) * √(x * z) * (1 - y * z)) := by
      apply div_le_div
      · rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_nonneg_iff_of_pos_left, mul_nonneg_iff_of_pos_left, mul_nonneg_iff_of_pos_left, mul_nonneg_iff_of_pos_left, mul_nonneg_iff_of_pos_left]
        rw[← sub_pos] at z1
        exact LT.lt.le z1
        exact z0
        rw[← sub_pos] at y1
        exact y1
        exact y0
        rw[← sub_pos] at x1
        exact x1
        exact x0
      · rfl
      · rw [mul_assoc, mul_assoc]
        apply Real.mul_pos
        norm_num
        apply Real.mul_pos
        rw[← sub_pos] at x1
        rwa[Real.sqrt_pos]
        apply Real.mul_pos
        rw[Real.sqrt_mul']
        apply Real.mul_pos
        rwa[Real.sqrt_pos]
        rwa[Real.sqrt_pos]
        exact LT.lt.le z0
        obtain g := mul_lt_of_lt_one_right y0 z1
        rw[sub_pos]
        exact lt_trans g y1
      · obtain g := lt_trans (mul_lt_of_lt_one_right y0 z1) y1
        rw[← sub_pos] at g
        rwa[mul_le_mul_iff_of_pos_right]
        exact g
    _ ≤ x * (1 -x) * y * (1 - y) * z * (1 - z) / (2 * √(1 - x) * √(x * z) * 2 * √(1 - y) * √((1 - z) * y)) := by
      apply div_le_div
      · rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_nonneg_iff_of_pos_left, mul_nonneg_iff_of_pos_left, mul_nonneg_iff_of_pos_left, mul_nonneg_iff_of_pos_left, mul_nonneg_iff_of_pos_left]
        rw[← sub_pos] at z1
        exact LT.lt.le z1
        exact z0
        rw[← sub_pos] at y1
        exact y1
        exact y0
        rw[← sub_pos] at x1
        exact x1
        exact x0
      · rfl
      · rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc]
        apply Real.mul_pos
        norm_num
        apply Real.mul_pos
        rw[← sub_pos] at x1
        rwa[Real.sqrt_pos]
        apply Real.mul_pos
        rw[Real.sqrt_mul']
        apply Real.mul_pos
        rwa[Real.sqrt_pos]
        rwa[Real.sqrt_pos]
        exact LT.lt.le z0
        apply Real.mul_pos
        norm_num
        apply Real.mul_pos
        rw[← sub_pos] at y1
        rwa[Real.sqrt_pos]
        rw[Real.sqrt_mul']
        apply Real.mul_pos
        rw[← sub_pos] at z1
        rwa[Real.sqrt_pos]
        rwa[Real.sqrt_pos]
        exact LT.lt.le y0
      · have g : 2 * √(1 - x) * √(x * z) > 0 := by
          rw[mul_assoc]
          apply Real.mul_pos
          norm_num
          apply Real.mul_pos
          rw[← sub_pos] at x1
          rwa[Real.sqrt_pos]
          rw[Real.sqrt_mul']
          apply Real.mul_pos
          rwa[Real.sqrt_pos]
          rwa[Real.sqrt_pos]
          exact LT.lt.le z0
        rw [mul_assoc, mul_assoc]
        rw [mul_assoc] at h2
        exact mul_le_mul_of_nonneg_left h2 (LT.lt.le g)
    _ = √x * √(1 -x) * √y * √(1 - y) * √z * √(1 - z) / 4 := by
        field_simp
        rw[← sub_pos] at x1
        rw[← sub_pos] at y1
        rw[← sub_pos] at z1
        rw [show x * (1 - x) * y * (1 - y) * z * (1 - z) * 4 = 4 * ((x * (1 - x)) * (y * (1 - y)) * (z * (1 - z))) by ring]
        rw [show (2 * (1 - x).sqrt * (x.sqrt * z.sqrt) * 2 * (1 - y).sqrt * ((1 - z).sqrt * y.sqrt)) =
          4 * ((√x * √(1 - x)) * (√y * √(1 - y)) * (√z * √(1 - z))) by ring]
        calc _
          _ = ((x * (1 - x)) * (y * (1 - y)) * (z * (1 - z))) / ((√x * √(1 - x)) * (√y * √(1 - y)) * (√z * √(1 - z))) := by ring
          _ = (x / √x) * ((1 - x) / √(1 - x)) * (y / √y) * ((1 - y) / √(1 -y)) * (z / √z) * ((1 - z) / √(1 - z)) := by ring
          _ = √x * √(1 - x) * √y * √(1 -y) * √z * √(1 - z) := by
            simp only [Real.div_sqrt]
    _ ≤ (1 / 2) * (1 / 2) * (1 / 2) / 4 := by
      apply div_le_div
      · norm_num
      · have d0 : 0 ≤ (1 / 2 : ℝ) := by norm_num
        have d1 : 0 ≤ (1 / 2 : ℝ) * (1 / 2) := by norm_num
        obtain d2 := mul_le_mul_of_le_of_le (max_value x0 x1) (mul_le_mul_of_le_of_le (max_value y0 y1) (max_value z0 z1) (nonneg y0 y1) d0) (nonneg x0 x1) d1
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc] at d2
        field_simp at *
        ring_nf at *
        exact d2
      · norm_num
      · norm_num
    _ < (1 / 30 : ℝ) := by norm_num

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

lemma bound1 (x y z : ℝ) (x0 : 0 < x) (x1 : x < 1) (y0 : 0 < y) (y1 : y < 1) (z0 : 0 < z) (z1 : z < 1) :
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


theorem zeta_3_irratoinal : ¬ ∃ q : ℚ , q = ∑' n : ℕ , 1 / ((n : ℚ) + 1) ^ 3:= by
  sorry

