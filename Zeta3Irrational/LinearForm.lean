import Mathlib
import Zeta3Irrational.d
import Zeta3Irrational.Integral
import Zeta3Irrational.Equality
import Zeta3Irrational.LegendrePoly
import Zeta3Irrational.Bound

open scoped Nat
open BigOperators

lemma d_cube_ne_zero {r : ℕ} : ((d (Finset.Icc 1 r) ^ 3) : ℝ) ≠ (0 : ℝ) := by
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero]
  apply d_ne_zero; simp

lemma J_rr_linear (r : ℕ) :
    ∃ a : ℤ, J r r = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 - a / (d (Finset.Icc 1 r)) ^ 3 := by
  if h : r = 0 then
    rw [h, zeta_3]; use 0; simp
  else
    rw [J_rr (by omega)]
    simp only [sub_right_inj]
    simp_rw [eq_div_iff d_cube_ne_zero, Finset.mul_sum, Finset.sum_mul]
    use ∑ i ∈ Finset.Icc 1 r, 2 * ↑(d (Finset.Icc 1 r)) ^ 3 / ↑i ^ 3
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro x hx
    rw [mul_assoc]
    nth_rewrite 2 [mul_comm]
    rw [mul_one_div, Int.cast_div]
    · simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_natCast, mul_div_assoc']
    · rw [← Nat.cast_pow, ← Nat.cast_pow, d_cube', Nat.cast_pow]
      apply Dvd.dvd.mul_left
      norm_cast
      apply dvd_d_of_mem
      simp_all
    · simp_all only [Finset.mem_Icc, Int.cast_pow, Int.cast_natCast, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero]
      linarith

lemma Icc_diff_Icc {r s : ℕ} (h : r > s) (g : ¬s = 0) : Finset.Icc 1 r \ Finset.Icc 1 s = Finset.Icc (s + 1) r := by
  ext x
  constructor
  · intro hx
    simp_all only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_Icc, not_and, not_le, and_true]
    exact LT.lt.nat_succ_le (hx.2 hx.1.1)
  · intro hx
    simp_all only [gt_iff_lt, Finset.mem_Icc, Finset.mem_sdiff, and_true, not_and, not_le]
    constructor
    · linarith
    · intro
      linarith

lemma one_div_sum_eq {r s : ℕ} (h : r > s) :
    ∑ m ∈ Finset.Icc 1 r, (1 / m ^ 2 : ℝ) - ∑ m ∈ Finset.Icc 1 s, (1 / m ^ 2 : ℝ) =
    ∑ m ∈ Finset.Icc 1 (r - s), (1 / (s + m) ^ 2 : ℝ) := by
  rw [← Finset.sum_sdiff_eq_sub]
  · if h1 : s = 0 then
      simp_all
    else
      simp_rw [← Nat.cast_add]
      rw [Icc_diff_Icc h h1, ← Nat.Ico_succ_right, ← Nat.Ico_succ_right,
        Finset.sum_Ico_add (f := fun (x : ℕ) => 1 / ((x ^ 2) : ℝ)) (c := s), Nat.succ_eq_add_one,
        Nat.succ_eq_add_one, add_comm, show r - s + 1 + s = r + 1 by omega]
  · exact Finset.Icc_subset_Icc_right (LT.lt.le (gt_iff_lt.1 h))

lemma J_rs_linear {r s : ℕ} (h : r > s) : ∃ a : ℤ, J r s = a / (d (Finset.Icc 1 r)) ^ 3 := by
  rw [J_rs (by linarith)]
  simp_rw [eq_div_iff d_cube_ne_zero, one_div_sum_eq h]
  use (∑ m ∈ Finset.Icc 1 (r - s), (d (Finset.Icc 1 r)) ^ 2 / (s + m) ^ 2 *
    (d (Finset.Icc 1 r)) / (r - s))
  rw [Finset.sum_div, Finset.sum_mul, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show 3 = 1 + 2 by omega, pow_add, pow_one, mul_comm, mul_assoc, mul_div_assoc', mul_one_div,
    mul_div_assoc', mul_comm, ← mul_div_assoc', Int.cast_div]
  · rw [Int.cast_mul, Int.cast_div]
    · simp_all only [gt_iff_lt, Finset.mem_Icc, Int.cast_pow, Int.cast_natCast, Int.cast_add,
      Int.cast_sub]
      rw [mul_div_assoc']
    · norm_cast
      rw [d_sq']
      apply dvd_d_of_mem
      simp_all only [gt_iff_lt, Finset.mem_Icc, Finset.mem_image, ge_iff_le, zero_le, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj, exists_eq_right]
      omega
    · simp_all only [gt_iff_lt, Finset.mem_Icc, Int.cast_pow, Int.cast_add, Int.cast_natCast,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
      rw [← Nat.cast_add]
      norm_cast; omega
  · apply Dvd.dvd.mul_left
    rw [← Nat.cast_sub (by linarith)]
    norm_cast
    apply dvd_d_of_mem
    simp_all only [gt_iff_lt, Finset.mem_Icc, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le,
      and_true]
    linarith
  · simp_all only [gt_iff_lt, Finset.mem_Icc, Int.cast_sub, Int.cast_natCast]
    rw [← Nat.cast_sub (by linarith)]
    norm_cast; linarith

lemma multi_integral_sum_comm (c : ℕ → ℤ) : ∫ (x : ℝ) (y : ℝ) in (0)..1, ∑ x_1 ∈ Finset.range (n + 1),
    ∑ x_2 ∈ Finset.range (n + 1), ↑(c x_1) * x ^ x_1 * ↑(c x_2) * y ^ x_2 * (x * y).log / (1 - x * y)
    = ∑ x_1 ∈ Finset.range (n + 1), ∑ x_2 ∈ Finset.range (n + 1), ∫ (x : ℝ) (y : ℝ) in (0)..1,
    ↑(c x_1) * x ^ x_1 * ↑(c x_2) * y ^ x_2 * (x * y).log / (1 - x * y) := by
  sorry

lemma multi_integral_mul_const (c d : ℕ) (p q : ℝ): ∫ (x : ℝ) (y : ℝ) in (0)..1,
    p * x ^ c * q * y ^ d * (x * y).log / (1 - x * y) = p * q * - J c d := by
  simp_rw [mul_div_assoc, J, neg_neg]
  rw [← intervalIntegral.integral_const_mul]
  simp_rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  apply intervalIntegral.integral_congr
  intro y _
  ring

noncomputable def p (r s : ℕ) : ℤ :=
  if h : r > s then (J_rs_linear h).choose
  else if h : r < s then (J_rs_linear h).choose
  else -(J_rr_linear r).choose

noncomputable def q (r s : ℕ) : ℤ :=
  if r > s then 0
  else if r < s then 0
  else 2

lemma J_symm (r s : ℕ) : J r s = J s r := by
  rw [neg_inj]
  have : ∫ (x : ℝ) in (0)..1, ∫ (y : ℝ) in (0)..1, x ^ r * y ^ s * (x * y).log / (1 - x * y) =
    ∫ (y : ℝ) in (0)..1, ∫ (x : ℝ) in (0)..1, x ^ r * y ^ s * (x * y).log / (1 - x * y) := by
    rw [intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← MeasureTheory.integral_subtype, ← MeasureTheory.integral_subtype]
    simp_rw [intervalIntegral.integral_of_le (show 0 ≤ 1 by norm_num), MeasureTheory.integral_Ioc_eq_integral_Ioo]
    · sorry
    · simp
    · simp
  rw [this]
  apply intervalIntegral.integral_congr
  intro _ _
  simp
  apply intervalIntegral.integral_congr
  intro _ _
  simp
  ring_nf

lemma linear_int_aux : ∃ a b : ℕ → ℕ → ℤ, ∀ r s : ℕ, J r s =
    b r s * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 + a r s / (d (Finset.Icc 1 (Nat.max r s))) ^ 3 := by
  use p
  use q
  intro x y
  if h : x > y then
    cases' (J_rs_linear h) with a ha
    simp only [p, q]
    simp_all only [gt_iff_lt, one_div, dite_eq_ite, ite_true, Int.cast_zero, zero_mul, dite_true,
      zero_add]
    rw [(J_rs_linear h).choose_spec] at ha
    rw [show x.max y = x by exact max_eq_left_iff.2 (LT.lt.le h)]
    simp_all
  else if h1 : x < y then
    cases' (J_rs_linear h1) with a ha
    simp only [p, q]
    obtain h2 := J_symm x y
    simp_all only [gt_iff_lt, one_div, dite_eq_ite, ite_true, ite_self, Int.cast_zero,
      zero_mul, dite_true, zero_add, not_false_eq_true, dite_false]
    rw [(J_rs_linear h1).choose_spec] at ha
    simp only [not_lt] at h
    simp_all
  else
    have h : x = y := by linarith
    cases' (J_rr_linear y) with a ha
    simp only [p, q]
    simp_all only [gt_iff_lt, lt_self_iff_false, not_false_eq_true, dite_eq_ite, ite_false,
      Int.cast_ofNat, not_isEmpty_of_nonempty, tsum_empty, mul_zero, zero_sub, sub_right_inj,
      dite_false, Int.cast_neg, max_self]
    rw [(J_rr_linear y).choose_spec, ← Mathlib.Tactic.RingNF.add_neg, ← neg_div] at ha
    simp_all
