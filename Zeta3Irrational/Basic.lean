/-
A formal proof of the irrationality of Riemann-Zeta(3).
Author: Junqi Liu and Jujian Zhang.
-/
import Mathlib
import Zeta3Irrational.d
import Zeta3Irrational.Integral
import Zeta3Irrational.Equality
import Zeta3Irrational.LegendrePoly
import Zeta3Irrational.Bound

open scoped Nat
open BigOperators

namespace LinearForm

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
  -- rw [neg_inj]
  -- have : ∫ (x : ℝ) in (0)..1, ∫ (y : ℝ) in (0)..1, x ^ r * y ^ s * (x * y).log / (1 - x * y) =
  --   ∫ (y : ℝ) in (0)..1, ∫ (x : ℝ) in (0)..1, x ^ r * y ^ s * (x * y).log / (1 - x * y) := by
  --   sorry
  -- rw [this]
  -- apply intervalIntegral.integral_congr
  -- intro _ _
  -- simp
  -- apply intervalIntegral.integral_congr
  -- intro _ _
  -- simp
  -- ring_nf
  sorry

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

end LinearForm

open Polynomial LinearForm

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
  delta JJ
  simp only [Left.neg_pos_iff]
  sorry
  -- simp only [JJ]
  -- rw [← intervalIntegral.integral_neg]
  -- apply intervalIntegral.intervalIntegral_pos_of_pos_on
  -- · apply IntervalIntegrable.neg
  --   sorry
  -- · intro x hx
  --   rw [← intervalIntegral.integral_neg]
  --   apply intervalIntegral.intervalIntegral_pos_of_pos_on
  --   · apply IntervalIntegrable.neg
  --     apply IntervalIntegrable.continuousOn_mul
  --     · apply intervalIntegral.intervalIntegrable_inv
  --       · intro y hy
  --         have : x * y < 1 := by
  --           obtain ⟨hx1, hx2⟩ := hx
  --           simp_all only [ge_iff_le, zero_le_one, Set.uIcc_of_le, Set.mem_Icc]
  --           obtain ⟨hy1, hy2⟩ := hy
  --           calc x * y ≤ x := by rwa [mul_le_iff_le_one_right hx1]
  --             _ < 1 := by exact hx2
  --         linarith
  --       · apply ContinuousOn.sub continuousOn_const
  --         apply ContinuousOn.mul continuousOn_const continuousOn_id
  --     · apply ContinuousOn.mul
  --       · sorry
  --       · sorry
  --   · intro y hy
  --     simp only [Left.neg_pos_iff]
  --     apply mul_neg_of_neg_of_pos
  --     · apply mul_neg_of_pos_of_neg
  --       · sorry
  --       · refine Real.log_neg ?_ (mul_lt_one_aux hx hy)
  --         simp_all
  --     · rw [inv_pos, sub_pos]
  --       exact mul_lt_one_aux hx hy
  --   · norm_num
  -- · norm_num

lemma linear_int (n : ℕ) : ∃ a b : ℕ → ℤ,
    fun1 n = a n + b n * (d (Finset.Icc 1 n) : ℤ) ^ 3  * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  delta fun1 JJ
  obtain ⟨c, hc⟩ := legendre_eq_intpoly n
  simp_rw [hc, Polynomial.eval_finset_sum, Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_div]
  simp only [zsmul_eq_mul, eval_mul, eval_intCast, eval_pow, eval_X]
  simp_rw [← mul_assoc, multi_integral_sum_comm, multi_integral_mul_const]
  simp only [← Finset.sum_neg_distrib, Finset.mul_sum]
  obtain ⟨qq', ⟨pp', hqq'⟩⟩ := linear_int_aux
  use fun n => ∑ x ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
    d (Finset.Icc 1 n) ^ 3 * c x * c i * qq' x i / d (Finset.Icc 1 (Nat.max x i)) ^ 3
  use fun n => ∑ x ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1), c x * c i * pp' x i
  rw [← Nat.cast_pow, ← Int.cast_pow , ← Int.cast_mul, Finset.sum_mul]
  simp only [Nat.cast_pow, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  specialize hqq' x y
  rw [hqq', ← mul_neg, neg_neg, mul_add, mul_add, add_comm]
  congr 1
  · rw [Int.cast_div]
    · rw [mul_div_assoc', ← mul_div_assoc, div_eq_div_iff]
      · norm_cast
        rw [← mul_assoc, ← mul_assoc]
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        Nat.cast_eq_zero]
        apply d_ne_zero
        simp
      · simp only [Int.cast_pow, Int.cast_natCast, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, Nat.cast_eq_zero]
        apply d_ne_zero
        simp
    · rw [mul_assoc, mul_assoc]
      apply Dvd.dvd.mul_right
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, IsIntegrallyClosed.pow_dvd_pow_iff]
      norm_cast
      apply d_dvd_d_of_le
      simp_all only [zsmul_eq_mul, Finset.mem_range, Finset.le_eq_subset]
      intro a b
      simp_all only [Finset.mem_Icc, true_and]
      simp only [one_div, le_max_iff] at b
      rcases b with ⟨_ ,(c | c)⟩
      <;>
      linarith
    · simp only [Int.cast_pow, Int.cast_natCast, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, Nat.cast_eq_zero]
      apply d_ne_zero
      simp
  · ring

lemma JJ_upper (n : ℕ) : JJ n < 2 * (1 / 30) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  simp only [JJ]
  simp_rw [← intervalIntegral.integral_neg, ← neg_div, neg_mul_eq_mul_neg, JJ_upper_aux,
    ← intervalIntegral.integral_const_mul]
  sorry

lemma upper_tendsto_zero : Filter.Tendsto (fun n ↦ 2 * (21 / 30) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) ⊤ (nhds 0) := by
  sorry

lemma fun1_tendsto_zero : Filter.Tendsto (fun n ↦ fun1 n) ⊤ (nhds 0) := by
  intro x hx
  delta fun1
  sorry

theorem zeta_3_irratoinal : ¬ ∃ r : ℚ , (r : ℝ) = riemannZeta 3 := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp)]
  simp_rw [← Complex.ofReal_natCast]
  norm_cast
  simp_rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
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
