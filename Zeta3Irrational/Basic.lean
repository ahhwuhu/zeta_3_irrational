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
import Zeta3Irrational.LinearForm

open scoped Nat
open BigOperators Polynomial

noncomputable abbrev JJ (n : ℕ) : ℝ :=
  - ∫ (x : ℝ) in (0)..1, (∫ (y : ℝ) in (0)..1,
    (legendre n).eval x * (legendre n).eval y * (x * y).log / (1 - x * y))

noncomputable abbrev fun1 (n : ℕ) : ℝ := (d (Finset.Icc 1 n)) ^ 3 * JJ n

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

theorem integral_Ioo_congr {f g : ℝ → ℝ} (h : ∀ x ∈ Set.Ioo 0 1, f x = g x) :
    ∫ x in (0)..1, f x = ∫ x in (0)..1, g x := by
  rw [intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
     MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  exact MeasureTheory.setIntegral_congr (by simp) h

/-
∫ (z : ℝ) (x : ℝ) (y : ℝ) in (0)..1, (x * (1 - x) * y * (1 - y) * z *
    (1 - z) / ((1 - (1 - z) * x) * (1 - y * z))) ^ n / ((1 - (1 - z) * x) * (1 - y * z))
-/


lemma intervalIntegral_eq_setInteral' (n : ℕ) :
    ∫ (z : ℝ) (x : ℝ) (y : ℝ) in (0)..1,
    (x * (1 - x) * y * (1 - y) * z *
    (1 - z) / ((1 - (1 - z) * x) * (1 - y * z))) ^ n / ((1 - (1 - z) * x) * (1 - y * z)) =
    ∫ (zxy : ℝ × ℝ × ℝ) in (Set.Ioo 0 1) ×ˢ ((Set.Ioo 0 1) ×ˢ (Set.Ioo 0 1)),
      (zxy.2.1 * (1 - zxy.2.1) * zxy.2.2 * (1 - zxy.2.2) * zxy.1 * (1 - zxy.1) / ((1 - (1 - zxy.1) * zxy.2.1) * (1 - zxy.2.2 * zxy.1))) ^ n /
      ((1 - (1 - zxy.1) * zxy.2.1) * (1 - zxy.2.2 * zxy.1))
      ∂MeasureTheory.volume := by
  sorry

lemma intervalIntegral_eq_setInteral (n : ℕ) :
    ∫ (x : ℝ) (y : ℝ) (z : ℝ) in (0)..1,
    ( x * (1 - x) * y * (1 - y) * z * (1 - z) / ((1 - (1 - z) * x) * (1 - y * z))) ^ n / ((1 - (1 - z) * x) * (1 - y * z)) =
    ∫ (xyz : ℝ × ℝ × ℝ) in (Set.Ioo 0 1) ×ˢ ((Set.Ioo 0 1) ×ˢ (Set.Ioo 0 1)),
      (xyz.1 * (1 - xyz.1) * xyz.2.1 * (1 - xyz.2.1) * xyz.2.2 * (1 - xyz.2.2) / ((1 - (1 - xyz.2.2) * xyz.1) * (1 - xyz.2.1 * xyz.2.2))) ^ n /
      ((1 - (1 - xyz.2.2) * xyz.1) * (1 - xyz.2.1 * xyz.2.2))
      ∂MeasureTheory.volume := by
  rw [intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod]
  swap
  · sorry -- everything is continuous
  refine MeasureTheory.setIntegral_congr (by simp) ?_
  intro x hx
  simp only
  rw [intervalIntegral.integral_of_le (by norm_num), MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod]
  swap
  · sorry -- everything is continuous
  refine MeasureTheory.setIntegral_congr (by simp) ?_
  intro y hy
  simp only
  rw [intervalIntegral.integral_of_le (by norm_num), MeasureTheory.integral_Ioc_eq_integral_Ioo]

lemma integral_comm1 (n : ℕ) : ∫ (x : ℝ) (y : ℝ) in (0)..1, eval x (legendre n) * (-1) ^ n *
    eval y (legendre n) * ∫ (z : ℝ) in (0)..1, 1 / ((1 - (1 - z) * x) * (1 - (1 - y) * z)) =
    ∫ (z : ℝ) (x : ℝ) (y : ℝ) in (0)..1, eval x (legendre n) * eval (1 - y) (legendre n) * 1 /
    ((1 - (1 - z) * x) * (1 - (1 - y) * z)) := by
  sorry

lemma integral_comm2 (n : ℕ) : ∫ (z : ℝ) (x : ℝ) (y : ℝ) in (0)..1, (x * (1 - x) * y * (1 - y) * z *
    (1 - z) / ((1 - (1 - z) * x) * (1 - y * z))) ^ n / ((1 - (1 - z) * x) * (1 - y * z)) =
    ∫ (x : ℝ) (y : ℝ) (z : ℝ) in (0)..1, (x * (1 - x) * y * (1 - y) * z * (1 - z) / ((1 - (1 - z) *
    x) * (1 - y * z))) ^ n / ((1 - (1 - z) * x) * (1 - y * z)) := by
  rw [intervalIntegral_eq_setInteral, intervalIntegral_eq_setInteral',
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod, MeasureTheory.setIntegral_prod]
  pick_goal 2
  · sorry
  pick_goal 2
  · sorry

  change ∫ (z : ℝ) in Set.Ioo 0 1, ∫ (xy : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, _ = ∫ x in _, ∫ (yz) in _, _
  dsimp
  rw [MeasureTheory.integral_integral_swap]
  pick_goal 2
  · sorry

  change ∫ xy in _, ∫ z in _,  _ = _
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.setIntegral_prod]
  pick_goal 2
  · sorry

  refine MeasureTheory.setIntegral_congr (by simp) ?_
  intro x hx
  dsimp
  rw [MeasureTheory.setIntegral_prod]
  sorry


lemma JJ_eq_form (n : ℕ) : JJ n = ∫ (x : ℝ) (y : ℝ) (z : ℝ) in (0)..1,
    ( x * (1 - x) * y * (1 - y) * z * (1 - z) / ((1 - (1 - z) * x) * (1 - y * z))) ^ n / ((1 - (1 - z) * x) * (1 - y * z)) := by
  calc
  _ = ∫ (x : ℝ) (y : ℝ) in (0)..1, eval (1 - x) (legendre n) * eval y (legendre n) * (∫ (z : ℝ) in (0)..1, (1 / (1 - (1 - (1 - x) * y) * z))) := by
    simp_rw [← intervalIntegral.integral_neg, ← neg_div, neg_mul_eq_mul_neg, JJ_upper_aux]
    have eq := intervalIntegral.mul_integral_comp_sub_mul (a := 0) (b := 1)
      (f := fun x ↦ ∫ (y : ℝ) in (0)..1, eval x (legendre n) * eval y (legendre n) * ∫ (z : ℝ) in (0)..1, 1 / (1 - (1 - x * y) * z)) 1 1
    simp only [one_mul, mul_one, sub_self, mul_zero, sub_zero] at eq
    exact eq.symm
  _ = ∫ (x : ℝ) (y : ℝ) in (0)..1, eval x (legendre n) * (-1) ^ n * eval y (legendre n) *
      ∫ (z : ℝ) in (0)..1, 1 /((1 - (1 - z) * x) * (1 - (1 - y) * z)):= by
    apply integral_Ioo_congr
    intro x hx
    apply integral_Ioo_congr
    intro y hy
    simp_all only [Set.mem_Ioo]
    rw [legendre_eval_symm, show 1 - (1 - x) = x by simp, integral_equality x y hx.1 hx.2 hy.1 hy.2]
    ring_nf
  _ = ∫ (z : ℝ) (x : ℝ) (y : ℝ) in (0)..1, eval x (legendre n) * eval (1 - y) (legendre n) *
      1 /((1 - (1 - z) * x) * (1 - (1 - y) * z)):= by
    exact integral_comm1 n
  _ = ∫ (z : ℝ) (x : ℝ) (y : ℝ) in (0)..1, eval x (legendre n) * eval y (legendre n) *
      1 /((1 - (1 - z) * x) * (1 - y * z)):= by
    apply integral_Ioo_congr
    intro z _
    apply integral_Ioo_congr
    intro x _
    have eq := intervalIntegral.mul_integral_comp_sub_mul (a := 0) (b := 1)
      (f := fun y ↦ eval x (legendre n) * eval (1 - y) (legendre n) * 1 / ((1 - (1 - z) * x) * (1 - (1 - y) * z))) 1 1
    simp only [one_mul, sub_sub_cancel, mul_one, sub_self, mul_zero, sub_zero] at eq
    simp_all only [Set.mem_Ioo, eval_mul, one_div, eval_C, mul_one]
  _ = ∫ (z : ℝ) in (0)..1, (∫ (x : ℝ) in (0)..1, eval x (legendre n) / ((1 - (1 - z) * x))) *
      (∫ (y : ℝ) in (0)..1, eval y (legendre n) / ((1 - y * z))) := by
    apply integral_Ioo_congr
    intro z _
    rw [← intervalIntegral.integral_mul_const]
    simp_rw [← intervalIntegral.integral_const_mul, ← mul_div_mul_comm]
    simp
  _ = ∫ (z : ℝ) (x : ℝ) (y : ℝ) in (0)..1,
      ( x * (1 - x) * y * (1 - y) * z * (1 - z) / ((1 - (1 - z) * x) * (1 - y * z))) ^ n /
      ((1 - (1 - z) * x) * (1 - y * z)) := by
    apply integral_Ioo_congr
    intro z hz
    simp only [Set.mem_Ioo] at hz
    have hz1 : 0 < (1 - z) ∧ (1 - z) < 1 := by constructor <;> linarith
    simp_rw [legendre_integral_special hz1, mul_comm, legendre_integral_special hz]
    rw [mul_mul_mul_comm, ← pow_add, ← two_mul, pow_mul]
    simp only [even_two, Even.neg_pow, one_pow, one_mul, div_pow]
    simp_rw [← intervalIntegral.integral_mul_const]
    rw [intervalIntegral.integral_of_le (by norm_num), MeasureTheory.integral_Ioc_eq_integral_Ioo]
    symm
    rw [intervalIntegral.integral_of_le (by norm_num), MeasureTheory.integral_Ioc_eq_integral_Ioo]
    apply MeasureTheory.setIntegral_congr (by simp)
    intro x hx
    simp only
    rw [← intervalIntegral.integral_const_mul]
    apply integral_Ioo_congr
    intro y hy
    simp_all only [div_div, Set.mem_Ioo]
    rw [← mul_div_mul_comm, div_eq_div_iff]
    · simp only [mul_pow]; ring
    · suffices ((1 - z * y) * (1 - x * (1 - z))) ^ n * ((1 - z * y) * (1 - x * (1 - z))) > 0 by linarith
      rw [mul_pow]
      apply mul_pos <;> apply mul_pos
      · apply pow_pos; nlinarith
      · apply pow_pos; nlinarith
      · nlinarith
      · nlinarith
    · suffices (1 - x * (1 - z)) ^ (n + 1) * (1 - z * y) ^ (n + 1) > 0 by linarith
      apply mul_pos <;> apply pow_pos <;> nlinarith
  _ = ∫ (x : ℝ) (y : ℝ) (z : ℝ) in (0)..1,
      ( x * (1 - x) * y * (1 - y) * z * (1 - z) / ((1 - (1 - z) * x) * (1 - y * z))) ^ n /
      ((1 - (1 - z) * x) * (1 - y * z)) := by
    exact integral_comm2 n


lemma JJ_eq_form' (n : ℕ) :
    JJ n =
    ∫ (xyz : ℝ × ℝ × ℝ) in (Set.Ioo 0 1) ×ˢ ((Set.Ioo 0 1) ×ˢ (Set.Ioo 0 1)),
      (xyz.1 * (1 - xyz.1) * xyz.2.1 * (1 - xyz.2.1) * xyz.2.2 * (1 - xyz.2.2) / ((1 - (1 - xyz.2.2) * xyz.1) * (1 - xyz.2.1 * xyz.2.2))) ^ n /
      ((1 - (1 - xyz.2.2) * xyz.1) * (1 - xyz.2.1 * xyz.2.2))
      ∂MeasureTheory.volume := by
  rw [JJ_eq_form, intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod]
  swap
  · sorry -- everything is continuous
  refine MeasureTheory.setIntegral_congr (by simp) ?_
  intro x hx
  simp only
  rw [intervalIntegral.integral_of_le (by norm_num), MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod]
  swap
  · sorry -- everything is continuous
  refine MeasureTheory.setIntegral_congr (by simp) ?_
  intro y hy
  simp only
  rw [intervalIntegral.integral_of_le (by norm_num), MeasureTheory.integral_Ioc_eq_integral_Ioo]

-- lemma IntervalIntegrable1 : IntervalIntegrable
--     (fun x ↦ ∫ (y : ℝ) (z : ℝ) in (0)..1,
--     (x * (1 - x) * y * (1 - y) * z * (1 - z) / ((1 - (1 - z) * x) * (1 - y * z))) ^ n /
--     ((1 - (1 - z) * x) * (1 - y * z))) MeasureTheory.volume 0 1 := by
--   -- apply IntervalIntegrable.mono_fun'
--   -- apply MeasureTheory.continuous_integral_integral
--   rw [intervalIntegrable_iff, MeasureTheory.IntegrableOn, MeasureTheory.Integrable]
--   constructor
--   · sorry
--   · rw [MeasureTheory.HasFiniteIntegral]
--     sorry

-- lemma IntervalIntegrable2 {x : ℝ} (hx : x ∈ Set.Ioo 0 1) : IntervalIntegrable
--     (fun y ↦ ∫ (z : ℝ) in (0)..1,
--     (x * (1 - x) * y * (1 - y) * z * (1 - z) / ((1 - (1 - z) * x) * (1 - y * z))) ^ n /
--     ((1 - (1 - z) * x) * (1 - y * z))) MeasureTheory.volume 0 1 := by
--   apply Continuous.intervalIntegrable
--   simp_rw [intervalIntegral.integral_of_le (show 0 ≤ 1 by norm_num), ← MeasureTheory.integral_Icc_eq_integral_Ioc]
--   apply continuous_parametric_integral_of_continuous
--   · rw [continuous_iff_continuousAt]
--     intro y Y hy
--     sorry
--   · rw [← Set.uIcc_of_le (by norm_num)]
--     exact isCompact_uIcc

-- lemma IntervalIntegrable3 {x y : ℝ} (hx : x ∈ Set.Ioo 0 1) (hy : y ∈ Set.Ioo 0 1): IntervalIntegrable
--   (fun z ↦ (x * (1 - x) * y * (1 - y) * z * (1 - z) / ((1 - (1 - z) * x) * (1 - y * z))) ^ n /
--       ((1 - (1 - z) * x) * (1 - y * z)))
--   MeasureTheory.volume 0 1 := by
--   apply IntervalIntegrable.continuousOn_mul
--   · apply intervalIntegral.intervalIntegrable_inv
--     · intro z hz
--       suffices (1 - (1 - z) * x) * (1 - y * z) > 0 by linarith
--       apply mul_pos <;> simp_all only [Set.mem_Ioo, ge_iff_le, zero_le_one, Set.uIcc_of_le,
--         Set.mem_Icc, sub_pos] <;> nlinarith
--     · apply ContinuousOn.mul
--       · apply ContinuousOn.sub continuousOn_const
--         apply ContinuousOn.mul
--         · apply ContinuousOn.sub continuousOn_const continuousOn_id
--         · exact continuousOn_const
--       · apply ContinuousOn.sub continuousOn_const
--         apply ContinuousOn.mul continuousOn_const continuousOn_id
--   · apply ContinuousOn.pow
--     apply ContinuousOn.div
--     · apply ContinuousOn.mul _ (ContinuousOn.sub continuousOn_const continuousOn_id)
--       apply ContinuousOn.mul continuousOn_const continuousOn_id
--     · apply ContinuousOn.mul
--       · apply ContinuousOn.sub continuousOn_const
--         apply ContinuousOn.mul _ continuousOn_const
--         apply ContinuousOn.sub continuousOn_const continuousOn_id
--       · apply ContinuousOn.sub continuousOn_const
--         apply ContinuousOn.mul continuousOn_const continuousOn_id
--     · intro z hz
--       suffices (1 - (1 - z) * x) * (1 - y * z) > 0 by linarith
--       apply mul_pos <;>
--       simp_all only [Set.mem_Ioo, ge_iff_le, zero_le_one, Set.uIcc_of_le, Set.mem_Icc, sub_pos] <;>
--       nlinarith

lemma JJ_pos (n : ℕ) : 0 < JJ n := by
  rw [JJ_eq_form']
  -- rw [intervalIntegral.integral_of_le]
  -- simp_rw [intervalIntegral.integral_of_le]
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · set F := _;
    change 0 < MeasureTheory.volume.restrict _ (Function.support F)

    have subset : Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ⊆ Function.support F := sorry

    rw [MeasureTheory.Measure.restrict_apply']
    rw [Set.inter_eq_right.2 subset]
    simp only [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    simp only [Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one, zero_lt_one]
    · measurability
  · delta Filter.EventuallyLE
    rw [Filter.eventually_iff, MeasureTheory.mem_ae_iff]
    rw [MeasureTheory.Measure.restrict_apply']
    convert_to MeasureTheory.volume (∅ : Set (ℝ × ℝ × ℝ)) = 0
    · congr 1
      ext ⟨x, ⟨y, z⟩⟩
      simp only [Pi.zero_apply, div_pow, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
        not_le, Set.mem_prod, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false, not_and, not_lt,
        and_imp]
      contrapose!
      rintro ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩
      sorry
    · exact MeasureTheory.OuterMeasureClass.measure_empty MeasureTheory.volume
    . measurability
  · sorry
  -- apply intervalIntegral.intervalIntegral_pos_of_pos_on IntervalIntegrable1 _ (by simp)
  -- · intro x hx
  --   apply intervalIntegral.intervalIntegral_pos_of_pos_on (IntervalIntegrable2 hx) _ (by simp)
  --   · intro y hy
  --     apply intervalIntegral.intervalIntegral_pos_of_pos_on (IntervalIntegrable3 hx hy) _ (by simp)
  --     · intro z hz
  --       simp_all only [Set.mem_Ioo]
  --       cases' hx with hx1 hx2
  --       cases' hy with hy1 hy2
  --       cases' hz with hz1 hz2
  --       rw [← sub_pos] at hx2 hy2 hz2
  --       apply div_pos
  --       · rw [div_pow]
  --         apply div_pos
  --         · apply pow_pos; positivity
  --         · apply pow_pos
  --           apply mul_pos <;> nlinarith
  --       · apply mul_pos <;> nlinarith

lemma JJ_upper (n : ℕ) : JJ n < 2 * (1 / 30) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  rw [JJ_eq_form, mul_rotate, mul_assoc]
  nth_rewrite 2 [mul_comm]
  rw [← zeta_3_eq_form]
  rw [← intervalIntegral.integral_const_mul]
  simp_rw [← intervalIntegral.integral_const_mul]
  sorry

lemma upper_tendsto_zero : Filter.Tendsto (fun n ↦ (2 * (21 / 30) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3)) Filter.atTop (nhds 0) := by
  rw [show (0 : ℝ) = 2 * 0 by simp]
  simp_rw [mul_assoc]
  apply Filter.Tendsto.const_mul (b := 2) (f := fun n ↦ (21 / 30) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3)
    (c := 0) (l := Filter.atTop)
  rw [show (0 : ℝ) = 0 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 by simp]
  apply Filter.Tendsto.mul_const (b := ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) (f := fun n ↦ (21 / 30) ^ n)
    (c := 0) (l := Filter.atTop)
  apply tendsto_pow_atTop_nhds_zero_of_lt_one (r := (21 / 30 : ℝ)) <;>
  norm_num

lemma fun1_tendsto_zero : Filter.Tendsto (fun n ↦ ENNReal.ofReal (fun1 n)) Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  if h : ε = ⊤ then simp [h]
  else
    delta fun1
    rw [show ε = ENNReal.ofReal ε.toReal by simp [h]]
    -- use x/lnx 的等价无穷小代换
    use 1
    intro n hn
    rw [ENNReal.ofReal_le_ofReal_iff (by simp)]

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
  have prop1 := ENNReal.Tendsto.mul_const (b := (q : ENNReal)) (fun1_tendsto_zero) (by simp)
  rw [zero_mul] at prop1
  have prop2 : ∀ n : ℕ, fun1 n * q > 1/2 := by
    suffices ∀ n : ℕ, fun1 n * q ≥ 1 by intro n; linarith [this n]
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
  rw [ENNReal.tendsto_atTop_zero] at prop1
  specialize prop1 (1/2) (by simp)
  simp only [one_div, Ico_mem_nhds_iff, Set.mem_Ioo, inv_pos, Nat.ofNat_pos, and_true, Set.mem_Ico,
    Filter.eventually_top] at prop1
  rw [← one_div] at prop1
  simp only [Filter.eventually_atTop, ge_iff_le] at prop1
  cases' prop1 with a ha
  specialize prop2 (a + 1)
  specialize ha (a + 1) (by simp)
  rw [gt_iff_lt, ← ENNReal.ofReal_lt_ofReal_iff, ENNReal.ofReal_mul' (by simp)] at prop2
  · suffices ENNReal.ofReal (fun1 (a + 1)) * ↑q < ENNReal.ofReal (fun1 (a + 1)) * ↑q by
      simp only [mul_neg, eval_mul, one_div, eval_C, Function.iterate_succ, Function.comp_apply,
      derivative_mul, derivative_X_pow, Nat.cast_add, Nat.cast_one, map_add, map_natCast, map_one,
      add_tsub_cancel_right, iterate_map_add, eval_add, lt_self_iff_false] at this
    rw [show ENNReal.ofReal ↑q = (q : ENNReal) by simp only [ENNReal.ofReal_natCast],
      show ENNReal.ofReal (1 / 2) = 1 / 2 by rw [← Real.ennnorm_eq_ofReal (by simp)]; simp] at prop2
    apply LE.le.trans_lt (b := (1 / 2 : ENNReal)) ha prop2
  · apply mul_pos _ (by simp; omega)
    apply mul_pos _ (JJ_pos (a + 1))
    apply pow_pos
    simp only [Nat.cast_pos]
    exact fin_d_neq_zero (a + 1)
