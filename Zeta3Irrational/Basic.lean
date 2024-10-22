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
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (-(x.1 * x.2).log / (1 - x.1 * x.2) * (shiftedLegendre n).eval x.1 * (shiftedLegendre n).eval x.2)

noncomputable abbrev JJ' (n : ℕ) : ℝ :=
    ∫ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
    (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1)

noncomputable abbrev JJENN (n : ℕ) : ENNReal :=
    ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ENNReal.ofReal
    ((x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
    (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1))

noncomputable abbrev fun1 (n : ℕ) : ℝ := (d (Finset.Icc 1 n)) ^ 3 * JJ n

lemma linear_int (n : ℕ) : ∃ a b : ℕ → ℤ,
    fun1 n = a n + b n * (d (Finset.Icc 1 n) : ℤ) ^ 3  * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  delta fun1 JJ
  obtain ⟨c, hc⟩ := shiftedLegendre_eq_int_poly n
  simp_rw [hc, Polynomial.eval_finset_sum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
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
  rw [hqq', mul_add, mul_add, add_comm]
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

lemma JJ_eq_form (n : ℕ) : JJ n = JJ' n := by
  simp only [JJ, JJ']
  calc
  _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    eval x.1 (shiftedLegendre n) * eval x.2 (shiftedLegendre n) * (∫ (z : ℝ) in (0)..1, (1 / (1 - (1 - x.1 * x.2) * z))) := by
    apply MeasureTheory.setIntegral_congr (by measurability)
    intro x hx
    simp only [Set.mem_prod, Set.mem_Ioo] at hx ⊢
    rw [mul_assoc, mul_comm, ← integral1] <;> nlinarith
  _ = ∫ (x : ℝ) (y : ℝ) in (0)..1, eval x (shiftedLegendre n) * (-1) ^ n * eval y (shiftedLegendre n) *
      ∫ (z : ℝ) in (0)..1, 1 /((1 - (1 - z) * x) * (1 - (1 - y) * z)):= by
    sorry
  _ = ∫ (z : ℝ) (x : ℝ) (y : ℝ) in (0)..1,
      ( x * (1 - x) * y * (1 - y) * z * (1 - z) / ((1 - (1 - z) * x) * (1 - y * z))) ^ n /
      ((1 - (1 - z) * x) * (1 - y * z)) := by
    sorry
  _ = ∫ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) / (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n /
      (1 - (1 - x.2.1 * x.2.2) * x.1) := by
    sorry

lemma JJENN_upper (n : ℕ) : JJENN n ≤
    ENNReal.ofReal (2 * (1 / 24) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) := by
  calc
  _ ≤ ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal ((1 / 24) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
    rw [JJENN, ← MeasureTheory.lintegral_indicator _ (by measurability),
        ← MeasureTheory.lintegral_indicator _ (by measurability)]
    apply MeasureTheory.lintegral_mono
    intro x
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
    · simp only [h, ↓reduceIte]
      simp only [Set.mem_prod, Set.mem_Ioo] at h
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_div_right]
      · apply pow_le_pow_left
        · apply div_nonneg
          · apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg (by linarith) (by linarith)
          · simp only [sub_nonneg]
            suffices (1 - x.2.1 * x.2.2) * x.1 < x.1 by linarith
            rw [mul_lt_iff_lt_one_left]
            · simp only [sub_lt_self_iff]
              nlinarith
            · nlinarith
        · suffices x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
            (1 - (1 - x.2.1 * x.2.2) * x.1) < (1 / 24 : ℝ)by linarith
          apply bound' <;> linarith
      · simp only [sub_pos]
        suffices (1 - x.2.1 * x.2.2) * x.1 < x.1 by linarith
        rw [mul_lt_iff_lt_one_left]
        · simp only [sub_lt_self_iff]
          nlinarith
        · nlinarith
    · simp only [h, ↓reduceIte, le_refl]
  _ = ENNReal.ofReal ((1 / 24) ^ n) * ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
    rw [← MeasureTheory.lintegral_const_mul]
    · rw [← MeasureTheory.lintegral_indicator _ (by measurability),
        ← MeasureTheory.lintegral_indicator _ (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [h, ↓reduceIte]
        rw [← ENNReal.ofReal_mul, ← mul_one_div]
        apply pow_nonneg (by norm_num)
      · simp only [h, ↓reduceIte]
    · apply Measurable.ennreal_ofReal
      apply Measurable.const_div
      apply Measurable.const_sub
      apply Measurable.mul _ measurable_fst
      apply Measurable.const_sub
      apply Measurable.mul
      apply Measurable.comp' measurable_fst measurable_snd
      apply Measurable.comp' measurable_snd measurable_snd
  _ = ENNReal.ofReal (2 * (1 / 24) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) := by
    have h := JENN_eq_triple 0 0
    simp only [pow_zero, mul_one] at h
    rw [← h, J_ENN_rr]
    simp only [one_div, inv_pow, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, mul_zero,
      sub_zero]
    rw [← ENNReal.ofReal_mul (by norm_num), ← mul_assoc]
    nth_rw 2 [mul_comm]

lemma integrableOn_JJ' (n : ℕ) : MeasureTheory.Integrable (fun (x : ℝ × ℝ × ℝ) ↦
    (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) / (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n /
    (1 - (1 - x.2.1 * x.2.2) * x.1)) (MeasureTheory.volume.restrict (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)) := by
  rw [MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    rw [← aemeasurable_indicator_iff (by measurability)]
    apply AEMeasurable.indicator _ (by measurability)
    apply AEMeasurable.div
    · apply AEMeasurable.pow_const
      apply AEMeasurable.div
      · apply AEMeasurable.mul _ (AEMeasurable.const_sub (AEMeasurable.fst (f := id) aemeasurable_id) _)
        apply AEMeasurable.mul _ (AEMeasurable.fst (f := id) aemeasurable_id)
        apply AEMeasurable.mul _ (AEMeasurable.const_sub (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.2)
          (AEMeasurable.snd (f := id) aemeasurable_id)) _)
        apply AEMeasurable.mul _ (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.2)
          (AEMeasurable.snd (f := id) aemeasurable_id))
        apply AEMeasurable.mul _ (AEMeasurable.const_sub (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.1)
          (AEMeasurable.fst (f := id) aemeasurable_id)) _)
        exact (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.1)
          (AEMeasurable.fst (f := id) aemeasurable_id))
      · apply AEMeasurable.const_sub
        apply AEMeasurable.mul _ (AEMeasurable.fst (f := id) aemeasurable_id)
        apply AEMeasurable.const_sub
        apply AEMeasurable.mul _ (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.2)
          (AEMeasurable.snd (f := id) aemeasurable_id))
        exact (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.1)
          (AEMeasurable.fst (f := id) aemeasurable_id))
    · apply AEMeasurable.const_sub
      apply AEMeasurable.mul _ (AEMeasurable.fst (f := id) aemeasurable_id)
      apply AEMeasurable.const_sub
      apply AEMeasurable.mul _ (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.2)
        (AEMeasurable.snd (f := id) aemeasurable_id))
      exact (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.1)
        (AEMeasurable.fst (f := id) aemeasurable_id))
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    set k := _
    change k < ⊤
    have : k = JJENN n := by
      simp only [k, JJENN]
      rw [← MeasureTheory.lintegral_indicator _ (by measurability),
        ← MeasureTheory.lintegral_indicator _ (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, norm_mul, norm_div, norm_neg, Real.norm_eq_abs, norm_pow]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [ENNReal.ofReal_eq_ofReal_iff]
        · congr 3
          · rw [abs_eq_self.2, abs_eq_self.2, abs_eq_self.2, abs_eq_self.2, abs_eq_self.2,
              abs_eq_self.2] <;> nlinarith
          · simp only [abs_eq_self, sub_nonneg]
            apply mul_le_one (by nlinarith) (by linarith) (by linarith)
          · simp only [abs_eq_self, sub_nonneg]
            apply mul_le_one (by nlinarith) (by linarith) (by linarith)
        · positivity
        · apply div_nonneg
          · apply pow_nonneg
            apply div_nonneg
            · apply mul_nonneg _ (by linarith)
              apply mul_nonneg _ (by linarith)
              apply mul_nonneg _ (by linarith)
              apply mul_nonneg _ (by linarith)
              apply mul_nonneg (by linarith) (by linarith)
            · simp only [abs_eq_self, sub_nonneg]
              apply mul_le_one (by nlinarith) (by linarith) (by linarith)
          · simp only [abs_eq_self, sub_nonneg]
            apply mul_le_one (by nlinarith) (by linarith) (by linarith)
      · simp only [hx, ↓reduceIte]
    rw [this]
    apply LE.le.trans_lt (JJENN_upper n)
    simp only [one_div, inv_pow, ENNReal.ofReal_lt_top]

lemma JJ_pos (n : ℕ) : 0 < JJ n := by
  rw [JJ_eq_form, JJ']
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · set F := _;
    change 0 < MeasureTheory.volume.restrict _ (Function.support F)
    have subset : Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ⊆ Function.support F := by
      intro a ha
      change F a ≠ 0
      simp only [div_pow, ne_eq, _root_.div_eq_zero_iff, pow_eq_zero_iff', mul_eq_zero, not_or,
        not_and, Decidable.not_not, F]
      simp only [Set.mem_prod, Set.mem_Ioo] at ha
      rcases ha with ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hz0, hz1⟩
      constructor
      · constructor
        · intro h
          rcases h with (h | h); swap; nlinarith
          rcases h with (h | h); swap; nlinarith
          rcases h with (h | h); swap; nlinarith
          rcases h with (h | h); swap; nlinarith
          rcases h with (h | h) <;> nlinarith
        · intro h
          suffices ¬1 - (1 - a.2.1 * a.2.2) * a.1 = 0 by tauto
          suffices 1 - (1 - a.2.1 * a.2.2) * a.1 > 0 by linarith
          simp only [gt_iff_lt, sub_pos]
          suffices (1 - a.2.1 * a.2.2) * a.1 < a.1 by linarith
          rw [mul_lt_iff_lt_one_left]
          · simp only [sub_lt_self_iff]
            nlinarith
          · exact hx0
      · suffices 1 - (1 - a.2.1 * a.2.2) * a.1 > 0 by linarith
        simp only [gt_iff_lt, sub_pos]
        suffices (1 - a.2.1 * a.2.2) * a.1 < a.1 by linarith
        rw [mul_lt_iff_lt_one_left]
        · simp only [sub_lt_self_iff]
          nlinarith
        · exact hx0
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
      suffices 0 < (y * (1 - y) * z * (1 - z) * x * (1 - x)) ^ n / (1 - (1 - y * z) * x) ^ n /
        (1 - (1 - y * z) * x) by linarith
      apply div_pos
      · apply div_pos
        · apply pow_pos
          apply mul_pos; swap; linarith
          apply mul_pos; swap; linarith
          apply mul_pos; swap; linarith
          apply mul_pos; swap; linarith
          apply mul_pos hy0; linarith
        · apply pow_pos
          simp only [sub_pos]
          suffices (1 - y * z) * x < x by linarith
          rw [mul_lt_iff_lt_one_left]
          · simp only [sub_lt_self_iff]
            nlinarith
          · exact hx0
      · simp only [sub_pos]
        suffices (1 - y * z) * x < x by linarith
        rw [mul_lt_iff_lt_one_left]
        · simp only [sub_lt_self_iff]
          nlinarith
        · exact hx0
    · exact MeasureTheory.OuterMeasureClass.measure_empty MeasureTheory.volume
    . measurability
  · exact integrableOn_JJ' n

lemma Summable_of_zeta_two' : Summable (fun (n : ℕ) ↦ 1 / ((n : ℝ) + 1) ^ 2) := by
  rw [Summable]
  use Real.pi ^ 2 / 6
  obtain h := hasSum_zeta_two
  let f := fun (n : ℕ) ↦ 1 / (n : ℝ) ^ 2
  let g := fun (n : ℕ) => n + 1
  have h1 : Function.Injective g := by
    intro m n h
    simp only [g] at h
    linarith
  have h2 : ∀ x ∉ Set.range g, f x = 0 := by
    intro x hx
    simp only [Set.mem_range, not_exists] at hx
    suffices x = 0 by simp only [one_div, inv_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero, f, this]
    by_contra! h
    apply hx (x - 1)
    simp only [g]
    omega
  have h3 : f ∘ g = fun (n : ℕ) ↦ 1 / (n + 1 : ℝ) ^ 2 := by
    ext x
    simp [f, g]
  have := Function.Injective.hasSum_iff (f := f) (g := g) (a := (Real.pi ^ 2 / 6 : ℝ)) h1 h2
  rw [h3] at this
  rw [this]
  simp only [f]
  exact h

lemma zeta_3_pos : 0 < ∑' (n : ℕ), 1 / ((n : ℝ) + 1) ^ 3 := by
  apply tsum_pos (ι := ℕ) (g := fun n => 1 / ((n : ℝ) + 1) ^ 3) (i := 1)
  · apply summable_of_sum_range_le (c := Real.pi ^ 2 / 6)
    · intro _
      positivity
    · intro n
      suffices ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 3 ≤ ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 by
        have : ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 ≤ Real.pi ^ 2 / 6 := by
          suffices ∑ i in Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 ≤ ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 2 by
            have h : ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 2 = (riemannZeta 2).re := by
              rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp)]
              simp_rw [← Complex.ofReal_natCast]
              norm_cast
            rw [h, riemannZeta_two] at this
            norm_cast at *
          apply sum_le_tsum (s := Finset.range n)
          intro i _
          positivity
          exact Summable_of_zeta_two'
        linarith
      apply Finset.sum_le_sum
      intro i _
      rw [div_le_div_iff, one_mul, one_mul]
      · apply pow_le_pow_right <;> linarith
      · positivity
      · positivity
  · intro m
    simp only [one_div, pow_succ, add_comm, add_left_comm]
    positivity
  · positivity

theorem JJ_upper (n : ℕ) : JJ n ≤ 2 * (1 / 24) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  rw [JJ_eq_form, JJ', MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  · trans (ENNReal.ofReal (2 * (1 / 24 : ℝ) ^ n * ∑' (n : ℕ), 1 / ((n : ℝ) + 1) ^ 3)).toReal
    · apply ENNReal.toReal_mono
      · exact ENNReal.ofReal_ne_top
      · exact JJENN_upper n
    · rw [ENNReal.toReal_ofReal]
      apply mul_nonneg (by norm_num)
      linarith [zeta_3_pos]
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · rw [MeasureTheory.IntegrableOn]
      exact integrableOn_JJ' n
    · rintro s hs -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro x hx
      by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [Set.mem_prod, Set.mem_Ioo] at h
        apply div_nonneg
        · apply pow_nonneg
          apply div_nonneg
          · apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg (by linarith) (by linarith)
          · simp only [abs_eq_self, sub_nonneg]
            apply mul_le_one (by nlinarith) (by linarith) (by linarith)
        · simp only [abs_eq_self, sub_nonneg]
          apply mul_le_one (by nlinarith) (by linarith) (by linarith)
      · rw [Set.mem_inter_iff] at hx
        tauto
  · apply AEMeasurable.aestronglyMeasurable
    rw [← aemeasurable_indicator_iff (by measurability)]
    apply AEMeasurable.indicator _ (by measurability)
    apply AEMeasurable.div
    · apply AEMeasurable.pow_const
      apply AEMeasurable.div
      · apply AEMeasurable.mul _ (AEMeasurable.const_sub (AEMeasurable.fst (f := id) aemeasurable_id) _)
        apply AEMeasurable.mul _ (AEMeasurable.fst (f := id) aemeasurable_id)
        apply AEMeasurable.mul _ (AEMeasurable.const_sub (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.2)
          (AEMeasurable.snd (f := id) aemeasurable_id)) _)
        apply AEMeasurable.mul _ (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.2)
          (AEMeasurable.snd (f := id) aemeasurable_id))
        apply AEMeasurable.mul _ (AEMeasurable.const_sub (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.1)
          (AEMeasurable.fst (f := id) aemeasurable_id)) _)
        exact (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.1)
          (AEMeasurable.fst (f := id) aemeasurable_id))
      · apply AEMeasurable.const_sub
        apply AEMeasurable.mul _ (AEMeasurable.fst (f := id) aemeasurable_id)
        apply AEMeasurable.const_sub
        apply AEMeasurable.mul _ (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.2)
          (AEMeasurable.snd (f := id) aemeasurable_id))
        exact (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.1)
          (AEMeasurable.fst (f := id) aemeasurable_id))
    · apply AEMeasurable.const_sub
      apply AEMeasurable.mul _ (AEMeasurable.fst (f := id) aemeasurable_id)
      apply AEMeasurable.const_sub
      apply AEMeasurable.mul _ (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.2)
        (AEMeasurable.snd (f := id) aemeasurable_id))
      exact (AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.1)
        (AEMeasurable.fst (f := id) aemeasurable_id))

lemma zeta3_le_zeta2 : ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 < ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 2 := by
  apply tsum_lt_tsum_of_nonneg (f := fun n => 1 / ((n : ℝ) + 1) ^ 3) (g := fun n => 1 / ((n : ℝ) + 1) ^ 2) (i := 2)
  · intro n
    positivity
  · intro n
    rw [div_le_div_iff, one_mul, one_mul]
    · apply pow_le_pow_right <;> linarith
    · positivity
    · positivity
  · norm_num
  · exact Summable_of_zeta_two'

lemma ε_N_def_of_pi_alt : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n : ℕ, n ≥ N → n.primeCounting ≤ (1 + ε) * (n : ℝ) / (n : ℝ).log := by
  intro ε hε
  obtain ⟨c,⟨hc0, hc1⟩⟩ := pi_alt
  rw [Asymptotics.isLittleO_const_iff (by simp), tendsto_atTop_nhds] at hc0
  specialize hc0 (Set.Ioo (-ε) ε) (by simp only [Set.mem_Ioo, Left.neg_neg_iff, hε, and_self])
    (by exact isOpen_Ioo)
  obtain ⟨N, hN⟩ := hc0
  use ⌈N⌉₊ + 2
  intro n hn
  have hn' : n ≥ N := by
    trans (⌈N⌉₊ : ℝ)
    norm_cast
    linarith
    exact Nat.le_ceil N
  specialize hN n hn'
  specialize hc1 n
  simp only [Nat.floor_natCast] at hc1
  simp only [Set.mem_Ioo] at hN
  rw [hc1, ← mul_div, ← mul_div, mul_le_mul_right]
  linarith
  apply div_pos
  norm_cast
  omega
  apply Real.log_pos
  norm_cast
  omega

lemma eventuallyN_of_le : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ↑(d (Finset.Icc 1 n)) ^ 3 ≤ (21 : ℝ) ^ n := by
    have h1 : (Real.exp 1) ^ 3 < (21 : ℝ) := by
      suffices (2.7182818286) ^ 3 < (21 : ℝ) by
        exact pow_lt_pow_left Real.exp_one_lt_d9 (n := 3) (by linarith [Real.exp_pos 1]) (by simp) |>.trans this
      norm_num
    have h : Real.log (21 ^ (1 / 3 : ℝ)) - 1 > 0 := by
      simp only [gt_iff_lt, sub_pos]
      rw [Real.exp_one_pow, Nat.cast_ofNat] at h1
      rwa [Real.log_rpow (by norm_num), one_div_mul_eq_div, lt_div_iff (by norm_num), one_mul,
         Real.lt_log_iff_exp_lt (by norm_num)]
    obtain ⟨N, hN⟩ := ε_N_def_of_pi_alt (Real.log (21 ^ (1 / 3)) - 1) h
    use N + 2
    intro n hn
    specialize hN n (by linarith [hn])
    rw [add_sub_cancel, Real.log_rpow (by norm_num)] at hN
    calc
    _ ≤ ((n : ℝ) ^ (n.primeCounting)) ^ 3 := by
      norm_cast
      apply pow_le_pow_left (by simp)
      exact d_le_pow_counting n
    _ ≤ (n ^ (1 / 3 * Real.log 21 * ↑n / Real.log ↑n)) ^ 3 := by
      apply pow_le_pow_left (by simp)
      rw [← Real.rpow_natCast, Real.rpow_le_rpow_left_iff]
      exact hN
      simp only [Nat.one_lt_cast]
      omega
    _ ≤ (21 : ℝ) ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by simp), mul_comm]
      nth_rewrite 1 [← Real.exp_log (x := n) (by simp only [Nat.cast_pos]; omega)]
      have h2 : Real.log ↑n * (↑3 * (1 / 3 * Real.log 21 * ↑n / Real.log ↑n)) = Real.log 21 * ↑n := by
        rw [← mul_assoc, mul_div, ← mul_assoc, ← mul_assoc]
        simp only [one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          IsUnit.mul_inv_cancel_right]
        rw [mul_rotate, ← mul_div, div_self, mul_one]
        simp only [ne_eq, Real.log_eq_zero, Nat.cast_eq_zero, Nat.cast_eq_one, not_or]
        norm_cast
        simp only [not_false_eq_true, and_true]
        constructor <;> omega
      rw [← Real.exp_one_rpow, ← Real.rpow_mul (by exact Real.exp_nonneg 1)]
      norm_cast
      rw [h2, Real.rpow_mul (by exact Real.exp_nonneg 1), Real.exp_one_rpow, Real.exp_log (by norm_num)]
      norm_cast

theorem fun1_tendsto_zero : Filter.Tendsto (fun n ↦ ENNReal.ofReal (fun1 n)) Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  if h : ε = ⊤ then simp [h]
  else
    delta fun1
    rw [show ε = ENNReal.ofReal ε.toReal by simp [h]]
    obtain ⟨N, hN⟩ := eventuallyN_of_le
    obtain h := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (ENNReal.ofReal (21 / 24 : ℝ)))
      (by simp only [ENNReal.ofReal_lt_one]; norm_num)
    rw [ENNReal.tendsto_atTop_zero] at h
    specialize h (ε / (ENNReal.ofReal (2 * (∑' n : ℕ , 1 / ((n : ℝ)+ 1) ^ 3))))
      (by simp only [one_div, gt_iff_lt, ENNReal.div_pos_iff, ne_eq, ENNReal.ofReal_ne_top,
        not_false_eq_true, and_true]; aesop)
    obtain ⟨N1, hN1⟩ := h
    use N.max N1
    intro n hn
    rw [ENNReal.ofReal_le_ofReal_iff (by simp)]
    suffices ↑(d (Finset.Icc 1 n)) ^ 3 * 2 * (1 / 24) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 ≤ ε.toReal by
      trans ↑(d (Finset.Icc 1 n)) ^ 3 * 2 * (1 / 24) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3
      swap
      exact this
      rw [mul_assoc, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by simp)
      linarith [JJ_upper n]
    calc
    _ ≤ 2 * (21 / 24 : ℝ) ^ n * (∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith[zeta_3_pos])
      nth_rewrite 2 [mul_comm, div_eq_mul_one_div]
      rw [mul_pow, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hN n (le_of_max_le_left hn)
    _ ≤ ε.toReal := by
      specialize hN1 n (le_of_max_le_right hn)
      rw [← ENNReal.ofReal_toReal_eq_iff.2 h, ← ENNReal.ofReal_div_of_pos (by linarith [zeta_3_pos]),
        ← ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_le_ofReal_iff] at hN1
      · rw [le_div_iff₀ (by linarith [zeta_3_pos])] at hN1
        linarith
      · suffices 0 <  ε.toReal / (2 * ∑' (n : ℕ), 1 / ((n : ℝ) + 1) ^ 3)by linarith
        apply div_pos _ (by linarith [zeta_3_pos])
        apply ENNReal.toReal_pos (by aesop) (by aesop)

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
