import Zeta3Irrational.Basic
import Zeta3Irrational.Bound
import Zeta3Irrational.Equality
import Zeta3Irrational.Integral
import Zeta3Irrational.LegendrePoly
import Zeta3Irrational.LinearForm
import Zeta3Irrational.d

theorem infinite_primes : {p : ℕ | p.Prime}.Infinite := by
  intro hfin
  set S := hfin.toFinset with hS_def
  set N := (∏ p ∈ S, p) + 1 with hN_def
  have hprod_pos : 0 < ∏ p ∈ S, p := by
    refine Finset.prod_pos (fun p hp => ?_)
    exact (hfin.mem_toFinset.mp hp).pos
  have hN_ne_one : N ≠ 1 := by
    have : 2 ≤ N := by simp [hN_def]; omega
    omega
  obtain ⟨q, hq_prime, hq_div_N⟩ := N.exists_prime_and_dvd hN_ne_one
  have hq_mem : q ∈ S := hfin.mem_toFinset.mpr hq_prime
  have hq_div_prod : q ∣ ∏ p ∈ S, p := Finset.dvd_prod_of_mem _ hq_mem
  have hq_div_one : q ∣ 1 := by
    have h := Nat.dvd_sub' hq_div_N hq_div_prod
    have hsub : N - ∏ p ∈ S, p = 1 := by simp [hN_def]
    rwa [hsub] at h
  exact Nat.Prime.one_lt hq_prime |>.ne' (Nat.dvd_one.mp hq_div_one)



