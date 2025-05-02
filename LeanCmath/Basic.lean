import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith

open Nat

theorem infinitude_of_primes : ∀ (n : ℕ), ∃ p ≥ n, Nat.Prime p := by
  intro n

  let m := factorial n + 1
  let p := minFac m

  -- Show that p is prime by being the minimum factor of m, and by m > 1
  have p_prime : Nat.Prime p := by
    -- minFac's are prime so long as m ≠ 1
    refine minFac_prime ?_
    -- translate m ≠ 1 to 0 < n!
    apply Ne.symm ∘ Nat.ne_of_lt ∘ Nat.lt_add_of_pos_left
    exact factorial_pos n

  -- p is the prime we are looking for, we just have to show it satisfies
  -- the conditions of the proof
  use p

  -- we already have p is prime, refine the And and we will prove p ≥ n
  refine And.intro ?_ p_prime

  -- show by contradiction that p cannot be < n
  by_contra! p_lt_n

  -- p divides n! + 1 by construction, it is the min prime factor of it
  have p_div_n_fact_plus_one : p ∣ factorial n + 1 := Nat.minFac_dvd m

  -- p divides n! because, by assumption, p < n
  have p_div_n_fact : p ∣ factorial n := by
    -- all 0 < p ∧ p ≤ n divide n!
    refine Nat.dvd_factorial ?_ (Nat.le_of_lt p_lt_n)
    -- show that 0 < p by contradiction
    by_contra! p_le_zero
    -- if p == 0, then p_prime shows that 0 is prime
    rw [eq_zero_of_le_zero p_le_zero] at p_prime
    -- 0 isn't prime!
    apply Nat.not_prime_zero p_prime

  -- with p ∣ n! and p ∣ n! + 1, p must divide 1
  have p_div_one : p ∣ 1 :=
    (Nat.dvd_add_iff_right p_div_n_fact).mpr p_div_n_fact_plus_one

  -- finally, we can show that p ≥ n since p is prime and divides one,
  -- a contradiction
  exact Nat.Prime.not_dvd_one p_prime p_div_one
