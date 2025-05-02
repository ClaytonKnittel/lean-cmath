import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs

/--
Proof that `n!` is divisible by all nonzero integers `m ≤ n`.
-/
theorem all_n_divide_fact_n : ∀ {n m : ℕ}, m ≠ 0 ∧ m ≤ n → m ∣ Nat.factorial n := by
  intro n m ⟨m_ne_zero, m_le_n⟩
  match n with
  | .zero => exact (False.elim ∘ m_ne_zero ∘ Nat.le_zero.mp) m_le_n
  | .succ n_pred =>
    cases m_le_n with
    | refl =>
      use Nat.factorial n_pred
      rfl
    | step m_le_n_pred =>
      rw [Nat.factorial_succ]
      apply Nat.dvd_mul_left_of_dvd
      exact all_n_divide_fact_n (And.intro m_ne_zero m_le_n_pred)

theorem all_n_divide_fact_n' : ∀ {n m : ℕ}, m ≠ 0 ∧ m ≤ n → m ∣ Nat.factorial n := by
  exact And.elim (Nat.dvd_factorial ∘ Nat.zero_lt_of_ne_zero)

theorem no_n_divides_fact_n_plus_1 : ∀ {n m : ℕ}, 2 ≤ m ∧ m ≤ n → ¬ m ∣ Nat.factorial n + 1 := by
  intro n m h
  match h with
  | ⟨two_le_m, m_le_n⟩ =>
    intro m_div_n_fact_plus_1
    have zero_ne_m := Nat.ne_zero_of_lt two_le_m
    let m_div_n_fact := all_n_divide_fact_n (And.intro zero_ne_m m_le_n)
    have m_le_one : m ≤ 1 := by apply?
    sorry

theorem infinitude_of_primes : ∀ (n : ℕ), ∃ p ≥ n, Nat.Prime p := by
  intro n
  let f := Nat.factorial n + 1
  let p_greater_n := Nat.le_succ_of_le (Nat.self_le_factorial n)

  have f_ge_2 : 2 ≤ f := by
    let n_fact_pos := Nat.factorial_pos n
    sorry
  have f_min_fac_gt_n : Nat.minFac f > n := by
    exact no_n_divides_fact_n_plus_1 (And.intro f_ge_2 sorry)

  use f
  exact And.intro p_greater_n sorry
