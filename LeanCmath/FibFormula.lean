import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Sqrt

noncomputable def φ : Real := (1 + √5) / 2
noncomputable def φ₂ : Real := (1 - √5) / 2

theorem phi_sq : φ + 1 = φ * φ := by
  unfold φ
  field_simp [mul_add, add_mul]
  linarith

theorem phi2_sq : φ₂ + 1 = φ₂ * φ₂ := by
  unfold φ₂
  field_simp [sub_mul, mul_sub]
  linarith

theorem fib_formula : ∀ n, Nat.fib n = (φ ^ n - φ₂ ^ n) / Real.sqrt 5 := by
  intro n
  cases n with
  | zero => simp
  | succ n_minus_1 =>
    cases n_minus_1 with
    | zero =>
      unfold φ φ₂
      field_simp [fib_formula Nat.zero]
    | succ n =>
      field_simp [Nat.fib_add_two, fib_formula n, fib_formula (n + 1), pow_add _ n 1, mul_comm]
      calc
        _ = (φ + 1) * φ ^ n - (φ₂ + 1) * (φ₂) ^ n := ?_
        _ = φ ^ (n + 2) - (φ₂) ^ (n + 2) := ?_
      . linarith
      . have sq : ∀ (n : ℝ), n * n = n ^ 2 := by
          intro n
          rw [← pow_one n, ← pow_add]
          field_simp
        field_simp [phi_sq, phi2_sq, sq φ, sq φ₂, ← pow_add, add_comm 2, Mathlib.Tactic.RingNF.add_neg]
