import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.Linarith
import LeanCmath.PrimePower

def ConsecutiveFactors (n a b : ℕ) :=
  a ∣ n ∧ b ∣ n ∧ a < b ∧ ¬∃ c, (c ∣ n ∧ a < c ∧ c < b)

def Dividable (n : ℕ) :=
  ∀ {a b c : ℕ},
    ConsecutiveFactors n a b ∧ ConsecutiveFactors n b c
    → a ∣ b + c

lemma pp_is_dividable {n : ℕ} (h : n > 1) : IsPrimePower n → Dividable n := by
  intro pp
  let ⟨p, ⟨exp, ⟨p_prime, n_eq_p_exp⟩⟩⟩ := pp

  have n_gt_0 : 0 < n := Nat.zero_lt_of_lt h

  have cons_are_p_apart {x y : ℕ} : ConsecutiveFactors n x y → x * p = y := by
    intro ⟨hx, ⟨hy, ⟨x_lt_y, h⟩⟩⟩
    by_contra h_contra
    apply h
    exists x * p

    have x_gt_0 : 0 < x := Nat.pos_of_dvd_of_pos hx n_gt_0
    have x_lt_n : x < n := by

      sorry

    have xp_div_n : x * p ∣ n := by sorry
    have xp_gt_x : x * p > x :=
      (Nat.lt_mul_iff_one_lt_right x_gt_0).mpr p_prime.one_lt
    have xp_lt_y : x * p < y := sorry

    exact And.intro xp_div_n (And.intro xp_gt_x xp_lt_y)

  intro x y z ⟨xy_cons, yz_cons⟩
  let y_subs := cons_are_p_apart xy_cons
  let z_subs := cons_are_p_apart yz_cons
  rw [← z_subs, ← y_subs]

  exists p + p ^ 2
  linarith

lemma dividable_is_pp {n : ℕ} (h : n > 1) : Dividable n → IsPrimePower n := by
  sorry

theorem P1 : ∀ n > 1, IsPrimePower n ↔ Dividable n := by
  intro _ h
  exact ⟨pp_is_dividable h, dividable_is_pp h⟩
