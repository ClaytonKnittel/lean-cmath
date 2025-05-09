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

lemma cons_are_p_apart {x y p n : ℕ} (hn : PrimePower p n)
    : ConsecutiveFactors n x y → x * p = y := by
  let ⟨e, ⟨p_prime, n_eq_p_exp⟩⟩ := hn
  intro ⟨hx, ⟨hy, ⟨x_lt_y, h⟩⟩⟩
  let ⟨x_exp, ⟨_, x_eq_p_exp⟩⟩ := PrimePower.dvd_is_pp hn hx
  let ⟨y_exp, ⟨_, y_eq_p_exp⟩⟩ := PrimePower.dvd_is_pp hn hy

  have exp_lt : x_exp < y_exp :=
    (Nat.pow_lt_pow_iff_right p_prime.one_lt).mp
      (x_eq_p_exp ▸ y_eq_p_exp ▸ x_lt_y)

  have exp_eq : x_exp + 1 = y_exp := by
    by_contra ne
    apply h
    have lt := Nat.lt_of_le_of_ne exp_lt ne

    exists p ^ (x_exp + 1)
    refine And.intro ?_ ⟨
        x_eq_p_exp ▸ Nat.pow_lt_pow_succ p_prime.one_lt,
        y_eq_p_exp ▸ Nat.pow_lt_pow_of_lt p_prime.one_lt lt
      ⟩

    let ⟨b, n_eq⟩ := hy
    let ⟨k, y_eq⟩ := Nat.exists_eq_add_of_lt lt
    exists b * p ^ (k + 1)
    rw [n_eq, ← y_eq_p_exp, y_eq, add_assoc, Nat.pow_add, mul_assoc,
        mul_comm _ b]

  rw [← x_eq_p_exp, ← y_eq_p_exp, ← exp_eq]
  exact rfl

lemma pp_is_dividable {n : ℕ} : IsPrimePower n → Dividable n :=
  fun ⟨p, hp⟩ _ _ _ ⟨xy_cons, yz_cons⟩ => by
    let y_subs := cons_are_p_apart hp xy_cons
    let z_subs := cons_are_p_apart hp yz_cons
    rw [← z_subs, ← y_subs]
    exists p + p ^ 2
    linarith

lemma dividable_is_pp {n : ℕ} (h : n > 1) : Dividable n → IsPrimePower n := by
  sorry

theorem P1 : ∀ n > 1, IsPrimePower n ↔ Dividable n :=
  fun _ h => ⟨pp_is_dividable, dividable_is_pp h⟩
