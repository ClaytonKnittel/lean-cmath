import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.Linarith

def ConsecutiveFactors (n a b : ℕ) :=
  a ∣ n ∧ b ∣ n ∧ a < b ∧ ¬∃ c, (c ∣ n ∧ a < c ∧ c < b)

theorem inv_cons_factors {n a b x y : ℕ} (ha : n = x * a)
    (hb : n = y * b) (h : ConsecutiveFactors n a b)
    : ConsecutiveFactors n y x :=
  sorry

-- theorem minFac_cons_factor {n p : ℕ} (hp : p = n.minFac)

def Dividable (n : ℕ) :=
  ∀ {a b c : ℕ},
    ConsecutiveFactors n a b ∧ ConsecutiveFactors n b c
    → a ∣ b + c

lemma cons_are_p_apart {x y p n : ℕ} (p_prime : p.Prime)
    (hn : ∃ k, 0 < k ∧ p ^ k = n)
    : ConsecutiveFactors n x y → x * p = y := by
  let ⟨e, ⟨e_gt_0, n_eq_p_exp⟩⟩ := hn
  intro ⟨hx, ⟨hy, ⟨x_lt_y, h⟩⟩⟩
  let ⟨x_exp, ⟨_, x_eq_p_exp⟩⟩ := (Nat.dvd_prime_pow p_prime).mp (n_eq_p_exp ▸ hx)
  let ⟨y_exp, ⟨_, y_eq_p_exp⟩⟩ := (Nat.dvd_prime_pow p_prime).mp (n_eq_p_exp ▸ hy)

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
    rw [n_eq, y_eq_p_exp, y_eq, add_assoc, Nat.pow_add, mul_assoc,
        mul_comm _ b]

  rw [x_eq_p_exp, y_eq_p_exp, ← exp_eq]
  exact rfl

lemma pp_is_dividable {n : ℕ} : IsPrimePow n → Dividable n :=
  fun ⟨p, e, hp, hpp⟩ _ _ _ ⟨xy_cons, yz_cons⟩ => by
    let y_subs := cons_are_p_apart hp.nat_prime ⟨e, hpp⟩ xy_cons
    let z_subs := cons_are_p_apart hp.nat_prime ⟨e, hpp⟩ yz_cons
    rw [← z_subs, ← y_subs]
    exists p + p ^ 2
    linarith

lemma dividable_is_pp {n : ℕ} (h : n > 1) : Dividable n → IsPrimePow n := by
  sorry

theorem P1 : ∀ n > 1, IsPrimePow n ↔ Dividable n :=
  fun _ h => ⟨pp_is_dividable, dividable_is_pp h⟩
