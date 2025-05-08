import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.Linarith

def PrimePowerExp (p exp n : ℕ) := p.Prime ∧ p ^ exp = n
def PrimePower (p n : ℕ) := ∃ exp, PrimePowerExp p exp n
def IsPrimePower (n : ℕ) := ∃ p, PrimePower p n

namespace PrimePower

theorem gt_zero {n : ℕ} (hn : IsPrimePower n) : 0 < n := by
  let ⟨_, ⟨_, ⟨p_prime, n_eq_p_exp⟩⟩⟩ := hn
  rw [← n_eq_p_exp]
  exact Nat.pow_pos p_prime.pos

theorem ne_zero {n : ℕ} (hn : IsPrimePower n) : n ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (gt_zero hn)

theorem one_prime_factor {n p q : ℕ} {hn : PrimePower p n}
    (q_prime : q.Prime) (hq : q ∣ n)
    : q = p := by
  let ⟨_, ⟨p_prime, n_eq_p_exp⟩⟩ := hn
  rw [← n_eq_p_exp] at hq
  let q_div_p := Nat.Prime.dvd_of_dvd_pow q_prime hq
  exact (Nat.prime_dvd_prime_iff_eq q_prime p_prime).mp q_div_p

theorem one_prime_factor' {n p q : ℕ} {hn : PrimePower p n}
    (q_prime : q.Prime) (hq : q ≠ p)
    : n.factorization q = 0 := by
  let ⟨_, ⟨p_prime, n_eq_p_exp⟩⟩ := hn
  by_contra!
  sorry

theorem not_pp_has_different_factor {n p : ℕ}
    {p_prime : p.Prime} (n_gt_1 : 1 < n) {hn : ¬PrimePower p n}
    : ∃ q, q.Prime ∧ q ≠ p ∧ q ∣ n := by
  sorry

theorem factors_are_pp {n p a : ℕ} {hn : PrimePower p n}
    (ha : a ∣ n)
    : PrimePower p a := by
  let ⟨exp, ⟨p_prime, n_eq_p_exp⟩⟩ := hn
  -- have s : ∃ q, q.Prime ∧ q ≠ p ∧ q ∣ a := by exact?
  -- let ⟨c, hc⟩ := ha
  rw [← n_eq_p_exp] at ha
  have h1 : ∃q, a = p ^ q :=

  -- have a_is_pow : ∃ pow, a = p ^ pow := by
  --   sorry

theorem one_prime_divides_is_pp {n p : ℕ} (h : ∀ q, q ∣ n → p ∣ q) : PrimePower p n := by
  sorry

theorem pp_divisor_is_pp {n m p : ℕ} {hn : PrimePower p n} (hd : m ∣ n)
    : PrimePower p m := by
  let ⟨p_exp, ⟨p_prime, n_eq_p_exp⟩⟩ := hn

  have m_has_same_factors {q : ℕ} {a : q ∣ m} : q ∣ n := Nat.dvd_trans a hd
  have m_is_pow : ∀ q, q ∣ m → p ∣ q := by
    intro q q_div_m
    by_contra p_ndiv_q
    have exists_other_prime : ∃ p₂ ≠ p, p₂.Prime ∧ p₂ ∣ m := by
      sorry
    sorry

  exact one_prime_divides_is_pp m_is_pow
