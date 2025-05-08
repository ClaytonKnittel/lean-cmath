import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.Linarith

def PrimePowerExp (p exp n : ℕ) := p.Prime ∧ p ^ exp = n
def PrimePower (p n : ℕ) := ∃ exp, PrimePowerExp p exp n
def IsPrimePower (n : ℕ) := ∃ p, PrimePower p n

theorem pp_is_pp {n p : ℕ} (hn : PrimePower p n) : IsPrimePower n := by
  exists p

namespace PrimePower

theorem gt_zero {n : ℕ} (hn : IsPrimePower n) : 0 < n := by
  let ⟨_, ⟨_, ⟨p_prime, n_eq_p_exp⟩⟩⟩ := hn
  rw [← n_eq_p_exp]
  exact Nat.pow_pos p_prime.pos

theorem ne_zero {n : ℕ} (hn : IsPrimePower n) : n ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (gt_zero hn)

theorem one_factor {n p e : ℕ} (n_ne_0 : n ≠ 0) (p_prime : p.Prime)
    : PrimePowerExp p e n ↔ n.factorization = Finsupp.single p e := by
  have pp_has_one_factor : PrimePowerExp p e n → n.factorization = Finsupp.single p e := by
    intro h
    let ⟨p_prime, n_eq_p_exp⟩ := h
    rw [← n_eq_p_exp]
    exact Nat.Prime.factorization_pow p_prime

  have one_factor_is_pp : n.factorization = Finsupp.single p e → PrimePowerExp p e n := by
    have p_e_ne_0 : p ^ e ≠ 0 := pow_ne_zero e (Nat.Prime.ne_zero p_prime)

    intro h
    let x : (p ^ e).factorization = Finsupp.single p e :=
      Nat.Prime.factorization_pow p_prime
    rw [← x] at h
    let same_factorizations : ∀ q, n.factorization q = (p ^ e).factorization q :=
      fun q => congrArg (· q) h
    let y := Nat.eq_of_factorization_eq n_ne_0 p_e_ne_0 same_factorizations
    exact ⟨p_prime, y.symm⟩

  exact ⟨pp_has_one_factor, one_factor_is_pp⟩

theorem dvd_is_pp {n p m : ℕ} (hn : PrimePower p n) (h : m ∣ n)
    : PrimePower p m := by
  have n_ne_0 : n ≠ 0 := ne_zero (pp_is_pp hn)
  have m_ne_0 : m ≠ 0 := ne_zero_of_dvd_ne_zero n_ne_0 h

  let ⟨exp, ⟨p_prime, n_eq_p_exp⟩⟩ := hn
  let h₁ : n.factorization = Finsupp.single p exp :=
    (one_factor n_ne_0 p_prime).mp ⟨p_prime, n_eq_p_exp⟩
  let h₂ : m.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd m_ne_0 n_ne_0).mpr h
  let h₃ : ∀ q ≠ p, m.factorization q = 0 := by
    intro q q_ne_p
    have n_fact_0 : n.factorization q = 0 := by
      rw [h₁]
      exact Finsupp.single_eq_of_ne q_ne_p.symm
    let h := h₂ q
    rw [n_fact_0] at h
    exact Nat.eq_zero_of_le_zero h

  let m_exp := m.factorization p
  let h : m.factorization = Finsupp.single p m_exp := Finsupp.ext fun q => by
    by_cases hp : q = p
    · rw [hp, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne, h₃ q hp]
      exact hp ∘ Eq.symm

  exists m_exp
  exact (one_factor m_ne_0 p_prime).mpr h
