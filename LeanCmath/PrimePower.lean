import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.Linarith

def PrimePowerExp (p exp n : ℕ) := p.Prime ∧ p ^ exp = n
def PrimePower (p n : ℕ) := ∃ exp, PrimePowerExp p exp n
def IsPrimePower (n : ℕ) := ∃ p, PrimePower p n

theorem ppe_is_pp {n p e : ℕ} (hn : PrimePowerExp p e n) : IsPrimePower n :=
  ⟨p, e, hn⟩

theorem pp_is_pp {n p : ℕ} (hn : PrimePower p n) : IsPrimePower n :=
  ⟨p, hn⟩

namespace PrimePower

theorem gt_zero {n : ℕ} (hn : IsPrimePower n) : 0 < n := by
  let ⟨_, ⟨_, ⟨p_prime, h⟩⟩⟩ := hn
  exact h.symm ▸ Nat.pow_pos p_prime.pos

theorem ne_zero {n : ℕ} (hn : IsPrimePower n) : n ≠ 0 :=
  (gt_zero hn).ne'

theorem one_factor {n p e : ℕ} (n_ne_0 : n ≠ 0) (p_prime : p.Prime) :
    PrimePowerExp p e n ↔ n.factorization = Finsupp.single p e :=
  ⟨
    fun ⟨_, h⟩ => h ▸ Nat.Prime.factorization_pow p_prime,
    fun h : n.factorization = (Finsupp.single p e) => by
      have : n = p ^ e :=
        Nat.eq_of_factorization_eq
          n_ne_0
          (pow_ne_zero _ p_prime.ne_zero)
          (fun q => congrArg (· q) (h ▸ (Nat.Prime.factorization_pow p_prime).symm))
      exact ⟨p_prime, this.symm⟩
  ⟩

theorem pp_fact_is_single {n p e : ℕ} (hn : PrimePowerExp p e n)
    : n.factorization = Finsupp.single p e :=
  let ⟨pp, _⟩ := hn
  ((one_factor ∘ ne_zero ∘ ppe_is_pp) hn pp).mp hn

theorem dvd_is_pp {n p m : ℕ} (hn : PrimePower p n) (h : m ∣ n)
    : PrimePower p m := by
  have n_ne_0 : n ≠ 0 := ne_zero (pp_is_pp hn)
  have m_ne_0 : m ≠ 0 := ne_zero_of_dvd_ne_zero n_ne_0 h

  let ⟨exp, ⟨p_prime, n_eq_p_exp⟩⟩ := hn

  have m_le_n : m.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd m_ne_0 n_ne_0).mpr h

  have m_fac_0_except_at_p : ∀ q ≠ p, m.factorization q = 0 := by
    intro q q_ne_p
    have n_fact_0 : n.factorization q = 0 := by
      rw [pp_fact_is_single ⟨p_prime, n_eq_p_exp⟩]
      exact Finsupp.single_eq_of_ne q_ne_p.symm
    let h := m_le_n q
    rw [n_fact_0] at h
    exact Nat.eq_zero_of_le_zero h

  let m_exp := m.factorization p
  let h : m.factorization = Finsupp.single p m_exp := Finsupp.ext fun q => by
    by_cases hp : q = p
    · rw [hp, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne, m_fac_0_except_at_p q hp]
      exact hp ∘ Eq.symm

  exists m_exp
  exact (one_factor m_ne_0 p_prime).mpr h

theorem dvd_is_pp' {n p m : ℕ} (hn : PrimePower p n) (h : m ∣ n)
    : PrimePower p m := by
  let ⟨e, ⟨pp, _⟩⟩ := hn
  let n_ne_0 := ne_zero (pp_is_pp hn)
  let m_ne_0 := ne_zero_of_dvd_ne_zero n_ne_0 h
  let le_fact := (Nat.factorization_le_iff_dvd m_ne_0 n_ne_0).mpr h
  let m_exp := m.factorization p
  have : ∀ q ≠ p, m.factorization q = 0 :=
    sorry
  let m_fact_eq : m.factorization = Finsupp.single p m_exp :=
    sorry
  exact ⟨m_exp, (one_factor m_ne_0 pp).mpr m_fact_eq⟩
