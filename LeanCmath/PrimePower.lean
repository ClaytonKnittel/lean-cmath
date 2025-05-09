import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.Linarith

open Finsupp (single single_eq_same single_eq_of_ne)
open Nat (eq_of_factorization_eq eq_zero_of_le_zero factorization_le_iff_dvd pow_pos Prime)

def PrimePowerExp (p exp n : ℕ) := p.Prime ∧ p ^ exp = n
def PrimePower (p n : ℕ) := ∃ exp, PrimePowerExp p exp n
def IsPrimePower (n : ℕ) := ∃ p, PrimePower p n

theorem ppe_is_pp {n p e : ℕ} (hn : PrimePowerExp p e n) : IsPrimePower n :=
  ⟨p, e, hn⟩

theorem pp_is_pp {n p : ℕ} (hn : PrimePower p n) : IsPrimePower n :=
  ⟨p, hn⟩

namespace PrimePower

theorem gt_zero {n : ℕ} (hn : IsPrimePower n) : 0 < n :=
  let ⟨_, ⟨_, ⟨p_prime, h⟩⟩⟩ := hn
  h.symm ▸ pow_pos p_prime.pos

theorem ne_zero {n : ℕ} (hn : IsPrimePower n) : n ≠ 0 :=
  (gt_zero hn).ne'

theorem one_factor {n p e : ℕ} (n_ne_0 : n ≠ 0) (p_prime : p.Prime) :
    PrimePowerExp p e n ↔ n.factorization = single p e :=
  ⟨
    fun ⟨_, h⟩ => h ▸ Prime.factorization_pow p_prime,
    fun h : n.factorization = (single p e) => by
      have : n = p ^ e :=
        eq_of_factorization_eq
          n_ne_0
          (pow_ne_zero _ p_prime.ne_zero)
          (fun q => congrArg (· q) (h ▸ (Prime.factorization_pow p_prime).symm))
      exact ⟨p_prime, this.symm⟩
  ⟩

theorem pp_fact_is_single {n p e : ℕ} (hn : PrimePowerExp p e n)
    : n.factorization = single p e :=
  let ⟨pp, _⟩ := hn
  ((one_factor ∘ ne_zero ∘ ppe_is_pp) hn pp).mp hn

theorem dvd_is_pp {n p m : ℕ} (hn : PrimePower p n) (h : m ∣ n)
    : PrimePower p m :=
  let ⟨_, ⟨p_prime, n_eq_p_exp⟩⟩ := hn
  let n_ne_0 := ne_zero (pp_is_pp hn)
  let m_ne_0 := ne_zero_of_dvd_ne_zero n_ne_0 h
  let le_fact := (factorization_le_iff_dvd m_ne_0 n_ne_0).mpr h
  let m_exp := m.factorization p
  let n_fact := ((one_factor n_ne_0 p_prime).mp ⟨p_prime, n_eq_p_exp⟩)

  let n_fact_0 : ∀ q ≠ p, n.factorization q = 0 :=
    fun q h =>
      Eq.trans
        (congrArg (· q) n_fact)
        (single_eq_of_ne h.symm)
  let m_fact_eq : m.factorization = single p m_exp :=
    Finsupp.ext fun q =>
      if h : p = q then
        h ▸ single_eq_same.symm
      else
        (single_eq_of_ne h : (single p m_exp) q = 0).symm ▸
          eq_zero_of_le_zero (n_fact_0 q (h ∘ Eq.symm) ▸ le_fact q)

  ⟨m_exp, (one_factor m_ne_0 p_prime).mpr m_fact_eq⟩
