import Mathlib.Data.Nat.Prime.Defs
import Init.Data.List.Basic
import Mathlib.Data.List.Prime
import Mathlib.Data.Nat.Factors

def primeFactorsList : ℕ → List ℕ
  | 0 => []
  | 1 => []
  | k + 2 =>
    let m := (k + 2).minFac
    m :: primeFactorsList ((k + 2) / m)
decreasing_by exact Nat.factors_lemma

-- def x : ℕ → Prop := fun (x : Nat) => x.Prime
lemma zero_le (n : ℕ) : 0 <= n := by
  exact Nat.zero_le n

def x : 0 <= 1 := zero_le 1

lemma euclid_lemma {p a b : ℕ} (pp : p.Prime) (h : p ∣ a * b): (p ∣ a) ∨ (p ∣ b) := by
  sorry

theorem primeFactorList_unique {n : ℕ} {ps : List ℕ} (h₁ : ps.prod = n) (h₂ : ∀ p ∈ ps, p.Prime) :
    ps.Perm n.primeFactorsList := by
  exact n.primeFactorsList_unique h₁ h₂
