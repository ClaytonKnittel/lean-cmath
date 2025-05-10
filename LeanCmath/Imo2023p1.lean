import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

def ConsecutiveFactors (n a b : ℕ) :=
  a ∣ n ∧ b ∣ n ∧ a < b ∧ ¬∃ c, (c ∣ n ∧ a < c ∧ c < b)

theorem inv_cons_factors {n a b x y : ℕ} (ha : n = a * x)
    (hb : n = b * y) (h : ConsecutiveFactors n a b)
    : ConsecutiveFactors n y x :=
  sorry

theorem minFac_cons_factor {n : ℕ} (hn : ¬IsPrimePow n)
    : ∃ q e,
      q.Prime ∧
      ConsecutiveFactors n (n.minFac ^ e) (n.minFac ^ (e + 1)) ∧
      ConsecutiveFactors n (n.minFac ^ (e + 1)) q :=
  sorry

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

lemma pp_is_dividable {n : ℕ} : IsPrimePow n → Dividable n := by
  intro ⟨p, e, hp, hpp⟩ _ _ _ ⟨xy_cons, yz_cons⟩
  let y_subs := cons_are_p_apart hp.nat_prime ⟨e, hpp⟩ xy_cons
  let z_subs := cons_are_p_apart hp.nat_prime ⟨e, hpp⟩ yz_cons
  rw [← z_subs, ← y_subs]
  exists p + p ^ 2
  linarith

lemma dividable_is_pp {n : ℕ} (n_gt_1 : n > 1) : Dividable n → IsPrimePow n := by
  intro hd
  let p := n.minFac
  by_contra hn
  let ⟨q, e, q_prime, cxy, cyz⟩ := minFac_cons_factor hn
  let ⟨x_div_n, y_div_n, _⟩ := cxy
  let ⟨_, z_div_n, _⟩ := cyz
  let ⟨x_inv, hx⟩ := x_div_n
  let ⟨y_inv, hy⟩ := y_div_n
  let ⟨z_inv, hz⟩ := z_div_n
  let cyx_inv := inv_cons_factors hx hy cxy
  let czy_inv := inv_cons_factors hy hz cyz

  let ⟨f, h⟩ := hd ⟨czy_inv, cyx_inv⟩

  let h : p ^ (e + 1) ∣ q * (1 + p) := by
    let h : p ^ (e + 1) * q * _ = p ^ (e + 1) * q * _ :=
      congrArg (p ^ (e + 1) * q * ·) h
    exists f

    have : Function.Injective (· * n) :=
      fun _ _ h => Nat.mul_right_cancel (Nat.zero_lt_of_lt n_gt_1) h
    apply_fun (· * n)
    dsimp

    rw [mul_add, add_mul, mul_one]
    nth_rw 1 [hy]
    nth_rw 2 [hx]
    nth_rw 3 [hz]

    rw [mul_assoc, ← Nat.mul_add q, ← mul_assoc, ← Nat.pow_add_one',
        ← Nat.mul_add, ← mul_assoc, mul_comm q, mul_assoc _ f, mul_rotate' f,
        ← mul_assoc]
    exact h

  have h₁ : 0 < (p ^ (e + 1)).factorization p := by
    let q : (p ^ (e + 1)).factorization = _ :=
      (n.minFac_prime (Nat.ne_of_lt n_gt_1).symm).factorization_pow
    let r := congrArg (· n.minFac) q
    dsimp at r
    let s : (p ^ (e + 1)).factorization p = e + 1 := Finsupp.single_eq_same ▸ r
    exact
      (
        Finsupp.single_eq_same ▸
        (congrArg (· p)
         (n.minFac_prime (Nat.ne_of_lt n_gt_1).symm).factorization_pow)
      )
      ▸ Nat.zero_lt_succ e
  sorry

theorem P1 : ∀ n > 1, IsPrimePow n ↔ Dividable n :=
  fun _ h => ⟨pp_is_dividable, dividable_is_pp h⟩
