import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

lemma mul_cmp_compl {a b x y : ℕ} (hab : a < b) (hy : 0 < y)
    (h : a * x = b * y) : y < x :=
  Nat.lt_of_mul_lt_mul_left
    (h ▸ Nat.mul_lt_mul_of_pos_right hab hy)

theorem p_succ_fact_zero {p : ℕ} (hp : p.Prime)
    : (p + 1).factorization p = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  exact hp.not_dvd_one ∘ Nat.dvd_add_self_left.mp

def ConsecutiveFactors (n a b : ℕ) :=
  a ∣ n ∧ b ∣ n ∧ a < b ∧ ¬∃ c, (c ∣ n ∧ a < c ∧ c < b)

theorem not_pow_cons_factors_other_prime {p e c : ℕ} (hp : p.Prime)
    (c_gt_e : c > p ^ e) (c_lt_p_e_plus1 : c < p ^ (e + 1))
    : ∃ q ≠ p, q.Prime ∧ q ∣ c := by
  by_contra h
  have : ∃ c_e, c.factorization = Finsupp.single p c_e := by
    have {q : ℕ} (q_ne_p : q ≠ p) : c.factorization q = 0 := by
      refine Or.elim (em q.Prime) ?_ (Nat.factorization_eq_zero_of_non_prime c ·)
      intro q_prime
      by_contra h₂
      exact h ⟨q, q_ne_p, q_prime, Nat.dvd_of_factorization_pos h₂⟩
    exists c.factorization p
    apply Finsupp.ext
    intro q
    by_cases hq : q = p
    . rw [hq, Finsupp.single_eq_same]
    . rw [Finsupp.single_eq_of_ne (hq ∘ Eq.symm)]
      exact this hq
  obtain ⟨c_e, hf⟩ := this

  let c_is_pow_p :=
    Nat.eq_of_factorization_eq
      (Nat.ne_zero_of_lt c_gt_e)
      (pow_ne_zero c_e hp.ne_zero)
      fun p => (congrArg (· p) (Nat.Prime.factorization_pow hp ▸ hf))

  have gt_e : c_e ≥ e + 1 :=
    (Nat.pow_lt_pow_iff_right hp.one_lt).mp (c_is_pow_p ▸ c_gt_e)
  have lt_e_plus1 : c_e < e + 1 :=
    (Nat.pow_lt_pow_iff_right hp.one_lt).mp (c_is_pow_p ▸ c_lt_p_e_plus1)
  exact Nat.le_lt_asymm gt_e lt_e_plus1

theorem inv_cons_factors {n a b x y : ℕ} (hn : 0 < n) (ha : n = a * x)
    (hb : n = b * y) (h : ConsecutiveFactors n a b)
    : ConsecutiveFactors n y x := by
  have div_n_ne_0 {a b : ℕ} (h : n = a * b) : 0 < b :=
    Nat.zero_lt_of_ne_zero ((Nat.mul_ne_zero_iff).mp (h ▸ hn.ne).symm).right

  let ⟨_, _, a_lt_b, no_c⟩ := h
  have y_lt_x := mul_cmp_compl a_lt_b (div_n_ne_0 hb) (ha ▸ hb)

  let ha := Nat.mul_comm _ _ ▸ ha
  let hb := Nat.mul_comm _ _ ▸ hb
  refine ⟨⟨b, hb⟩, ⟨a, ha⟩, y_lt_x, ?_⟩

  by_contra hc
  let ⟨c, ⟨z, hc⟩, y_lt_c, c_lt_x⟩ := hc
  apply no_c

  exists z
  exact ⟨
    ⟨c, Nat.mul_comm _ _ ▸ hc⟩,
    mul_cmp_compl c_lt_x (div_n_ne_0 ha) (hc ▸ ha),
    mul_cmp_compl y_lt_c (div_n_ne_0 hc) (hc ▸ hb.symm)
  ⟩

theorem minFac_cons_factor {n : ℕ} (hn : 1 < n) (h : ¬IsPrimePow n)
    : ∃ q e,
      q.Prime ∧ q ≠ n.minFac ∧
      ConsecutiveFactors n (n.minFac ^ e) (n.minFac ^ (e + 1)) ∧
      ConsecutiveFactors n (n.minFac ^ (e + 1)) q := by
  have n_ne_0 := Nat.ne_zero_of_lt hn

  let p := n.minFac
  have p_prime : p.Prime := n.minFac_prime (Nat.ne_of_lt hn).symm

  let c := ordCompl[p] n
  have : 1 < c := by sorry
  let q := c.minFac
  have q_prime : q.Prime := c.minFac_prime (Nat.ne_of_lt this).symm
  -- use Nat.le_minFac
  have p_lt_q : p < q := by sorry

  let e_plus1 := min (n.factorization p) (p.log q)
  have : 0 < e_plus1 :=
    lt_min
      (p_prime.factorization_pos_of_dvd
        n_ne_0
        (Nat.minFac_dvd n))
      (by simp [p_lt_q.le, p_prime.one_lt])
  let ⟨e, he⟩ := Nat.exists_add_one_eq.mpr this

  exists q, e
  refine ⟨q_prime, (Nat.ne_of_lt p_lt_q).symm, ?_⟩

  have {e : ℕ} : e ≤ n.factorization p → p ^ e ∣ n :=
    Nat.multiplicity_eq_factorization p_prime n_ne_0
      ▸ pow_dvd_of_le_multiplicity
  have p_e_dvd_n : p ^ e ∣ n :=
    (he ▸ this ∘ Nat.le_of_add_right_le) (Nat.min_le_left _ _)
  have p_e_succ_dvd_n : p ^ (e + 1) ∣ n :=
    he ▸ this (Nat.min_le_left _ _)

  have p_e_plus1_lt_q : p ^ (e + 1) < q := sorry
  have p_only_fac_lt_q {r : ℕ} (r_prime : r.Prime)
      (r_lt_q : r < q) (r_dvd_n : r ∣ n)
      : r = p :=
    sorry
  have lt_q_pow_p {x : ℕ} (x_lt_q : x < q) (x_dvd_n : x ∣ n)
      : ∃ e, x.factorization = Finsupp.single p e :=
    sorry
  have lt_q_pow_p' {x : ℕ} (x_lt_q : x < q) (x_dvd_n : x ∣ n)
      : ∃ e, x = p ^ e := by
    let ⟨e, he⟩ := lt_q_pow_p x_lt_q x_dvd_n
    let x2 := Nat.Prime.factorization_pow p_prime ▸ he
    sorry
    -- exact
    --   Nat.eq_of_factorization_eq
    --     _ _
    --     (Nat.Prime.factorization_pow p_prime ▸ he)

  have : ConsecutiveFactors n (p ^ e) (p ^ (e + 1)) := by
    refine ⟨p_e_dvd_n, p_e_succ_dvd_n, Nat.pow_lt_pow_succ p_prime.one_lt, ?_⟩
    by_contra h
    obtain ⟨d, d_dvd_n, d_gt_p_e, d_lt_p_e_plus1⟩ := h
    let ⟨r, r_ne_p, r_prime, r_dvd_d⟩ :=
      not_pow_cons_factors_other_prime p_prime d_gt_p_e d_lt_p_e_plus1
    have : r < q := sorry
    exact r_ne_p (p_only_fac_lt_q r_prime this (r_dvd_d.trans d_dvd_n))
  refine ⟨this, ?_⟩

  have : ConsecutiveFactors n (p ^ (e + 1)) q := by
    refine ⟨
        p_e_succ_dvd_n,
        c.minFac_dvd.trans (Nat.ordCompl_dvd n p),
        p_e_plus1_lt_q,
        ?_
      ⟩
    by_contra h
    obtain ⟨d, d_dvd_n, d_gt_p_e_plus1, d_lt_q⟩ := h
    let ⟨d_e, he⟩ := lt_q_pow_p d_lt_q d_dvd_n
    have : d_e > e + 1 := sorry
    let xx :=
      Nat.Prime.factorization_pow p_prime ▸
        (Nat.factorization_le_iff_dvd
          (pow_ne_zero d_e p_prime.ne_zero)
          n_ne_0).mpr
        -- d_dvd_n
    sorry
  exact this

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
  let p_prime := (n.minFac_prime (Nat.ne_of_lt n_gt_1).symm)

  by_contra hn
  let ⟨q, e, q_prime, q_ne_p, cxy, cyz⟩ := minFac_cons_factor n_gt_1 hn
  let ⟨x_div_n, y_div_n, _⟩ := cxy
  let ⟨_, z_div_n, _⟩ := cyz
  let ⟨_, hx⟩ := x_div_n
  let ⟨_, hy⟩ := y_div_n
  let ⟨_, hz⟩ := z_div_n

  have n_gt_0 := Nat.zero_lt_of_lt n_gt_1
  let ⟨f, h⟩ :=
    hd ⟨
      inv_cons_factors n_gt_0 hy hz cyz,
      inv_cons_factors n_gt_0 hx hy cxy
    ⟩

  have h : p ^ (e + 1) ∣ q * (p + 1) := by
    let h : p ^ (e + 1) * q * _ = p ^ (e + 1) * q * _ :=
      congrArg (p ^ (e + 1) * q * ·) h
    exists f

    have : Function.Injective (· * n) :=
      fun _ _ h => Nat.mul_right_cancel (Nat.zero_lt_of_lt n_gt_1) h
    apply_fun (· * n)
    dsimp

    rw [add_comm, mul_add, add_mul, mul_one]
    nth_rw 1 [hy]
    nth_rw 2 [hx]
    nth_rw 3 [hz]

    rw [mul_assoc, ← Nat.mul_add q, ← mul_assoc, ← Nat.pow_add_one',
        ← Nat.mul_add, ← mul_assoc, mul_comm q, mul_assoc _ f, mul_rotate' f,
        ← mul_assoc]
    exact h

  have : 0 < (p ^ (e + 1)).factorization p :=
    (
      (congrArg (· n.minFac) p_prime.factorization_pow).trans
        Finsupp.single_eq_same
    ).symm ▸ Nat.zero_lt_succ e
  apply Nat.not_le_of_gt this

  have : (q * (p + 1)).factorization p = 0 := by
    rw [Nat.factorization_mul q_prime.ne_zero p.succ_ne_zero]
    dsimp
    rw [q_prime.factorization, Finsupp.single_eq_of_ne q_ne_p]
    rw [p_succ_fact_zero p_prime]
  exact this ▸ (
      Nat.factorization_le_iff_dvd
        (pow_ne_zero (e + 1) p_prime.ne_zero)
        (Nat.mul_ne_zero q_prime.ne_zero p.succ_ne_zero)
    ).mpr h p

theorem P1 : ∀ n > 1, IsPrimePow n ↔ Dividable n :=
  fun _ h => ⟨pp_is_dividable, dividable_is_pp h⟩
