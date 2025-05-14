import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factors
import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open FiniteMultiplicity

lemma PrimePow_ne {a b p q : ℕ} (p_prime : p.Prime) (q_prime : q.Prime) (p_ne_q : p ≠ q)
    (ha : ∃ k > 0, p ^ k = a) (hb : ∃ k > 0, q ^ k = b)
    : a ≠ b := by
  obtain ⟨a_k, a_k_ne_0, ha⟩ := ha
  obtain ⟨b_k, b_k_ne_0, hb⟩ := hb
  have a_ne_0 := ha ▸ (Nat.pow_pos (Nat.pos_of_ne_zero p_prime.ne_zero)).ne.symm
  have b_ne_0 := hb ▸ (Nat.pow_pos (Nat.pos_of_ne_zero q_prime.ne_zero)).ne.symm
  let fa := Nat.Prime.factorization_pow p_prime ▸ congrArg Nat.factorization ha
  let fb := Nat.Prime.factorization_pow q_prime ▸ congrArg Nat.factorization hb

  by_contra a_eq_b
  have :=
    (fa ▸ fb ▸ (Finsupp.single_eq_single_iff p q a_k b_k).mp)
      (congrArg Nat.factorization a_eq_b)
  exact
    not_or_intro
      (not_and.mpr fun p_eq_q _ => p_ne_q p_eq_q)
      (not_and.mpr fun a_k_eq_0 _ => a_k_ne_0.ne.symm a_k_eq_0)
      this

lemma dvd_ne_zero {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) : 0 < a :=
  Nat.zero_lt_of_ne_zero (fun ha => hb (zero_dvd_iff.mp (ha ▸ h)))

lemma dvd_n_fact_ne_zero {n r : ℕ} (n_ne_0 : n ≠ 0) (r_prime : r.Prime) (r_dvd_n : r ∣ n)
    : n.factorization r ≠ 0 := by
  by_contra h
  have := (Nat.factorization_eq_zero_iff n r).mp h
  exact match or_assoc.mpr this with
  | .inl h => by
    let x := not_and_or.mpr h
    exact x ⟨r_prime, r_dvd_n⟩
  | .inr h => n_ne_0 h

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
    (c_gt_e : c > p ^ e) (c_lt_p_e_succ : c < p ^ (e + 1))
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
  have lt_e_succ : c_e < e + 1 :=
    (Nat.pow_lt_pow_iff_right hp.one_lt).mp (c_is_pow_p ▸ c_lt_p_e_succ)
  exact Nat.le_lt_asymm gt_e lt_e_succ

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

theorem factorization_prime {n p : ℕ} (h : n.factorization p ≠ 0) : p.Prime := by
  by_cases hp : p.Prime
  . exact hp
  . exact False.elim (h (Nat.factorization_eq_zero_of_non_prime n hp))

theorem minFac_cons_factor {n : ℕ} (hn : 1 < n) (h : ¬IsPrimePow n)
    : ∃ q e,
      q.Prime ∧ q ≠ n.minFac ∧
      ConsecutiveFactors n (n.minFac ^ e) (n.minFac ^ (e + 1)) ∧
      ConsecutiveFactors n (n.minFac ^ (e + 1)) q := by
  have n_ne_0 := Nat.ne_zero_of_lt hn

  let p := n.minFac
  have p_prime : p.Prime := n.minFac_prime (Nat.ne_of_lt hn).symm

  let c := ordCompl[p] n
  have c_gt_one : 1 < c := by sorry
  have c_dvd_n := Nat.ordCompl_dvd n p
  let q := c.minFac
  have q_prime : q.Prime := c.minFac_prime (Nat.ne_of_lt c_gt_one).symm

  have p_unique {r : ℕ} (r_lt_q : r < q) (r_ne_p : r ≠ p) : n.factorization r = 0 := by
    let c_n_fact_eq : c.factorization r = n.factorization r :=
      (Finsupp.erase_ne r_ne_p : _ = n.factorization r) ▸
        (congrArg (· r) (Nat.factorization_ordCompl n p))
    have : c.factorization r = 0 := by
      by_contra h
      exact
        Nat.le_lt_asymm
          (Nat.minFac_le_of_dvd
            (Nat.succ_le_of_lt (factorization_prime h).one_lt)
            (Nat.dvd_of_factorization_pos h))
          r_lt_q
    exact c_n_fact_eq ▸ this

  have p_lt_q : p < q := by
    have q_dvd_c : q ∣ c := Nat.minFac_dvd c
    have q_dvd_n : q ∣ n := Nat.dvd_trans q_dvd_c c_dvd_n
    have c_fact_q : c.factorization q ≠ 0 := by
      by_contra h
      exact
        Or.elim
          ((Nat.factorization_eq_zero_iff _ _).mp h)
          (· q_prime)
          (Or.elim · (· q_dvd_c) (Nat.ne_zero_of_lt c_gt_one ·))
    have : p ≠ q := by
      let c_fact_def := congrArg (· q) (Nat.factorization_ordCompl n p)
      by_contra h
      have : (n / p ^ n.factorization p).factorization q = (Finsupp.erase p n.factorization) p := by
        exact h ▸ c_fact_def
      exact c_fact_q ((Finsupp.erase_same : _ = 0) ▸ this)
    have p_le_q : p ≤ q := Nat.minFac_le_of_dvd q_prime.one_lt q_dvd_n
    exact
      Nat.lt_of_le_of_ne
        (Nat.minFac_le_of_dvd q_prime.one_lt q_dvd_n)
        this

  let e_succ := min (n.factorization p) (p.log q)
  have e_succ_ne_0 : 0 < e_succ :=
    lt_min
      (p_prime.factorization_pos_of_dvd
        n_ne_0
        (Nat.minFac_dvd n))
      (by simp [p_lt_q.le, p_prime.one_lt])
  let ⟨e, he⟩ := Nat.exists_add_one_eq.mpr e_succ_ne_0

  exists q, e
  refine ⟨q_prime, (Nat.ne_of_lt p_lt_q).symm, ?_⟩

  have {e : ℕ} : e ≤ n.factorization p → p ^ e ∣ n :=
    Nat.multiplicity_eq_factorization p_prime n_ne_0
      ▸ pow_dvd_of_le_multiplicity
  have p_e_dvd_n : p ^ e ∣ n :=
    (he ▸ this ∘ Nat.le_of_add_right_le) (Nat.min_le_left _ _)
  have p_e_succ_dvd_n : p ^ (e + 1) ∣ n :=
    he ▸ this (Nat.min_le_left _ _)

  have p_e_succ_lt_q : p ^ (e + 1) < q := by
    let p_e_succ_le_q :=
      (Nat.pow_le_of_le_log q_prime.ne_zero)
        (min_le_right (n.factorization p) (p.log q))
    have p_e_succ_ne_q : p ^ e_succ ≠ q :=
      PrimePow_ne
        p_prime
        q_prime
        p_lt_q.ne
        ⟨e_succ, e_succ_ne_0, rfl⟩
        ⟨1, Nat.zero_lt_one, Nat.pow_one q⟩
    exact he ▸ Nat.lt_of_le_of_ne p_e_succ_le_q p_e_succ_ne_q

  have : ConsecutiveFactors n (p ^ e) (p ^ (e + 1)) := by
    refine ⟨p_e_dvd_n, p_e_succ_dvd_n, Nat.pow_lt_pow_succ p_prime.one_lt, ?_⟩
    by_contra hd
    obtain ⟨d, d_dvd_n, d_gt_p_e, d_lt_p_e_succ⟩ := hd
    obtain ⟨r, r_ne_p, r_prime, r_dvd_d⟩ :=
      not_pow_cons_factors_other_prime p_prime d_gt_p_e d_lt_p_e_succ
    apply
      not_not_intro
        (p_unique
          (Nat.lt_of_le_of_lt
            (Nat.le_of_dvd (dvd_ne_zero n_ne_0 d_dvd_n) r_dvd_d)
            (d_lt_p_e_succ.trans p_e_succ_lt_q))
          r_ne_p)
    exact dvd_n_fact_ne_zero n_ne_0 r_prime (r_dvd_d.trans d_dvd_n)
  refine ⟨this, ?_⟩

  have : ConsecutiveFactors n (p ^ (e + 1)) q := by
    refine ⟨p_e_succ_dvd_n, c.minFac_dvd.trans c_dvd_n, p_e_succ_lt_q, ?_⟩
    by_contra h
    obtain ⟨d, d_dvd_n, d_gt_p_e_succ, d_lt_q⟩ := h

    have d_fact_lt_n : d.factorization ≤ n.factorization :=
      (Nat.factorization_le_iff_dvd
        (dvd_ne_zero n_ne_0 d_dvd_n).ne.symm
        n_ne_0).mpr d_dvd_n

    have : ∃ d_e, d.factorization = Finsupp.single p d_e := by
      exists d.factorization p
      exact
        Finsupp.ext
          fun r => by
            if hr : r = p then
              rw [hr, Finsupp.single_eq_same]
            else
              rw [Finsupp.single_eq_of_ne (hr ∘ Eq.symm)]
              exact if r_ge_q : r ≥ q then
                Nat.factorization_eq_zero_of_lt (Nat.lt_of_lt_of_le d_lt_q r_ge_q)
              else
                Nat.le_zero.mp (p_unique (Nat.lt_of_not_ge r_ge_q) hr ▸ d_fact_lt_n r)
    obtain ⟨d_e, hd_e⟩ := this

    have d_eq_p_e :=
      Nat.eq_of_factorization_eq
        (Nat.ne_of_lt (dvd_ne_zero n_ne_0 d_dvd_n)).symm
        (Nat.pow_pos (Nat.zero_lt_of_ne_zero p_prime.ne_zero)).ne.symm
        fun r => congrArg (· r) (Nat.Prime.factorization_pow p_prime ▸ hd_e)
    have d_e_gt_e_succ : d_e > e_succ :=
      he ▸ (Nat.pow_lt_pow_iff_right p_prime.one_lt).mp (d_eq_p_e ▸ d_gt_p_e_succ)

    by_cases he_min : n.factorization p < p.log q
    . -- show d_e > n.factorization p
      exact
        Nat.le_lt_asymm
          ((Finsupp.single_eq_same : _ = d_e) ▸ (hd_e ▸ d_fact_lt_n) p)
          ((min_eq_left he_min.le) ▸ d_e_gt_e_succ)
    . -- show p ^ d_e > q
      have : d_e ≥ (p.log q).succ :=
        (min_eq_right (Nat.ge_of_not_lt he_min)) ▸ d_e_gt_e_succ
      let q_lt_d :=
        Nat.lt_of_lt_of_le
          (Nat.lt_pow_succ_log_self p_prime.one_lt q)
          ((Nat.pow_le_pow_iff_right p_prime.one_lt).mpr this)
      exact Nat.lt_le_asymm d_lt_q (d_eq_p_e ▸ q_lt_d.le)
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
