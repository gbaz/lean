/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jeremy Avigad

The order relation on the integers. We show that int is an instance of linear_comm_ordered_ring
prod transfer the results.
-/
import .basic algebra.ordered_ring
open nat
open decidable
open int eq.ops algebra eq unit is_trunc

namespace int

private definition nonneg (a : ℤ) : Type.{0} := int.cases_on a (take n, unit) (take n, empty)
protected definition le (a b : ℤ) : Type.{0} := nonneg (b - a)

definition int_has_le [instance] [reducible] [priority int.prio]: has_le int :=
has_le.mk int.le

protected definition lt (a b : ℤ) : Type.{0} := (a + 1) ≤ b

definition int_has_lt [instance] [reducible] [priority int.prio]: has_lt int :=
has_lt.mk int.lt

definition is_hprop_nonneg (a : ℤ) : is_hprop (nonneg a) :=
begin
induction a: unfold [nonneg]; exact _
end

definition is_hprop_le [instance] (a b : ℤ) : is_hprop (le a b) := !is_hprop_nonneg

definition is_hprop_lt [instance] (a b : ℤ) : is_hprop (lt a b) := !is_hprop_nonneg

local attribute nonneg [reducible]
private definition decidable_nonneg [instance] (a : ℤ) : decidable (nonneg a) := int.cases_on a _ _
definition decidable_le [instance] (a b : ℤ) : decidable (a ≤ b) := decidable_nonneg _
definition decidable_lt [instance] (a b : ℤ) : decidable (a < b) := decidable_nonneg _

private theorem nonneg.elim {a : ℤ} : nonneg a → Σn : ℕ, a = n :=
int.cases_on a (take n H, sigma.mk n rfl) (take n', empty.elim)

private theorem nonneg_sum_nonneg_neg (a : ℤ) : nonneg a ⊎ nonneg (-a) :=
int.cases_on a (take n, sum.inl star) (take n, sum.inr star)

theorem le.intro {a b : ℤ} {n : ℕ} (H : a + n = b) : a ≤ b :=
have n = b - a, from eq_add_neg_of_add_eq (begin rewrite [add.comm, H] end), -- !add.comm ▸ H),
show nonneg (b - a), from this ▸ star

theorem le.elim {a b : ℤ} (H : a ≤ b) : Σn : ℕ, a + n = b :=
obtain (n : ℕ) (H1 : b - a = n), from nonneg.elim H,
sigma.mk n (!add.comm ▸ iff.mpr !add_eq_iff_eq_add_neg (H1⁻¹))

protected theorem le_total (a b : ℤ) : a ≤ b ⊎ b ≤ a :=
sum.imp_right
  (assume H : nonneg (-(b - a)),
   have -(b - a) = a - b, from !neg_sub,
   show nonneg (a - b), from this ▸ H)
  (nonneg_sum_nonneg_neg (b - a))

theorem of_nat_le_of_nat_of_le {m n : ℕ} (H : #nat m ≤ n) : of_nat m ≤ of_nat n :=
obtain (k : ℕ) (Hk : m + k = n), from nat.le.elim H,
le.intro (Hk ▸ (of_nat_add m k)⁻¹)

theorem le_of_of_nat_le_of_nat {m n : ℕ} (H : of_nat m ≤ of_nat n) : (#nat m ≤ n) :=
obtain (k : ℕ) (Hk : of_nat m + of_nat k = of_nat n), from le.elim H,
have m + k = n, from of_nat.inj (of_nat_add m k ⬝ Hk),
nat.le.intro this

theorem of_nat_le_of_nat_iff (m n : ℕ) : of_nat m ≤ of_nat n ↔ m ≤ n :=
iff.intro le_of_of_nat_le_of_nat of_nat_le_of_nat_of_le

theorem lt_add_succ (a : ℤ) (n : ℕ) : a < a + succ n :=
le.intro (show a + 1 + n = a + succ n, from
  calc
    a + 1 + n = a + (1 + n) : add.assoc
      ... = a + (n + 1)     : by rewrite (int.add_comm 1 n)
      ... = a + succ n      : rfl)

theorem lt.intro {a b : ℤ} {n : ℕ} (H : a + succ n = b) : a < b :=
H ▸ lt_add_succ a n

theorem lt.elim {a b : ℤ} (H : a < b) : Σn : ℕ, a + succ n = b :=
obtain (n : ℕ) (Hn : a + 1 + n = b), from le.elim H,
have a + succ n = b, from
  calc
    a + succ n = a + 1 + n : by rewrite [add.assoc, int.add_comm 1 n]
           ... = b         : Hn,
sigma.mk n this

theorem of_nat_lt_of_nat_iff (n m : ℕ) : of_nat n < of_nat m ↔ n < m :=
calc
  of_nat n < of_nat m ↔ of_nat n + 1 ≤ of_nat m : iff.refl
    ... ↔ of_nat (nat.succ n) ≤ of_nat m        : of_nat_succ n ▸ !iff.refl
    ... ↔ nat.succ n ≤ m                        : of_nat_le_of_nat_iff
    ... ↔ n < m                                 : iff.symm (lt_iff_succ_le _ _)

theorem lt_of_of_nat_lt_of_nat {m n : ℕ} (H : of_nat m < of_nat n) : #nat m < n :=
iff.mp !of_nat_lt_of_nat_iff H

theorem of_nat_lt_of_nat_of_lt {m n : ℕ} (H : #nat m < n) : of_nat m < of_nat n :=
iff.mpr !of_nat_lt_of_nat_iff H

/- show that the integers form an ordered additive group -/

protected theorem le_refl (a : ℤ) : a ≤ a :=
le.intro (add_zero a)

protected theorem le_trans {a b c : ℤ} (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c :=
obtain (n : ℕ) (Hn : a + n = b), from le.elim H1,
obtain (m : ℕ) (Hm : b + m = c), from le.elim H2,
have a + of_nat (n + m) = c, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : {of_nat_add n m}
      ... = a + n + m : (add.assoc a n m)⁻¹
      ... = b + m : {Hn}
      ... = c : Hm,
le.intro this

protected theorem le_antisymm : Π {a b : ℤ}, a ≤ b → b ≤ a → a = b :=
take a b : ℤ, assume (H₁ : a ≤ b) (H₂ : b ≤ a),
obtain (n : ℕ) (Hn : a + n = b), from le.elim H₁,
obtain (m : ℕ) (Hm : b + m = a), from le.elim H₂,
have a + of_nat (n + m) = a + 0, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : by rewrite of_nat_add
      ... = a + n + m                       : by rewrite add.assoc
      ... = b + m                           : by rewrite Hn
      ... = a                               : by rewrite Hm
      ... = a + 0                           : by rewrite add_zero,
have of_nat (n + m) = of_nat 0, from add.left_cancel this,
have n + m = 0,                 from of_nat.inj this,
assert n = 0,                     from nat.eq_zero_of_add_eq_zero_right this,
show a = b, from
  calc
    a = a + 0    : add_zero
  ... = a + n    : by rewrite this
  ... = b        : Hn

protected theorem lt_irrefl (a : ℤ) : ¬ a < a :=
(suppose a < a,
  obtain (n : ℕ) (Hn : a + succ n = a), from lt.elim this,
  have a + succ n = a + 0, from
    Hn ⬝ !add_zero⁻¹,
  !succ_ne_zero (of_nat.inj (add.left_cancel this)))

protected theorem ne_of_lt {a b : ℤ} (H : a < b) : a ≠ b :=
(suppose a = b, absurd (this ▸ H) (int.lt_irrefl b))

theorem le_of_lt {a b : ℤ} (H : a < b) : a ≤ b :=
obtain (n : ℕ) (Hn : a + succ n = b), from lt.elim H,
le.intro Hn

protected theorem lt_iff_le_prod_ne (a b : ℤ) : a < b ↔ (a ≤ b × a ≠ b) :=
iff.intro
  (assume H, pair (le_of_lt H) (int.ne_of_lt H))
  (assume H,
    have a ≤ b, from prod.pr1 H,
    have a ≠ b, from prod.pr2 H,
    obtain (n : ℕ) (Hn : a + n = b), from le.elim `a ≤ b`,
    have n ≠ 0, from (assume H' : n = 0, `a ≠ b` (!add_zero ▸ H' ▸ Hn)),
    obtain (k : ℕ) (Hk : n = nat.succ k), from nat.exists_eq_succ_of_ne_zero this,
    lt.intro (Hk ▸ Hn))

protected theorem le_iff_lt_sum_eq (a b : ℤ) : a ≤ b ↔ (a < b ⊎ a = b) :=
iff.intro
  (assume H,
    by_cases
      (suppose a = b, sum.inr this)
      (suppose a ≠ b,
        obtain (n : ℕ) (Hn : a + n = b), from le.elim H,
        have n ≠ 0, from (assume H' : n = 0, `a ≠ b` (!add_zero ▸ H' ▸ Hn)),
        obtain (k : ℕ) (Hk : n = nat.succ k), from nat.exists_eq_succ_of_ne_zero this,
        sum.inl (lt.intro (Hk ▸ Hn))))
  (assume H,
    sum.elim H
      (assume H1, le_of_lt H1)
      (assume H1, H1 ▸ !int.le_refl))

theorem lt_succ (a : ℤ) : a < a + 1 :=
int.le_refl (a + 1)

protected theorem add_le_add_left {a b : ℤ} (H : a ≤ b) (c : ℤ) : c + a ≤ c + b :=
obtain (n : ℕ) (Hn : a + n = b), from le.elim H,
have H2 : c + a + n = c + b, from
  calc
    c + a + n = c + (a + n) : add.assoc c a n
      ... = c + b : {Hn},
le.intro H2

protected theorem add_lt_add_left {a b : ℤ} (H : a < b) (c : ℤ) : c + a < c + b :=
let H' := le_of_lt H in
(iff.mpr (int.lt_iff_le_prod_ne _ _)) (pair (int.add_le_add_left H' _)
                                  (take Heq, let Heq' := add_left_cancel Heq in
                                   !int.lt_irrefl (Heq' ▸ H)))

protected theorem mul_nonneg {a b : ℤ} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a * b :=
obtain (n : ℕ) (Hn : 0 + n = a), from le.elim Ha,
obtain (m : ℕ) (Hm : 0 + m = b), from le.elim Hb,
le.intro
  (inverse
    (calc
      a * b = (0 + n) * b : by rewrite Hn
        ... = n * b       : by rewrite zero_add
        ... = n * (0 + m) : by rewrite Hm
        ... = n * m       : by rewrite zero_add
        ... = 0 + n * m   : by rewrite zero_add))

protected theorem mul_pos {a b : ℤ} (Ha : 0 < a) (Hb : 0 < b) : 0 < a * b :=
obtain (n : ℕ) (Hn : 0 + nat.succ n = a), from lt.elim Ha,
obtain (m : ℕ) (Hm : 0 + nat.succ m = b), from lt.elim Hb,
lt.intro
  (inverse
    (calc
      a * b = (0 + nat.succ n) * b                     : by rewrite Hn
        ... = nat.succ n * b                           : by rewrite zero_add
        ... = nat.succ n * (0 + nat.succ m)            : by rewrite Hm
        ... = nat.succ n * nat.succ m                  : by rewrite zero_add
        ... = of_nat (nat.succ n * nat.succ m)         : by rewrite of_nat_mul
        ... = of_nat (nat.succ n * m + nat.succ n)     : by rewrite nat.mul_succ
        ... = of_nat (nat.succ (nat.succ n * m + n))   : by rewrite nat.add_succ
        ... = 0 + nat.succ (nat.succ n * m + n)        : by rewrite zero_add))

protected theorem zero_lt_one : (0 : ℤ) < 1 := star

protected theorem not_le_of_gt {a b : ℤ} (H : a < b) : ¬ b ≤ a :=
  assume Hba,
  let Heq := int.le_antisymm (le_of_lt H) Hba in
  !int.lt_irrefl (Heq ▸ H)

protected theorem lt_of_lt_of_le {a b c : ℤ} (Hab : a < b) (Hbc : b ≤ c) : a < c :=
  let Hab' := le_of_lt Hab in
  let Hac := int.le_trans Hab' Hbc in
  (iff.mpr !int.lt_iff_le_prod_ne) (pair Hac
    (assume Heq, int.not_le_of_gt (Heq ▸ Hab) Hbc))

protected theorem lt_of_le_of_lt  {a b c : ℤ} (Hab : a ≤ b) (Hbc : b < c) : a < c :=
  let Hbc' := le_of_lt Hbc in
  let Hac := int.le_trans Hab Hbc' in
  (iff.mpr !int.lt_iff_le_prod_ne) (pair Hac
    (assume Heq, int.not_le_of_gt (Heq⁻¹ ▸ Hbc) Hab))

protected definition linear_ordered_comm_ring [reducible] [trans_instance] :
    linear_ordered_comm_ring int :=
⦃linear_ordered_comm_ring, int.integral_domain,
  le               := int.le,
  le_refl          := int.le_refl,
  le_trans         := @int.le_trans,
  le_antisymm      := @int.le_antisymm,
  lt               := int.lt,
  le_of_lt         := @int.le_of_lt,
  lt_irrefl        := int.lt_irrefl,
  lt_of_lt_of_le   := @int.lt_of_lt_of_le,
  lt_of_le_of_lt   := @int.lt_of_le_of_lt,
  add_le_add_left  := @int.add_le_add_left,
  mul_nonneg       := @int.mul_nonneg,
  mul_pos          := @int.mul_pos,
  le_iff_lt_sum_eq  := int.le_iff_lt_sum_eq,
  le_total         := int.le_total,
  zero_ne_one      := int.zero_ne_one,
  zero_lt_one      := int.zero_lt_one,
  add_lt_add_left  := @int.add_lt_add_left⦄

protected definition decidable_linear_ordered_comm_ring [reducible] [instance] :
    decidable_linear_ordered_comm_ring int :=
⦃decidable_linear_ordered_comm_ring,
 int.linear_ordered_comm_ring,
 decidable_lt := decidable_lt⦄

/- more facts specific to int -/

theorem of_nat_nonneg (n : ℕ) : 0 ≤ of_nat n := star

theorem of_nat_pos {n : ℕ} (Hpos : #nat n > 0) : of_nat n > 0 :=
of_nat_lt_of_nat_of_lt Hpos

theorem of_nat_succ_pos (n : nat) : of_nat (nat.succ n) > 0 :=
of_nat_pos !nat.succ_pos

theorem exists_eq_of_nat {a : ℤ} (H : 0 ≤ a) : Σn : ℕ, a = of_nat n :=
obtain (n : ℕ) (H1 : 0 + of_nat n = a), from le.elim H,
sigma.mk n (!zero_add ▸ (H1⁻¹))

theorem exists_eq_neg_of_nat {a : ℤ} (H : a ≤ 0) : Σn : ℕ, a = -(of_nat n) :=
have -a ≥ 0, from iff.mpr !neg_nonneg_iff_nonpos H,
obtain (n : ℕ) (Hn : -a = of_nat n), from exists_eq_of_nat this,
sigma.mk n (eq_neg_of_eq_neg (Hn⁻¹))

theorem of_nat_nat_abs_of_nonneg {a : ℤ} (H : a ≥ 0) : of_nat (nat_abs a) = a :=
obtain (n : ℕ) (Hn : a = of_nat n), from exists_eq_of_nat H,
Hn⁻¹ ▸ ap of_nat (nat_abs_of_nat n)

theorem of_nat_nat_abs_of_nonpos {a : ℤ} (H : a ≤ 0) : of_nat (nat_abs a) = -a :=
have -a ≥ 0, from iff.mpr !neg_nonneg_iff_nonpos H,
calc
  of_nat (nat_abs a) = of_nat (nat_abs (-a)) : nat_abs_neg
                 ... = -a                    : of_nat_nat_abs_of_nonneg this

theorem of_nat_nat_abs (b : ℤ) : nat_abs b = abs b :=
sum.elim (le.total 0 b)
  (assume H : b ≥ 0, of_nat_nat_abs_of_nonneg H ⬝ (abs_of_nonneg H)⁻¹)
  (assume H : b ≤ 0, of_nat_nat_abs_of_nonpos H ⬝ (abs_of_nonpos H)⁻¹)

theorem nat_abs_abs (a : ℤ) : nat_abs (abs a) = nat_abs a :=
abs.by_cases rfl !nat_abs_neg

theorem lt_of_add_one_le {a b : ℤ} (H : a + 1 ≤ b) : a < b :=
obtain (n : nat) (H1 : a + 1 + n = b), from le.elim H,
have a + succ n = b, by rewrite [-H1, add.assoc, add.comm 1],
lt.intro this

theorem add_one_le_of_lt {a b : ℤ} (H : a < b) : a + 1 ≤ b :=
obtain (n : nat) (H1 : a + succ n = b), from lt.elim H,
have a + 1 + n = b, by rewrite [-H1, add.assoc, add.comm 1],
le.intro this

theorem lt_add_one_of_le {a b : ℤ} (H : a ≤ b) : a < b + 1 :=
lt_add_of_le_of_pos H star

theorem le_of_lt_add_one {a b : ℤ} (H : a < b + 1) : a ≤ b :=
have H1 : a + 1 ≤ b + 1, from add_one_le_of_lt H,
le_of_add_le_add_right H1

theorem sub_one_le_of_lt {a b : ℤ} (H : a ≤ b) : a - 1 < b :=
lt_of_add_one_le (begin rewrite sub_add_cancel, exact H end)

theorem lt_of_sub_one_le {a b : ℤ} (H : a - 1 < b) : a ≤ b :=
!sub_add_cancel ▸ add_one_le_of_lt H

theorem le_sub_one_of_lt {a b : ℤ} (H : a < b) : a ≤ b - 1 :=
le_of_lt_add_one begin rewrite sub_add_cancel, exact H end

theorem lt_of_le_sub_one {a b : ℤ} (H : a ≤ b - 1) : a < b :=
!sub_add_cancel ▸ (lt_add_one_of_le H)

theorem sign_of_succ (n : nat) : sign (nat.succ n) = 1 :=
sign_of_pos (of_nat_pos !nat.succ_pos)

theorem exists_eq_neg_succ_of_nat {a : ℤ} : a < 0 → Σm : ℕ, a = -[1+m] :=
int.cases_on a
  (take (m : nat) H, absurd (of_nat_nonneg m : 0 ≤ m) (not_le_of_gt H))
  (take (m : nat) H, sigma.mk m rfl)

theorem eq_one_of_mul_eq_one_right {a b : ℤ} (H : a ≥ 0) (H' : a * b = 1) : a = 1 :=
have a * b > 0, by rewrite H'; apply star,
have b > 0, from pos_of_mul_pos_left this H,
have a > 0, from pos_of_mul_pos_right `a * b > 0` (le_of_lt `b > 0`),
sum.elim (le_sum_gt a 1)
  (suppose a ≤ 1,
    show a = 1, from le.antisymm this (add_one_le_of_lt `a > 0`))
  (suppose a > 1,
    assert a * b ≥ 2 * 1,
      from mul_le_mul (add_one_le_of_lt `a > 1`) (add_one_le_of_lt `b > 0`) star H,
    have empty, by rewrite [H' at this]; exact this,
    empty.elim this)

theorem eq_one_of_mul_eq_one_left {a b : ℤ} (H : b ≥ 0) (H' : a * b = 1) : b = 1 :=
eq_one_of_mul_eq_one_right H (!mul.comm ▸ H')

theorem eq_one_of_mul_eq_self_left {a b : ℤ} (Hpos : a ≠ 0) (H : b * a = a) : b = 1 :=
eq_of_mul_eq_mul_right Hpos (H ⬝ (one_mul a)⁻¹)

theorem eq_one_of_mul_eq_self_right {a b : ℤ} (Hpos : b ≠ 0) (H : b * a = b) : a = 1 :=
eq_one_of_mul_eq_self_left Hpos (!mul.comm ▸ H)

theorem eq_one_of_dvd_one {a : ℤ} (H : a ≥ 0) (H' : a ∣ 1) : a = 1 :=
dvd.elim H'
  (take b,
    suppose 1 = a * b,
    eq_one_of_mul_eq_one_right H this⁻¹)

theorem exists_least_of_bdd {P : ℤ → Type} [HP : decidable_pred P]
    (Hbdd : Σ b : ℤ, Π z : ℤ, z ≤ b → ¬ P z)
        (Hinh : Σ z : ℤ, P z) : Σ lb : ℤ, P lb × (Π z : ℤ, z < lb → ¬ P z) :=
  begin
    cases Hbdd with [b, Hb],
    cases Hinh with [elt, Helt],
    existsi b + of_nat (least (λ n, P (b + of_nat n)) (nat.succ (nat_abs (elt - b)))),
    have Heltb : elt > b, begin
      apply lt_of_not_ge,
      intro Hge,
      apply (Hb _ Hge) Helt
    end,
    have H' : P (b + of_nat (nat_abs (elt - b))), begin
      rewrite [of_nat_nat_abs_of_nonneg (int.le_of_lt (iff.mpr !sub_pos_iff_lt Heltb)),
              add.comm, sub_add_cancel],
      apply Helt
    end,
    apply pair,
    apply least_of_lt _ !lt_succ_self H',
    intros z Hz,
    cases em (z ≤ b) with [Hzb, Hzb],
    apply Hb _ Hzb,
    let Hzb' := lt_of_not_ge Hzb,
    let Hpos := iff.mpr !sub_pos_iff_lt Hzb',
    have Hzbk : z = b + of_nat (nat_abs (z - b)),
      by rewrite [of_nat_nat_abs_of_nonneg (int.le_of_lt Hpos), int.add_comm, sub_add_cancel],
    have Hk : nat_abs (z - b) < least (λ n, P (b + of_nat n)) (nat.succ (nat_abs (elt - b))), begin
     note Hz' := iff.mp !lt_add_iff_sub_lt_left Hz,
     rewrite [-of_nat_nat_abs_of_nonneg (int.le_of_lt Hpos) at Hz'],
     apply lt_of_of_nat_lt_of_nat Hz'
    end,
    let Hk' := not_le_of_gt Hk,
    rewrite Hzbk,
    apply λ p, mt (ge_least_of_lt _ p) Hk',
    apply nat.lt_trans Hk,
    apply least_lt _ !lt_succ_self H'
  end

theorem exists_greatest_of_bdd {P : ℤ → Type} [HP : decidable_pred P]
    (Hbdd : Σ b : ℤ, Π z : ℤ, z ≥ b → ¬ P z)
        (Hinh : Σ z : ℤ, P z) : Σ ub : ℤ, P ub × (Π z : ℤ, z > ub → ¬ P z) :=
  begin
    cases Hbdd with [b, Hb],
    cases Hinh with [elt, Helt],
    existsi b - of_nat (least (λ n, P (b - of_nat n)) (nat.succ (nat_abs (b - elt)))),
    have Heltb : elt < b, begin
      apply lt_of_not_ge,
      intro Hge,
      apply (Hb _ Hge) Helt
    end,
    have H' : P (b - of_nat (nat_abs (b - elt))), begin
      rewrite [of_nat_nat_abs_of_nonneg (int.le_of_lt (iff.mpr !sub_pos_iff_lt Heltb)),
              sub_sub_self],
      apply Helt
    end,
    apply pair,
    apply least_of_lt _ !lt_succ_self H',
    intros z Hz,
    cases em (z ≥ b) with [Hzb, Hzb],
    apply Hb _ Hzb,
    let Hzb' := lt_of_not_ge Hzb,
    let Hpos := iff.mpr !sub_pos_iff_lt Hzb',
    have Hzbk : z = b - of_nat (nat_abs (b - z)),
      by rewrite [of_nat_nat_abs_of_nonneg (int.le_of_lt Hpos), sub_sub_self],
    have Hk : nat_abs (b - z) < least (λ n, P (b - of_nat n)) (nat.succ (nat_abs (b - elt))), begin
      note Hz' := iff.mp !lt_add_iff_sub_lt_left (iff.mpr !lt_add_iff_sub_lt_right Hz),
      rewrite [-of_nat_nat_abs_of_nonneg (int.le_of_lt Hpos) at Hz'],
      apply lt_of_of_nat_lt_of_nat Hz'
    end,
    let Hk' := not_le_of_gt Hk,
    rewrite Hzbk,
    apply λ p, mt (ge_least_of_lt _ p) Hk',
    apply nat.lt_trans Hk,
    apply least_lt _ !lt_succ_self H'
  end

end int
