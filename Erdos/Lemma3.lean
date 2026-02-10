import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

open Nat BigOperators Finset

namespace Erdos728

variable {p : ℕ} {D : ℕ} (hp : p > 1)
include hp

/--
The number corresponding to a sequence of digits.
-/
def from_digits (p : ℕ) {D : ℕ} (f : Fin D → Fin p) : ℕ :=
  ∑ i : Fin D, (f i : ℕ) * p ^ (i : ℕ)

/--
The sequence of digits corresponding to a number.
-/
def to_digits (p : ℕ) (D : ℕ) (h : p > 0) (m : ℕ) : Fin D → Fin p :=
  fun i => ⟨(m / p ^ (i : ℕ)) % p, Nat.mod_lt _ h⟩

omit hp in
lemma from_digits_succ {D : ℕ} (f : Fin (D + 1) → Fin p) :
    from_digits p f = f 0 + p * from_digits p (Fin.tail f) := by
  rw [from_digits, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
  congr 1
  rw [from_digits, mul_sum]
  congr; ext i
  simp only [Fin.tail]
  ring

lemma to_digits_succ {D : ℕ} (m : ℕ) :
    to_digits p (D + 1) (by omega) m =
      Fin.cons ⟨m % p, Nat.mod_lt _ (by omega)⟩ (to_digits p D (by omega) (m / p)) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp only [to_digits, Fin.cons_zero]
    rw [Fin.val_zero, pow_zero, Nat.div_one]
  · intro j
    simp only [to_digits, Fin.cons_succ]
    rw [Fin.val_succ, Nat.pow_succ', Nat.div_div_eq_div_mul]

lemma from_digits_lt_pow (f : Fin D → Fin p) : from_digits p f < p ^ D := by
  have hp_ge_2 : p ≥ 2 := by omega
  have h_sum : from_digits p f = ∑ i : Fin D, (f i : ℕ) * p ^ (i : ℕ) := rfl
  have h_bound : from_digits p f ≤ ∑ i : Fin D, (p - 1) * p ^ (i : ℕ) := by
    rw [h_sum]
    gcongr with i
    exact Nat.le_pred_of_lt (Fin.is_lt (f i))
  rw [← mul_sum, Fin.sum_univ_eq_sum_range, Nat.geomSum_eq hp_ge_2] at h_bound
  have h_eq : (p - 1) * ((p ^ D - 1) / (p - 1)) = p ^ D - 1 :=
    Nat.mul_div_cancel' (Nat.sub_one_dvd_pow_sub_one p D)
  rw [h_eq] at h_bound
  exact lt_of_le_of_lt h_bound (Nat.pred_lt (Nat.ne_of_gt (Nat.pow_pos (by omega))))

lemma from_digits_to_digits (m : ℕ) (hm : m < p ^ D) :
    from_digits p (to_digits p D (by omega) m) = m := by
  induction D generalizing m with
  | zero =>
    cases m
    · simp [from_digits, to_digits]
    · simp at hm
  | succ D ih =>
    rw [to_digits_succ hp m]
    rw [from_digits_succ]
    simp only [Fin.cons_zero, Fin.tail_cons]
    conv_rhs => rw [(Nat.mod_add_div m p).symm]
    rw [ih (m / p) (by
        rw [pow_succ, mul_comm] at hm
        exact Nat.div_lt_of_lt_mul hm)]

lemma from_digits_inj {D : ℕ} (f g : Fin D → Fin p)
    (h : from_digits p f = from_digits p g) : f = g := by
  induction D with
  | zero => ext i; exact Fin.elim0 i
  | succ D ih =>
    rw [from_digits_succ, from_digits_succ] at h
    have h_mod : (f 0 : ℕ) % p = (g 0 : ℕ) % p := by
      rw [← Nat.add_mul_mod_self_left (f 0) p _, h, Nat.add_mul_mod_self_left]
    have h0 : f 0 = g 0 := by
      apply Fin.eq_of_val_eq
      have hf : (f 0 : ℕ) < p := Fin.is_lt (f 0)
      have hg : (g 0 : ℕ) < p := Fin.is_lt (g 0)
      rw [Nat.mod_eq_of_lt hf] at h_mod
      rw [Nat.mod_eq_of_lt hg] at h_mod
      exact h_mod
    
    have h_rem : p * from_digits p (Fin.tail f) = p * from_digits p (Fin.tail g) := by
      rw [h0] at h
      exact Nat.add_left_cancel h
    
    have h_tail : from_digits p (Fin.tail f) = from_digits p (Fin.tail g) :=
      Nat.eq_of_mul_eq_mul_left (by omega) h_rem
    
    have h_rec : Fin.tail f = Fin.tail g := ih _ _ h_tail
    
    ext i
    refine Fin.cases ?_ ?_ i
    · exact congr_arg (fun x => x.val) h0
    · intro j
      exact congr_arg (fun x => x.val) (congr_fun h_rec j)

lemma to_digits_from_digits (f : Fin D → Fin p) :
    to_digits p D (by omega) (from_digits p f) = f :=
  from_digits_inj hp _ _ (from_digits_to_digits hp _ (from_digits_lt_pow hp f))

/--
The bijection between numbers less than p^D and digit sequences of length D.
-/
def digits_bijection : {m : ℕ // m < p ^ D} ≃ (Fin D → Fin p) where
  toFun := fun ⟨m, _⟩ => to_digits p D (by omega) m
  invFun := fun f => ⟨from_digits p f, from_digits_lt_pow hp f⟩
  left_inv := fun ⟨m, hm⟩ => Subtype.ext (from_digits_to_digits hp m hm)
  right_inv := fun f => to_digits_from_digits hp f

/--
The set of digit sequences with a cascade of length at least `l` starting at `S`.
-/
def cascade_set (S l : ℕ) (h : S + l ≤ D) : Finset (Fin D → Fin p) :=
  Finset.univ.filter (fun f => ∀ i : ℕ, (hi : i < l) → f ⟨S + i, by have := hi; have := h; omega⟩ = ⟨p - 1, by omega⟩)

lemma card_cascade_set (S l : ℕ) (h : S + l ≤ D) :
    (cascade_set hp S l h).card = p ^ (D - l) := by
  -- Implementation needed
  sorry

/--
Cascade length starting at S.
-/
def cascade_length (f : Fin D → Fin p) (S : ℕ) : ℕ :=
  (List.range (D - S)).takeWhile (fun i =>
    if h : S + i < D then f ⟨S + i, h⟩ == ⟨p - 1, by omega⟩ else false) |>.length

lemma cascade_length_ge_iff (f : Fin D → Fin p) (S l : ℕ) (h : S + l ≤ D) :
    cascade_length hp f S ≥ l ↔ ∀ i : ℕ, (hi : i < l) → f ⟨S + i, by have := hi; have := h; omega⟩ = ⟨p - 1, by omega⟩ := by
  sorry

lemma lemma_A3 (S l : ℕ) (h : S + l ≤ D) :
    (Finset.univ.filter (fun m : Fin D → Fin p => cascade_length hp m S ≥ l)).card = p ^ (D - l) := by
  rw [Finset.filter_congr (fun m _ => cascade_length_ge_iff hp m S l h)]
  exact card_cascade_set hp S l h

/--
Carry at index i for m + k in base p.
-/
def carry (p : ℕ) (m k : ℕ) (i : ℕ) : ℕ :=
  if (m % p ^ (i + 1) + k % p ^ (i + 1) ≥ p ^ (i + 1)) then 1 else 0

omit hp in
lemma carry_le_one (m k i : ℕ) : carry p m k i ≤ 1 := by
  dsimp [carry]
  split_ifs <;> simp

lemma v_p_choose_eq_sum_carry (hp_prime : p.Prime) (m k : ℕ) :
    padicValNat p ((m + k).choose k) = ∑ i ∈ range (m + k), carry p m k i := by
  -- This requires relating `carry` to Mathlib's carry count (Kummer)
  -- Or proving recurrence and sum directly.
  sorry

lemma lemma_A2 (m k s : ℕ) (h_s : p ^ (s + 1) > k) (h_D : D > s) (hm : m < p ^ D) (hp_prime : p.Prime) :
    padicValNat p ((m + k).choose k) ≤ s + 1 + cascade_length hp (to_digits p D (by omega) m) (s + 1) := by
  sorry

end Erdos728
