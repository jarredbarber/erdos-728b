import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

open Nat BigOperators Finset

namespace Erdos728

variable {p : ℕ} {D : ℕ} (hp : p > 1)

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
    to_digits p (D + 1) (by omega) m = Fin.cons ⟨m % p, Nat.mod_lt _ (by omega)⟩ (to_digits p D (by omega) (m / p)) := sorry

lemma from_digits_lt_pow (f : Fin D → Fin p) : from_digits p f < p ^ D := sorry

lemma from_digits_to_digits (m : ℕ) (hm : m < p ^ D) :
    from_digits p (to_digits p D (by omega) m) = m := by
  induction D generalizing m with
  | zero =>
    cases m
    · simp [from_digits, to_digits]
    · simp at hm
  | succ D ih =>
    rw [to_digits_succ (by omega) m]
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
  from_digits_inj _ _ (from_digits_to_digits hp (from_digits p f) (from_digits_lt_pow f))

/--
The bijection between numbers less than p^D and digit sequences of length D.
-/
def digits_bijection : {m : ℕ // m < p ^ D} ≃ (Fin D → Fin p) where
  toFun := fun ⟨m, _⟩ => to_digits p D (by omega) m
  invFun := fun f => ⟨from_digits p f, from_digits_lt_pow f⟩
  left_inv := fun ⟨m, hm⟩ => Subtype.ext (from_digits_to_digits hp m hm)
  right_inv := fun f => to_digits_from_digits hp f

end Erdos728
