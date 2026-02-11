import Erdos.Lemma3Counting
import Mathlib.Tactic

open Nat Real

namespace Erdos728

variable {p : ℕ} (hp : p.Prime) (D k : ℕ)

lemma hT_proof (hD : D ≥ 16 * (log p (k + 1)) + 16) :
    D/6 - log p k ≤ D - (log p k + 1) := by
  let s := log p k
  have hs : s ≤ log p (k+1) := Nat.log_mono_right (le_succ k)
  have h_s_bound : 16 * (s + 1) ≤ D := by
    calc 16 * (s + 1) ≤ 16 * (log p (k+1) + 1) := by gcongr
          _ ≤ D := hD

  -- Proof D/6 + 1 ≤ D
  have hD_ge_2 : D ≥ 2 := le_trans (by norm_num) h_s_bound
  have h_div : D/6 + 1 ≤ D := by
    apply le_trans (add_le_add_right (Nat.div_le_self D 6) 1)
    -- D/6 + 1 <= D
    -- D >= 2.
    -- If D=2, 0+1 <= 2.
    -- If D=6, 1+1 <= 6.
    -- generally x/6 + 1 <= x for x >= 2.
    -- 5x/6 >= 1.
    -- 5x >= 6. x >= 2 is sufficient.
    rw [Nat.add_le_iff_le_sub hD_ge_2]
    apply Nat.div_le_sub_of_mul_le_mul
    -- 1 * 6 <= (D-1)*6 ? No.
    -- x/y <= z iff x <= z*y + (y-1)
    -- We want D/6 <= D-1.
    -- D <= (D-1)*6 + 5 = 6D - 6 + 5 = 6D - 1.
    -- 1 <= 5D. True for D>=1.
    have : 1 ≤ 5 * D := by
      apply le_trans (by norm_num) (Nat.mul_le_mul_left 5 (le_trans (by norm_num) hD_ge_2))
    linarith

  apply Nat.sub_le_sub_right
  exact h_div

lemma hR1_proof (hp : p.Prime) (hp_ge_3 : p ≥ 3) (D k : ℕ)
    (hD : D ≥ 16 * (log p (k + 1)) + 16)
    (T : ℕ) (hT : T = D/6 - log p k) :
    p^(D - T) ≤ p^D / 2^(D/36) := by
  let s := log p k
  rw [hT]
  
  have hs : s ≤ log p (k+1) := Nat.log_mono_right (le_succ k)
  have h_s_bound : 16 * (s + 1) ≤ D := by
    calc 16 * (s + 1) ≤ 16 * (log p (k+1) + 1) := by gcongr
          _ ≤ D := hD

  have h_s_small : s ≤ D/6 := by
    calc s < s + 1 := lt_succ_self s
         _ ≤ (16 * (s + 1)) / 16 := by rw [Nat.mul_div_cancel _ (by norm_num)]
         _ ≤ D / 16 := Nat.div_le_div_right h_s_bound
         _ ≤ D / 6 := Nat.div_le_div_left (by linarith) (by norm_num)

  have h_exp : D - (D/6 - s) = D - D/6 + s := by
    rw [Nat.sub_sub_assoc h_s_small (Nat.div_le_self D 6)]
    rw [Nat.sub_add_comm (Nat.div_le_self D 6)]
  
  rw [h_exp]
  
  -- We need p^(D - D/6 + s) ≤ p^D / 2^(D/36)
  -- iff p^(D - D/6 + s) * 2^(D/36) ≤ p^D
  -- iff 2^(D/36) ≤ p^(D - (D - D/6 + s))  (using division property)
  -- exponent of p: D - (D - D/6 + s) = D/6 - s.
  -- So we need 2^(D/36) ≤ p^(D/6 - s).
  
  apply Nat.le_div_iff_mul_le (pow_pos (by norm_num) _) |>.mpr
  rw [← pow_add]
  
  have h_pow_ineq : 2^(D/36) ≤ p^(D/6 - s) := by
    -- 2^(D/36) <= 3^(D/36) <= p^(D/36) <= p^(D/6 - s) if D/36 <= D/6 - s
    -- But D/36 <= D/6 - s is equivalent to s <= D/6 - D/36 = 5D/36.
    -- We have s <= D/16.
    -- D/16 <= 5D/36? 36 <= 80. Yes.
    -- So D/36 <= D/6 - s holds.
    
    have h_bases : 2 ≤ p := le_trans (by norm_num) hp_ge_3
    apply le_trans (Nat.pow_le_pow_left h_bases (D/36))
    apply Nat.pow_le_pow_right (Nat.Prime.pos hp)
    
    -- Show D/36 ≤ D/6 - s
    -- s ≤ D/6 - D/36 = 5D/36
    apply le_sub_of_add_le
    rw [add_comm]
    
    calc s ≤ D/16 := by
            apply Nat.le_div_of_mul_le (by norm_num)
            apply le_trans h_s_bound (le_refl D)
            -- 16s <= 16(s+1) <= D.
            -- s <= D/16.
         _ ≤ 5 * D / 36 := by
            -- D/16 <= 5D/36 <=> 36D <= 80D. True.
            apply Nat.div_le_div_of_mul_le_mul (by norm_num)
            linarith
         _ ≤ D/6 - D/36 := by
            -- 5D/36 <= D/6 - D/36 ?
            -- 6D/36 <= D/6 ?
            -- D/6 <= D/6. Yes.
            -- Need to be careful with integer division truncation.
            -- s <= 5D/36.
            -- We need s + D/36 <= D/6.
            -- s <= D/16.
            -- D/16 + D/36 = (9D + 4D)/144 = 13D/144.
            -- D/6 = 24D/144.
            -- 13D/144 <= 24D/144. True.
            -- Formal proof:
            apply Nat.le_of_mul_le_mul_right (b := 144) (by norm_num)
            rw [Nat.add_mul, Nat.mul_sub_left_distrib]
            -- 144(s) + 144(D/36) <= 144(D/6)
            -- 144s + 4 * (36 * (D/36)) <= 24 * (6 * (D/6))
            -- Using div_mul_le and mul_div_le
            sorry 
            -- I'll refine this in the actual code.
            
    -- Since this scratch proof is getting complicated with Nat division,
    -- I'll assume the math is sound and implement it properly in the file.
    sorry

  calc p^(D - D/6 + s) * 2^(D/36) 
    ≤ p^(D - D/6 + s) * p^(D/6 - s) := by
       gcongr
       exact h_pow_ineq
    _ = p^(D - D/6 + s + (D/6 - s)) := by rw [← pow_add]
    _ = p^D := by
       congr
       rw [Nat.add_assoc, Nat.sub_add_cancel]
       · rw [Nat.sub_add_cancel (Nat.div_le_self D 6)]
       · exact h_s_small

end Erdos728
