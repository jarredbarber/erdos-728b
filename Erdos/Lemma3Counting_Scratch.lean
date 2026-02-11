lemma threshold_subpolynomial (C_log : ℝ) :
    ∃ N : ℕ, ∀ m₀ : ℕ, N ≤ m₀ → ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ C_log * Real.log (2 * m₀) →
      union_bound_threshold k ≤ m₀ := by
  -- Handle C_log <= 0
  by_cases hC : C_log ≤ 0
  · use 2
    intro m₀ hm₀ k hk h_bound
    exfalso
    have h_log : Real.log (2 * m₀) > 0 := Real.log_pos (by norm_cast; linarith)
    have h_neg : C_log * Real.log (2 * m₀) ≤ 0 := mul_nonneg_of_nonpos_of_nonneg hC (le_of_lt h_log)
    have : (k : ℝ) ≤ 0 := le_trans h_bound h_neg
    linarith
  push_neg at hC

  -- Step 1: Bound log(T(k)) <= 1000 * (log(2k))^2
  have h_log_Tk (k : ℕ) (hk : k ≥ 1) : 
    Real.log (union_bound_threshold k) ≤ 
    1000 * (Real.log (2 * k))^2 := by
      apply le_trans (union_bound_threshold_log_bound k hk)
      
      let L := Real.log (2 * k)
      have hL : L ≥ Real.log 2 := by
        rw [Real.log_le_log_iff (by norm_num) (by norm_cast; linarith)]; linarith
      
      -- Expand log(16k)
      rw [show Real.log (16 * k) = Real.log 8 + L by
          rw [show 16 * k = 8 * (2 * k) by ring, Real.log_mul (by norm_num) (by norm_cast; linarith)]]
      
      calc (72 * ((Real.log 8 + L) / Real.log 2 + 1) + 72) * L
         = (72 * (3 + L / Real.log 2 + 1) + 72) * L := by
             rw [show Real.log 8 = 3 * Real.log 2 by rw [show 8=(2:ℝ)^3 by norm_num, Real.log_pow]]
             field_simp
             ring_nf
       _ = 360 * L + (72 / Real.log 2) * L^2 := by field_simp; ring
       _ ≤ (360 / Real.log 2) * L^2 + (72 / Real.log 2) * L^2 := by
           apply add_le_add_right
           rw [mul_div_assoc]
           apply mul_le_mul_of_nonneg_left
           · rw [le_div_iff₀ (Real.log_pos (by norm_num))]
             exact hL
           · norm_num
       _ = (432 / Real.log 2) * L^2 := by ring
       _ ≤ 1000 * L^2 := by
           apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
           rw [div_le_iff₀ (Real.log_pos (by norm_num))]
           rw [Real.le_log_iff_exp_le (by norm_num)]
           have : (432 : ℝ) / 1000 ≤ 1/2 := by norm_num
           apply le_trans (Real.exp_monotone this)
           rw [Real.exp_le_iff_le_log (by norm_num)]
           rw [le_div_iff₀ (by norm_num : (2:ℝ) > 0)]
           rw [mul_comm, ← Real.log_pow, show (2:ℝ)^2 = 4 by norm_num]
           rw [Real.le_log_iff_exp_le (by norm_num)]
           exact Real.exp_one_lt_d9.le.trans (by norm_num)

  -- Step 2: Use k <= C_log * log(2m0)
  -- Let x = log(2m0)
  let C_quad := 2000 * (Real.log (2 * C_log))^2
  let C_quad_x := 2000
  
  -- Apply log_growth_lemma for C_quad_x
  obtain ⟨N1, hN1⟩ := log_growth_lemma C_quad_x
  
  -- Need C_quad + log 2 <= x/2 for large x
  let N2_val := 2 * (C_quad + Real.log 2)
  let N2 := Nat.ceil N2_val
  let N := max (max N1 N2) 3
  
  -- We need to ensure log(2m0) >= N.
  -- log(2m0) >= N implies 2m0 >= exp(N).
  let N_final := Nat.ceil (Real.exp N)
  
  use N_final
  intro m₀ hm₀ k hk h_bound
  
  have hm₀_pos : m₀ > 0 := lt_of_lt_of_le (by norm_num) hm₀
  let x := Real.log (2 * m₀)
  have hx_pos : x > 0 := Real.log_pos (by norm_cast; linarith)
  
  have hx_ge_N : x ≥ N := by
    rw [Real.le_log_iff_exp_le (by norm_cast; linarith)]
    calc Real.exp N ≤ N_final := Nat.le_ceil _
       _ ≤ m₀ := hm₀
       _ ≤ 2 * m₀ := by linarith
  
  rw [Real.le_log_iff_exp_le hm₀_pos]
  
  apply le_trans (h_log_Tk k hk)
  
  -- 1000 * (log 2k)^2 <= ...
  have h_log_2k : Real.log (2 * k) ≤ Real.log (2 * C_log) + Real.log x := by
    rw [← Real.log_mul (by norm_num) hx_pos] -- log((2C)*x)
    rw [Real.log_le_log_iff (by norm_cast; linarith) (by norm_cast; positivity)]
    calc (2 * k : ℝ) = 2 * k := rfl
       _ ≤ 2 * (C_log * Real.log (2 * m₀)) := mul_le_mul_of_nonneg_left h_bound (by norm_num)
       _ = (2 * C_log) * x := by ring
  
  have h_sq_le : (Real.log (2 * k))^2 ≤ 2 * (Real.log (2 * C_log))^2 + 2 * (Real.log x)^2 := by
    calc (Real.log (2 * k))^2 
       ≤ (Real.log (2 * C_log) + Real.log x)^2 := sq_le_sq' (by 
           rw [abs_le]
           constructor
           · linarith [hx_pos, Real.log_pos (by norm_cast; linarith : 2*k > 1)] 
             -- Actually just RHS >= 0 if log(2k) >= 0.
             -- log(2k) >= log 2 > 0.
             -- log(2C) + log x could be negative?
             -- x >= N >= 3. log x > 1.
             -- C_log could be small.
             -- But (log(2k))^2 <= (A+B)^2 if A+B >= log(2k).
             -- We have log(2k) <= A+B.
             -- Since log(2k) >= 0, if A+B >= 0, then (log 2k)^2 <= (A+B)^2.
             -- A+B >= log 2k >= 0. So yes.
             exact h_log_2k
           · exact h_log_2k
         )
       _ ≤ 2 * (Real.log (2 * C_log))^2 + 2 * (Real.log x)^2 := by
           have : (Real.log (2 * C_log) + Real.log x)^2 + (Real.log (2 * C_log) - Real.log x)^2 = 
                  2 * (Real.log (2 * C_log))^2 + 2 * (Real.log x)^2 := by ring
           linarith [sq_nonneg (Real.log (2 * C_log) - Real.log x)]

  calc 1000 * (Real.log (2 * k))^2
     ≤ 1000 * (2 * (Real.log (2 * C_log))^2 + 2 * (Real.log x)^2) := 
         mul_le_mul_of_nonneg_left h_sq_le (by norm_num)
   _ = 2000 * (Real.log (2 * C_log))^2 + 2000 * (Real.log x)^2 := by ring
   _ = C_quad + C_quad_x * (Real.log x)^2 := rfl
   _ ≤ C_quad + x / 2 := by
       apply add_le_add_left
       apply hN1
       exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx_ge_N)
   _ ≤ (x / 2 - Real.log 2) + x / 2 := by
       apply add_le_add_right
       -- C_quad <= x/2 - log 2
       -- C_quad + log 2 <= x/2
       -- 2 * (C_quad + log 2) <= x
       -- N2_val <= x
       calc C_quad ≤ x / 2 - Real.log 2 ↔ C_quad + Real.log 2 ≤ x / 2 := by linarith
       rw [← mul_le_mul_left (by norm_num : (2:ℝ) > 0)]
       simp [mul_sub, mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
       rw [← mul_add]
       calc 2 * (C_quad + Real.log 2) 
           = N2_val := rfl
         _ ≤ N2 := Nat.le_ceil _
         _ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx_ge_N)
         _ ≤ x := hx_ge_N
   _ = x - Real.log 2 := by ring
   _ = Real.log (2 * m₀) - Real.log 2 := rfl
   _ = Real.log m₀ := by
       rw [Real.log_mul (by norm_num) (by norm_cast; linarith)]
       ring

