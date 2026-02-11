# timtam Task: Close sorry: valuation_le_cascade (L3C:45) (erdos728b-vtv)

Role: formalize
Agent: formalize (google-antigravity/claude-opus-4-6-thinking)
Start Time: 2026-02-11T06:03:57.929Z

## Agent Interaction



> **Thinking:**
> Let me start by understanding the task. I need to close a `sorry` in `Lemma3Counting.lean` at line 45 for a lemma called `valuation_le_cascade`. Let me first read the relevant files to understand the context.


```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-vtv --status "Reading source files and understanding context"
```

🛠️ **Executing tool: read**
Let me find the specific sorry at line 45 for `valuation_le_cascade`:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "valuation_le_cascade" Erdos/Lemma3Counting.lean
```

🛠️ **Executing tool: read**
Now let me understand the dependencies - the task says it uses `carry_propagate` (from erdos728b-zs3). Let me check the NL proofs:
```bash
$ cd /home/jarred/code/erdos-728b && ls proofs/
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -n -i "valuation_le_cascade\|valuation.*cascade\|cascade.*bound\|kummer.*cascade" proofs/lemma3-counting.md | head -30
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -n -i "cascade" proofs/lemma3-counting.md | head -30
```

🛠️ **Executing tool: read**

```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-vtv --status "Understanding proof approach: Kummer's theorem + carry cascade structure"
```
Now let me understand what we need to prove. The lemma states:

```
padicValNat p ((m + k).choose k) ≤ (log p k + 1) + cascade_length (p:=p) k D m
```

The NL proof (Lemma A2) says: carries at positions 0..s contribute at most s+1, and carries at positions s+1..s+L contribute at most L. Beyond position s+L, no carry propagates because the cascade terminates.

This is very similar to `valuation_gt_implies_cascade` which already exists in the file! Let me study that lemma and the relevant Mathlib API.
🛠️ **Executing tool: read**
Now let me look at `valuation_gt_implies_cascade` more carefully - it uses `Nat.factorization_choose'` which counts carry positions. Let me also check what API we have:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "factorization_choose" .lake/packages/mathlib/Mathlib/Data/Nat/Choose/Factorization.lean | head -20
```

```bash
$ cd /home/jarred/code/erdos-728b && sed -n '114,140p' .lake/packages/mathlib/Mathlib/Data/Nat/Choose/Factorization.lean
```
Now I have a clear picture. The key idea is:

1. By `factorization_choose'`, `v_p(C(m+k,k))` = number of carry positions in `{1, ..., b-1}`.
2. Carry positions at `{1, ..., s+1}` contribute at most `s+1` (where `s = log p k`).
3. Carry positions at `{s+2, ...}` can only be in the cascade region `{s+2, ..., s+1+L}` where `L = cascade_length`.
4. So total ≤ `(s+1) + L`.

Let me look at the existing `no_carry_beyond` lemma and `cascade_digit_neq` since those handle the cascade termination. But we have a complication: the lemma doesn't require `cascade_length < D - (s+1)`, so we might need to handle the case where the cascade fills all remaining digits.

Let me also check if there's an issue with `m < p^D` constraint and the cascade definition:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "cascade_length\|carry_cond\|carry_propagate\|no_carry_beyond\|cascade_digit_neq" Erdos/Lemma3Counting.lean | head -20
```
Now let me understand the structure. The proof approach is:

1. Use `Nat.factorization_choose'` to express `v_p` as number of carry positions.
2. Split carry positions into `{1, ..., s+1}` and `{s+2, ..., b-1}`.
3. Show all carry positions in `{s+2, ..., b-1}` are in `{s+2, ..., s+1+L}`.
4. So total ≤ `(s+1) + L`.

**Key subtlety**: The cascade_length is capped at `D - (s+1)`. When `m < p^D`, all digits of `m` at positions ≥ D are 0, so:
- If the cascade fills all D-(s+1) positions, then `L = D-(s+1)`. But since `m < p^D`, for positions ≥ D, `m`'s digits are 0, so the cascade can't continue. We need to handle this.

Actually, wait - `valuation_le_cascade` has the constraint `hm : m < p^D`, which means `m` has at most D digits. So for positions ≥ D, `digit p m i = 0`, and `0 ≠ p-1` (since p ≥ 2), so the cascade must terminate within D positions.

Let me think about the two cases:
1. `cascade_length < D - (s+1)`: We can use `cascade_digit_neq` and `no_carry_beyond` to show no carries beyond position `s+1+L`, giving total carries ≤ `(s+1) + L`.
2. `cascade_length = D - (s+1)`: Then `(s+1) + L = D`, so we need `v_p ≤ D`. But `v_p ≤ log p (m+k) ≤ log p (p^D + k)`. Hmm, this needs more thought.

Actually, for case 2, let's look again at the carry positions more carefully. If all carries from position s+2 up to D are present (cascade fills all remaining D digits), we still need carries above position D. But `m < p^D` means `m % p^i = m` for `i ≥ D`, so `k % p^i + m % p^i = k % p^i + m < p^i` for `i` large enough. Actually that's not obviously true.

Wait, let me reconsider. The key is we want an upper bound on the number of carry positions. The carry positions are positions `i ∈ {1, ..., b-1}` where `p^i ≤ k % p^i + m % p^i`. 

For positions `i ≥ D` where `m < p^D`: `m % p^i = m` (since `m < p^D ≤ p^i`). And `k % p^i + m` could still be ≥ `p^i`. Hmm, actually for `i` large enough relative to `log(m+k)`, `k % p^i + m % p^i = k + m < p^i`, so no carry.

But in any case, the carry positions beyond position `s+1+L` can be bounded: if the cascade terminates within D (case 1), no carries beyond. If the cascade fills all D digits (case 2), we have `L = D - (s+1)` and the bound is `(s+1) + (D - (s+1)) = D`. We need to show `v_p ≤ D` in this case, which follows from `factorization_choose_le_log` since `log p (m+k) ≤ D` (approximately, since `m < p^D` and we can bound `m+k`).

Hmm, wait, `factorization_choose_le_log` gives `v_p(C(n,k)) ≤ log p n`, so `v_p(C(m+k,k)) ≤ log p (m+k)`. But `m+k < p^D + k`, and `log p (p^D + k)` might be ≥ D. So this approach might not directly give `v_p ≤ D`.

Let me reconsider. Actually, let me look at case 2 more carefully: if `cascade_length = D - (s+1)`, then `(s+1) + L = D`. Since the result says `v_p ≤ (s+1) + L = D`, and `factorization_choose_le_log` gives `v_p ≤ log_p(m+k)`. We have `m < p^D` and `k ≥ 1`, so `m + k < p^D + k`. If `k < p^D` (which is true when `s < D`), then `m + k < 2*p^D < p^{D+1}` (for `p ≥ 2`), so `log_p(m+k) ≤ D`. That works!

Actually wait, `factorization_choose_le_log` gives `log p (m+k)` as the bound, and `m + k ≤ p^D - 1 + k`. If `k ≤ p^D - 1`, then `m + k ≤ 2*(p^D - 1) < 2*p^D ≤ p^{D+1}`, so `log_p(m+k) ≤ D`.

But actually, the cascade_length being `D - (s+1)` means all positions `s+1, ..., D-1` have digit `p-1`. With `m < p^D`, this means `m ≥ (p-1) * p^{s+1} * (1 + p + ... + p^{D-s-2})`. In this case, the carries from positions `s+2` to `D` contribute at most `D - (s+1)` carries. And positions 1 through `s+1` contribute at most `s+1`. Total ≤ `D = (s+1) + L`. But we also need carries at positions > D...

Actually, let me take a simpler approach. Instead of case splitting on whether cascade terminates within D, I can simply bound the carries at each region:

- Carries at positions 1..s+1: at most s+1 (there are s+1 positions)
- Carries at positions s+2..s+1+L: at most L
- Carries at positions > s+1+L: these are 0 if the cascade terminates within D. If cascade_length = D-(s+1), then positions > D need to be handled.

Actually, let me reconsider the proof approach. Looking at `valuation_gt_implies_cascade` more carefully:
🛠️ **Executing tool: read**
Now I see the pattern clearly. The existing `valuation_gt_implies_cascade` uses the same structure but with the additional assumption that `L < D - (s+1)` (derived from `L < D/6 - s` and `D ≥ 16`).

For `valuation_le_cascade`, we need to handle BOTH cases:
1. `L < D - (s+1)`: Use `cascade_digit_neq` and `no_carry_beyond` (same as existing code).
2. `L = D - (s+1)`: In this case `(s+1) + L = D`, and we need `v_p ≤ D`. This follows from `Nat.factorization_choose_le_log` + the bound `log_p(m+k) < D + 1` (since `m < p^D` and `k ≥ 1` with `k < p^D` when `s < D`; or more directly, `m + k ≤ p^D + k - 1`... hmm).

Wait, actually let me check: `Nat.factorization_choose_le_log` says `(choose n k).factorization p ≤ log p n`. So `v_p(C(m+k,k)) ≤ log_p(m+k)`. Since `m < p^D`, we have `m + k < p^D + k`. And `log_p(p^D + k) ≤ D` if `p^D + k < p^{D+1}`, i.e., `k < p^D * (p-1)`, which is true if `k < p^D` (since `p ≥ 2`).

And `k < p^D` iff `log_p k < D`, i.e., `s < D`. But what if `s ≥ D`? Then `cascade_length = 0` (since `D - (s+1)` would be 0 via nat subtraction), so we need `v_p ≤ s + 1`.

Actually, `Nat.factorization_choose_le_log` gives `v_p ≤ log_p(m+k)`. And `log_p(m+k) ≤ log_p(m) + log_p(k) + 1` or something... Hmm, that's not a standard bound.

Wait, but actually `v_p(C(m+k,k)) ≤ log_p(m+k)` from `factorization_choose_le_log`. And `m + k < p^D + k ≤ p^D + p^{s+1}`. Hmm this is getting complicated.

Let me take a different approach. Instead of case-splitting on whether L = D-(s+1), let me use the approach of the NL proof directly.

Actually, re-reading the NL proof of Lemma A2: "The carries at positions 0, 1, ..., s contribute at most s+1 to the total." This is trivially true since there are s+1 positions. "Carries at positions > s + L are all 0." This is because (a) if the cascade terminates within the digit range, `cascade_digit_neq` gives us a non-(p-1) digit, and `no_carry_beyond` kills carries above; (b) if the cascade fills all remaining digits, then for `m < p^D`, positions ≥ D have digit 0, which is not p-1 (for p ≥ 2).

So actually, for case (b), we'd use the fact that `digit p m D = 0` (since `m < p^D`) and `0 ≠ p - 1`, and then `no_carry_beyond` at position D.

Wait, but `cascade_length` is defined as `takeWhile` over positions `s+1, s+2, ...` checking for digit p-1 within D. If `m < p^D`, then `digit p m j = 0` for `j ≥ D`. So the cascade naturally stops because:
- If it fills all D-(s+1) positions (all digits s+1..D-1 are p-1), then `L = D-(s+1)`.
- Position `s+1+L = D` has digit 0 ≠ p-1.
- So `no_carry_beyond` applies at position D, killing all carries above D.

But actually, `cascade_digit_neq` requires `L < D - (s+1)`. In case 2, `L = D - (s+1)`, so we can't use it directly. We need to handle this case separately.

Let me think about what API I need:

1. For `m < p^D`: `digit p m j = 0` for `j ≥ D`.
2. `0 ≠ p - 1` for `p ≥ 2`.

Let me check if there's a lemma for point 1:
```bash
$ cd /home/jarred/code/erdos-728b && grep -rn "digit.*lt\|digit.*zero\|digit.*pow\|digits_lt" Erdos/Digits.lean | head -20
```

🛠️ **Executing tool: read**
Good. Now let me check if there's a lemma for `digit p m j = 0` when `m < p^(j+1)` or `m < p^D` and `j ≥ D`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_digit.lean << 'EOF'
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log

open Nat

-- digit p m i = (m / p^i) % p
-- For m < p^D and i ≥ D: m / p^i = 0 since m < p^D ≤ p^i

example (p m D i : ℕ) (hp : p > 0) (hm : m < p ^ D) (hi : i ≥ D) : (m / p ^ i) % p = 0 := by
  have : p ^ D ≤ p ^ i := Nat.pow_le_pow_right hp hi
  have : m < p ^ i := lt_of_lt_of_le hm this
  rw [Nat.div_eq_zero_iff (by positivity : p ^ i > 0) |>.mpr this, Nat.zero_mod]
EOF
lake env lean /tmp/test_digit.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_digit.lean << 'EOF'
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log

open Nat

example (p m D i : ℕ) (hp : p > 0) (hm : m < p ^ D) (hi : i ≥ D) : (m / p ^ i) % p = 0 := by
  have h1 : p ^ D ≤ p ^ i := Nat.pow_le_pow_right hp hi
  have h2 : m < p ^ i := lt_of_lt_of_le hm h1
  have h3 : m / p ^ i = 0 := Nat.div_eq_of_lt h2
  rw [h3, Nat.zero_mod]
EOF
lake env lean /tmp/test_digit.lean 2>&1
```
Now let me plan the proof structure:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-vtv --status "Writing proof for valuation_le_cascade"
```
My plan:
1. Handle two cases: `cascade_length < D - (s+1)` (cascade terminates within D) and `cascade_length ≥ D - (s+1)` (cascade fills remaining digits).
2. In case 1: Use `cascade_digit_neq` + `no_carry_beyond` to show carries only exist in `Ico 1 (s+2+L)`, giving `v_p ≤ s+1+L`.
3. In case 2: `L ≥ D - (s+1)`, so `(s+1) + L ≥ D ≥ log_p(m+k) ≥ v_p`. Use `factorization_choose_le_log`.

Let me first check `factorization_choose_le_log` more carefully:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_choose.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization

#check @Nat.factorization_choose_le_log
-- (choose n k).factorization p ≤ log p n
EOF
lake env lean /tmp/test_choose.lean 2>&1
```
So `(choose (m+k) k).factorization p ≤ log p (m+k)`. And `m + k < p^D + k`. Since `k ≤ p^{s+1} - 1` (from `s = log p k`), if `s+1 ≤ D`, then `k < p^D`, so `m+k < 2*p^D ≤ p*p^D = p^{D+1}`, thus `log_p(m+k) ≤ D`.

But what if `s+1 > D`? Then `cascade_length = 0` (since `D - (s+1) = 0` in nat), so the bound becomes `v_p ≤ s+1`. And `factorization_choose_le_log` gives `v_p ≤ log_p(m+k)`. We need `log_p(m+k) ≤ s+1`. But `m < p^D` and `k ≥ 1`, so `m + k ≤ p^D + k - 1 + 1 = p^D + k`. And `log_p(p^D + k) ≤ ...`. Hmm, if `D ≤ s`, then `p^D ≤ p^s ≤ k` (since `s = log_p k` means `p^s ≤ k`), so `m + k ≤ p^D + k ≤ 2k`. Thus `log_p(m+k) ≤ log_p(2k) ≤ log_p(k) + 1 = s + 1`. Wait, is `log_p(2k) ≤ s+1`? We have `s = log_p(k)`, so `k < p^{s+1}`, giving `2k < 2*p^{s+1} ≤ p*p^{s+1} = p^{s+2}` (for `p ≥ 2`). So `log_p(2k) ≤ s+1`. Yes!

OK so the two cases become:
- **Case s+1 ≤ D**: Either the cascade fills everything (L ≥ D-(s+1), so (s+1)+L ≥ D ≥ log_p(m+k) ≥ v_p), or the cascade terminates within D (use carry analysis).
- **Case s+1 > D**: `cascade_length = 0`, bound is `(s+1) + 0 = s+1`. And `v_p ≤ log_p(m+k) ≤ log_p(2k) ≤ s + 1`.

Actually, let me simplify. Let me just use:
- If `cascade_length L < D - (s+1)`: Use carry analysis (same as `valuation_gt_implies_cascade`).  
- Otherwise (`L ≥ D - (s+1)`, which includes `D ≤ s+1`): Use `factorization_choose_le_log` to bound `v_p ≤ D ≤ (s+1) + L`.

Let me verify the `factorization_choose_le_log` approach for the second case:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_bound.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log

open Nat

-- log_p(m + k) ≤ D when m < p^D and k < p^D and p ≥ 2
example (p m k D : ℕ) (hp : p ≥ 2) (hm : m < p ^ D) (hk : k < p ^ D) (hD : D > 0) :
    Nat.log p (m + k) ≤ D := by
  apply Nat.log_lt_of_lt_pow (by omega)
  calc m + k < p ^ D + p ^ D := by omega
    _ = 2 * p ^ D := by ring
    _ ≤ p * p ^ D := by nlinarith
    _ = p ^ (D + 1) := by rw [pow_succ]
EOF
lake env lean /tmp/test_bound.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_bound.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log

open Nat

example (p m k D : ℕ) (hp : p ≥ 2) (hm : m < p ^ D) (hk : k < p ^ D) (hD : D > 0) :
    Nat.log p (m + k) ≤ D := by
  have : m + k < p ^ (D + 1) := by
    calc m + k < p ^ D + p ^ D := by omega
      _ = 2 * p ^ D := by ring
      _ ≤ p * p ^ D := by nlinarith
      _ = p ^ (D + 1) := by rw [pow_succ]
  exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) this)
EOF
lake env lean /tmp/test_bound.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_bound.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log

open Nat

example (p m k D : ℕ) (hp : p ≥ 2) (hm : m < p ^ D) (hk : k < p ^ D) (hD : D > 0) :
    Nat.log p (m + k) ≤ D := by
  have h1 : m + k < p ^ (D + 1) := by
    have : 2 * p ^ D ≤ p ^ (D + 1) := by
      rw [pow_succ]; nlinarith [Nat.one_le_pow D p (by omega)]
    omega
  have h2 : Nat.log p (m + k) < D + 1 :=
    Nat.log_lt_of_lt_pow (by omega) h1
  omega
EOF
lake env lean /tmp/test_bound.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_bound.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log

open Nat

#check @Nat.log_lt_of_lt_pow
EOF
lake env lean /tmp/test_bound.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_bound.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log

open Nat

example (p m k D : ℕ) (hp : p ≥ 2) (hm : m < p ^ D) (hk : k < p ^ D) (hD : D > 0) :
    Nat.log p (m + k) ≤ D := by
  have h1 : m + k < p ^ (D + 1) := by
    have : p ^ (D + 1) = p * p ^ D := pow_succ p D
    nlinarith [Nat.one_le_pow D p (by omega)]
  by_cases hmk : m + k = 0
  · simp [hmk]
  have h2 : Nat.log p (m + k) < D + 1 :=
    Nat.log_lt_of_lt_pow (by omega) h1
  omega
EOF
lake env lean /tmp/test_bound.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_bound.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log

open Nat

example (p m k D : ℕ) (hp : p ≥ 2) (hm : m < p ^ D) (hk : k < p ^ D) (hD : D > 0) :
    Nat.log p (m + k) ≤ D := by
  have h1 : m + k < p ^ (D + 1) := by
    have h := pow_succ p D  -- p^(D+1) = p^D * p
    nlinarith [Nat.one_le_pow D p (by omega)]
  by_cases hmk : m + k = 0
  · simp [hmk]
  have h2 : Nat.log p (m + k) < D + 1 :=
    Nat.log_lt_of_lt_pow (by omega) h1
  omega
EOF
lake env lean /tmp/test_bound.lean 2>&1
```
Now let me also check the case where `s+1 > D`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_bound2.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log

open Nat

-- When s + 1 > D, i.e. log p k ≥ D, we have p^D ≤ k, so m < p^D ≤ k
-- Thus m + k ≤ 2k (approximately), and log_p(m+k) ≤ log_p(2k) ≤ s + 1
-- Actually: m + k < p^D + k ≤ k + k = 2k ≤ 2*p^{s+1} ≤ p*p^{s+1} = p^{s+2}
-- So log_p(m+k) ≤ s+1

example (p m k : ℕ) (hp : p ≥ 2) (hm : m < p ^ D) (hk : k ≥ 1) (hD : D ≤ Nat.log p k) :
    Nat.log p (m + k) ≤ Nat.log p k + 1 := by
  sorry
EOF
lake env lean /tmp/test_bound2.lean 2>&1
```
Let me now actually construct the full proof. I'll structure it as:

**Case 1**: `cascade_length < D - (s+1)` — Use Kummer + carry analysis.
**Case 2**: `cascade_length ≥ D - (s+1)` — Use `factorization_choose_le_log`.
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_valuation.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real

namespace Erdos728

section TestCascade

variable {p : ℕ} (k : ℕ) (D : ℕ)

-- Test: can we access the definitions and lemmas?
#check @cascade_length
#check @cascade_digit_neq
#check @no_carry_beyond
#check @carry_propagate

end TestCascade

end Erdos728
EOF
lake env lean /tmp/test_valuation.lean 2>&1
```
`cascade_digit_neq` and `no_carry_beyond` are `private`. I need to either:
1. Write the proof inline in `Lemma3Counting.lean` (which has access to private lemmas)
2. Make them non-private
3. Reprove equivalent results

Since the proof of `valuation_le_cascade` is right next to these private lemmas in the same file, I should be able to use them. Let me write the proof directly in `Lemma3Counting.lean`.

Let me first write and test the proof structure:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_val.lean << 'EOF'
import Erdos.Digits
import Erdos.Lemma3Common

open Nat BigOperators Finset

namespace Erdos728

-- Minimal standalone test to verify the proof approach
-- The actual proof goes in Lemma3Counting.lean where private lemmas are accessible

-- We need to show:
-- padicValNat p ((m + k).choose k) ≤ (log p k + 1) + cascade_length k D m
-- 
-- Strategy:
-- Case 1: cascade_length < D - (s+1) → carry analysis bounds v_p ≤ s+1+L
-- Case 2: cascade_length ≥ D - (s+1) → factorization_choose_le_log bounds v_p ≤ log_p(m+k) ≤ D ≤ s+1+L

end Erdos728
EOF
lake env lean /tmp/test_val.lean 2>&1
```
Good. Now let me write the actual proof. I'll write it directly in the file:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_val2.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log

open Nat

-- Test: digit p m i = 0 for m < p^D and i ≥ D
lemma digit_zero_of_lt_pow (p m D i : ℕ) (hp : p > 0) (hm : m < p ^ D) (hi : i ≥ D) :
    (m / p ^ i) % p = 0 := by
  have h1 : p ^ D ≤ p ^ i := Nat.pow_le_pow_right hp hi
  have h2 : m < p ^ i := lt_of_lt_of_le hm h1
  rw [Nat.div_eq_of_lt h2, Nat.zero_mod]

-- Test: log bound when both m and k are < p^D  
lemma log_mk_le_D (p m k D : ℕ) (hp : p ≥ 2) (hm : m < p ^ D) (hk_lt : k < p ^ D) :
    Nat.log p (m + k) ≤ D := by
  by_cases hmk : m + k = 0
  · simp [hmk]
  have h1 : m + k < p ^ (D + 1) := by
    have h := pow_succ p D
    nlinarith [Nat.one_le_pow D p (by omega)]
  exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) h1)
EOF
lake env lean /tmp/test_val2.lean 2>&1
```
Now let me write the actual proof. The key insight for Case 2 (when cascade fills everything):
- `L ≥ D - (s+1)` means `(s+1) + L ≥ D`.
- `v_p ≤ log_p(m+k)` by `factorization_choose_le_log`.
- We need `log_p(m+k) ≤ D`.
- If `s+1 ≤ D`, then `k < p^{s+1} ≤ p^D`, so both `m, k < p^D`, giving `m+k < 2*p^D ≤ p^{D+1}`, so `log_p(m+k) ≤ D`.
- If `s+1 > D`, then `L = 0` (cascade length defined over `D-(s+1) = 0` range), so bound is `s+1`. Since `v_p ≤ log_p(m+k)`, we need `log_p(m+k) ≤ s+1`. We have `m < p^D ≤ p^s ≤ k` (when `s ≥ D`... wait, `p^s ≤ k` only if `s ≤ log_p k`).

Actually, `s = log_p k`, so `p^s ≤ k` (definition of log). If `s ≥ D`, then `p^D ≤ p^s ≤ k`, so `m < p^D ≤ k`, giving `m + k < 2k`. And `log_p(2k) ≤ log_p(k) + 1 = s + 1` (since `2k < p * k ≤ p * p^s ≤ p^{s+1}` when `p ≥ 2`... wait, `k < p^{s+1}` by definition of log).

So `m + k < 2k ≤ 2 * (p^{s+1} - 1) < 2 * p^{s+1} ≤ p * p^{s+1} = p^{s+2}`, giving `log_p(m+k) ≤ s + 1`.

OK, let me combine both sub-cases. In Case 2, I need to show `v_p ≤ (s+1) + L`. I know `v_p ≤ log_p(m+k)` and `(s+1) + L ≥ (s+1) + (D - (s+1))` or `(s+1) + 0` depending on whether `s+1 ≤ D` or not.

Let me try a unified approach: `log_p(m+k) ≤ (s+1) + cascade_length` when `cascade_length ≥ D - (s+1)`.

Case 2a: `s+1 ≤ D`. Then `cascade_length ≥ D - (s+1)`, so `(s+1) + cascade_length ≥ D`. And `log_p(m+k) ≤ D`. Done.

Case 2b: `s+1 > D`. Then `D - (s+1) = 0` in ℕ, so `cascade_length ≥ 0` always. We need `log_p(m+k) ≤ s + 1 + cascade_length`. Since `cascade_length ≥ 0`, it suffices to show `log_p(m+k) ≤ s + 1`.

Let me write the proof now:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_full.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log

open Nat

-- Needed helper: log_p(m+k) ≤ s+1 when m < p^D and D ≤ s
lemma log_add_le_log_succ (p m k : ℕ) (hp : p ≥ 2) (hm : m < p ^ D) (hk : k ≥ 1)
    (hDs : D ≤ Nat.log p k) :
    Nat.log p (m + k) ≤ Nat.log p k + 1 := by
  have hs := Nat.log_lt_of_lt_pow (by omega : k ≠ 0) (Nat.lt_pow_succ_log_self (by omega) k)
  -- k < p^{s+1}
  -- m < p^D ≤ p^s ≤ k
  have hpD_le : p ^ D ≤ k := le_trans (Nat.pow_le_pow_right (by omega) hDs) (Nat.log_le_self_of_pos)
  sorry
EOF
lake env lean /tmp/test_full.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -r "log.*le.*self\|pow_log_le" .lake/packages/mathlib/Mathlib/Data/Nat/Log.lean | head -10
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_full.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log

open Nat

-- log_p(m+k) ≤ s+1 when m < p^D, D ≤ s, k ≥ 1
lemma log_add_le_succ_log (p m k D : ℕ) (hp : p ≥ 2) (hm : m < p ^ D) (hk : k ≥ 1)
    (hDs : D ≤ Nat.log p k) :
    Nat.log p (m + k) ≤ Nat.log p k + 1 := by
  set s := Nat.log p k
  -- k < p^{s+1}
  have hk_lt : k < p ^ (s + 1) := Nat.lt_pow_succ_log_self (by omega) k
  -- p^D ≤ p^s ≤ k
  have hpD_le_ps : p ^ D ≤ p ^ s := Nat.pow_le_pow_right (by omega) hDs
  -- m + k < p^D + k ≤ k + k = 2k
  have hmk_lt : m + k < 2 * k := by omega
  -- 2k ≤ 2 * (p^{s+1} - 1) < 2 * p^{s+1} ≤ p * p^{s+1} = p^{s+2}
  have h2k_lt : 2 * k < p ^ (s + 2) := by
    calc 2 * k < 2 * p ^ (s + 1) := by omega
      _ ≤ p * p ^ (s + 1) := by nlinarith
      _ = p ^ (s + 2) := by rw [pow_succ p (s + 1)]
  have hmk_lt_pow : m + k < p ^ (s + 2) := by omega
  by_cases hmk : m + k = 0
  · simp [hmk]
  exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hmk_lt_pow)
EOF
lake env lean /tmp/test_full.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_full.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log

open Nat

-- log_p(m+k) ≤ s+1 when m < p^D, D ≤ s, k ≥ 1
lemma log_add_le_succ_log (p m k D : ℕ) (hp : p ≥ 2) (hm : m < p ^ D) (hk : k ≥ 1)
    (hDs : D ≤ Nat.log p k) :
    Nat.log p (m + k) ≤ Nat.log p k + 1 := by
  set s := Nat.log p k
  have hk_lt : k < p ^ (s + 1) := Nat.lt_pow_succ_log_self (by omega) k
  have hpD_le_ps : p ^ D ≤ p ^ s := Nat.pow_le_pow_right (by omega) hDs
  have hps_le_k : p ^ s ≤ k := Nat.pow_log_le_self p (by omega)
  have hmk_lt : m + k < 2 * k := by omega
  have h2k_lt : 2 * k < p ^ (s + 2) := by
    have : 2 * p ^ (s + 1) ≤ p * p ^ (s + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [← pow_succ] at this
    omega
  have hmk_lt_pow : m + k < p ^ (s + 2) := by omega
  by_cases hmk : m + k = 0
  · simp [hmk]
  exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hmk_lt_pow)
EOF
lake env lean /tmp/test_full.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_full.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log

open Nat

lemma log_add_le_succ_log (p m k D : ℕ) (hp : p ≥ 2) (hm : m < p ^ D) (hk : k ≥ 1)
    (hDs : D ≤ Nat.log p k) :
    Nat.log p (m + k) ≤ Nat.log p k + 1 := by
  set s := Nat.log p k
  have hk_lt : k < p ^ (s + 1) := Nat.lt_pow_succ_log_self (by omega) k
  have hps_le_k : p ^ s ≤ k := Nat.pow_log_le_self p (by omega)
  have hmk_lt : m + k < 2 * k := by
    calc m + k < p ^ D + k := by omega
      _ ≤ p ^ s + k := by omega
      _ ≤ k + k := by omega
      _ = 2 * k := by ring
  have hmk_lt_pow : m + k < p ^ (s + 2) := by
    have h1 : p ^ (s + 2) = p ^ (s + 1) * p := pow_succ p (s + 1)
    nlinarith [Nat.one_le_pow (s + 1) p (by omega)]
  by_cases hmk : m + k = 0
  · simp [hmk]
  exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hmk_lt_pow)
EOF
lake env lean /tmp/test_full.lean 2>&1
```
The issue is omega can't relate `p^D` and `p^s`. Let me fix:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_full.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log

open Nat

lemma log_add_le_succ_log (p m k D : ℕ) (hp : p ≥ 2) (hm : m < p ^ D) (hk : k ≥ 1)
    (hDs : D ≤ Nat.log p k) :
    Nat.log p (m + k) ≤ Nat.log p k + 1 := by
  set s := Nat.log p k
  have hk_lt : k < p ^ (s + 1) := Nat.lt_pow_succ_log_self (by omega) k
  have hps_le_k : p ^ s ≤ k := Nat.pow_log_le_self p (by omega)
  have hpD_le_ps : p ^ D ≤ p ^ s := Nat.pow_le_pow_right (by omega) hDs
  have hmk_lt : m + k ≤ 2 * k := by linarith
  have hmk_lt_pow : m + k < p ^ (s + 2) := by
    have h1 : p ^ (s + 2) = p ^ (s + 1) * p := pow_succ p (s + 1)
    nlinarith [Nat.one_le_pow (s + 1) p (by omega)]
  by_cases hmk : m + k = 0
  · simp [hmk]
  exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hmk_lt_pow)
EOF
lake env lean /tmp/test_full.lean 2>&1
```
Now let me also verify the main bound for Case 2a:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_case2a.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log

open Nat

lemma log_mk_le_D (p m k D : ℕ) (hp : p ≥ 2) (hm : m < p ^ D) (hk_lt : k < p ^ D) :
    Nat.log p (m + k) ≤ D := by
  by_cases hmk : m + k = 0
  · simp [hmk]
  have h1 : m + k < p ^ (D + 1) := by
    have h := pow_succ p D -- p^(D+1) = p^D * p
    nlinarith [Nat.one_le_pow D p (by omega)]
  exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) h1)
EOF
lake env lean /tmp/test_case2a.lean 2>&1
```
Now let me write the complete proof. I'll approach it with a single case split:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_main.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset

-- Test that factorization_choose_le_log can bound v_p
-- We can't test with private lemmas, but we verify the math is right

example (p m k : ℕ) (hp : Nat.Prime p) :
    padicValNat p ((m + k).choose k) ≤ Nat.log p (m + k) := by
  rw [← Nat.factorization_def _ hp]
  exact Nat.factorization_choose_le_log
EOF
lake env lean /tmp/test_main.lean 2>&1
```
Now I have all the pieces. Let me write the actual proof in the file:
🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1
```
Two issues:
1. `cascade_digit_neq` is private and I can't access it. Wait, it's in the same file though. Let me check the section structure.
2. Various omega failures in Case 2.

The `cascade_digit_neq` is defined in `section ResidueCounting` while `valuation_le_cascade` is in `section Cascade`. Let me check:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "^section\|^end\|cascade_digit_neq\|valuation_le_cascade\|no_carry_beyond" Erdos/Lemma3Counting.lean | head -30
```
I see the problem. `cascade_digit_neq` and `no_carry_beyond` are private and defined in `section ResidueCounting` (line 605, 623), but I'm trying to use them in `section Cascade` (line 192). Since they're private, they're only accessible within their section scope — and since they're defined *after* the Cascade section, they're not available.

I have two options:
1. Move the private lemmas before `section Cascade` or into it
2. Prove equivalent inline statements

Let me move them or make them non-private. Actually, they're quite long. Better approach: I should prove `valuation_le_cascade` using its own proof, potentially duplicating some of the cascade/carry logic inline.

Actually, the cleanest approach is to move `cascade_digit_neq` and `no_carry_beyond` into the `Cascade` section (before `valuation_le_cascade`). They logically belong there.

Let me look at the dependencies of these lemmas:
🛠️ **Executing tool: read**
I see — `cascade_digit_neq` and `no_carry_beyond` are in the `ResidueCounting` section but they also depend on `not_pred_at_takeWhile_length` which is also in that section. Let me check if `not_pred_at_takeWhile_length` is defined earlier:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "not_pred_at_takeWhile_length" Erdos/Lemma3Counting.lean
```
All three lemmas (`not_pred_at_takeWhile_length`, `cascade_digit_neq`, `no_carry_beyond`) are in `ResidueCounting` section. Rather than moving them, let me prove the relevant parts directly in my proof of `valuation_le_cascade`. This is cleaner.

For Case 1, I need:
1. The digit at position `s+1+L` is not `p-1` (cascade terminates) — I can prove this inline using the `takeWhile` structure.
2. No carry beyond this position — I can prove this inline using `carry_propagate`.

Actually, an even better approach: let me just move these three lemmas to the Cascade section where they logically belong. They don't depend on anything specific to ResidueCounting.
🛠️ **Executing tool: read**
Let me take a different approach — I'll just add the needed helper lemmas right before `valuation_le_cascade` in the Cascade section, without `private`:
🛠️ **Executing tool: read**
I'll add helper lemmas right before `valuation_le_cascade`:
🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | grep -E "error:|warning.*sorry|Building Erdos" | head -20
```
No errors! The build succeeded. Let me verify the sorry for `valuation_le_cascade` is gone:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "sorry" Erdos/Lemma3Counting.lean
```
The `valuation_le_cascade` sorry has been successfully closed. Let me verify by checking the specific line:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "valuation_le_cascade" Erdos/Lemma3Counting.lean
```
Now let me do a full build to make sure everything compiles:
```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | tail -5
```
Build completed successfully. Let me commit the changes:
```bash
$ cd /home/jarred/code/erdos-728b && git add -A && git commit -m "Close sorry: valuation_le_cascade

Prove v_p(C(m+k,k)) ≤ (log_p(k)+1) + cascade_length using Kummer's
theorem and carry cascade analysis.

Proof structure:
- Case 1 (cascade terminates within D digits): Use carry_propagate
  to show no carries exist beyond position s+1+L, then count carries
  in Ico 1 (s+2+L) to get bound s+1+L.
- Case 2 (cascade fills remaining digits): Use factorization_choose_le_log
  to get v_p ≤ log_p(m+k) ≤ D ≤ (s+1)+L.

Added helper lemmas in Cascade section (primed versions of private lemmas
from ResidueCounting): cascade_digit_neq', no_carry_beyond',
not_pred_at_takeWhile_length', digit_zero_of_lt_pow."
```
