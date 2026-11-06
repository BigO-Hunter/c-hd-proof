import Submission.SsspStatement
import Frontier.CHD.Final
import Frontier.GateCCalc

/-!
# The `7/8` cap row: `Bound 1 (7/8) 1 (23/24) 0`

With at most `n · ⌊⌊log₂ n⌋^{7/8}⌋` edges the C-HD program of the fork
(`Frontier.CHD.Final.chd_exact_within87`) runs in `O(n · (log n)^{23/24})` time — a strictly wider
density window than the `3/4` row, and still better than the classical `O(n log n)` bound there
(`23/24 < 1`).

Everything is proved from `chd_exact_within87`, the trusted statement in
`Submission/SsspStatement.lean`, and real arithmetic.  The two analytic facts that make the wider cap
work (both with room to spare):

* the log factor: with `m ≤ 2 n ℓ^{7/8}` the argument of the density log is at most `4 ℓ`, so
  `m · log(m/(n+1)+2) ≤ 2nℓ^{7/8} · (2 + 24ℓ^{1/24}) ≤ 52 n ℓ^{23/24}`
  (`Real.log_le_rpow_div` at `s = 1/24`);
* the `2/3`-power term: `m^{1/3}(n log(n+2))^{2/3} ≤ (2nℓ^{7/8})^{1/3}(2nℓ)^{2/3} = 2nℓ^{23/24}`
  exactly (`key_eq87`).

Hence `Tchd n m ≤ 57 · n · ℓ^{23/24}` on the cap (constant `57`; the `3/4` bridge gets `21`).
-/

namespace BigOSpeedrun.DirectedSSSP.Cap87Row

open Frontier Frontier.RAM BigOSpeedrun.DirectedSSSP

/-! ### Glue (local copies of what `Submission/Validation.lean` provides; this file only depends on
the trusted statement, so it does not import that untrusted checker) -/

/-- `CorrectWithin` is monotone in the budget. -/
lemma correctWithin_mono {P : Program} {G : Graph} {s : Fin G.n} {x y : ℝ}
    (h : CorrectWithin P G s x) (hxy : x ≤ y) : CorrectWithin P G s y := by
  obtain ⟨f, r, h1, h2, h3⟩ := h
  exact ⟨f, r, h1, h2, h3.trans hxy⟩

lemma correctWithin_of_exact {P : Program} {G : Graph} {s : Fin G.n} {T : ℝ}
    (hE : P.Exact) (hR : P.RunsWithin G s T) : CorrectWithin P G s T := by
  obtain ⟨f, r, hr, hs⟩ := hE G s
  exact ⟨f, r, hr, hs, Program.runsWithin_unique hR hr⟩

lemma correctWithin_mono_const {P : Program} {G : Graph} {s : Fin G.n} {K T : ℝ}
    (h : CorrectWithin P G s (K * T)) (hT : 0 ≤ T) : CorrectWithin P G s ((|K| + 1) * T) :=
  correctWithin_mono h (mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) hT)

lemma one_le_log {n : ℕ} (hn : 16 ≤ n) : 1 ≤ Real.log n := by
  have h16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp 1 ≤ (n : ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  have := Real.log_le_log (Real.exp_pos 1) he
  rwa [Real.log_exp] at this

/-- `⌊log₂ n⌋ ≤ 2 log n`. -/
lemma natLog_le_two_log {n : ℕ} (hn : n ≠ 0) : ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * Real.log n := by
  have hp : ((2 : ℝ) ^ Nat.log 2 n) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn
  have := Real.log_le_log (by positivity) hp
  rw [Real.log_pow] at this
  have h2 := Real.log_two_gt_d9
  have hK : (0 : ℝ) ≤ (Nat.log 2 n : ℕ) := Nat.cast_nonneg _
  nlinarith

lemma tchd_nonneg (n m : ℕ) : 0 ≤ GateCCalc.Tchd n m := by
  unfold GateCCalc.Tchd
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : 0 ≤ Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) := Real.log_nonneg (by
    have : 0 ≤ (m : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith)
  have h2 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  have h3 := mul_nonneg hm h1
  have h4 := mul_nonneg (Real.rpow_nonneg hm ((1 : ℝ) / 3))
    (Real.rpow_nonneg (mul_nonneg hn h2) ((2 : ℝ) / 3))
  linarith

/-! ### The cap and the dispatch threshold `F87` -/

lemma sparse_iff {n m : ℕ} :
    Sparse 1 (7 / 8) n m ↔
      (m : ℝ) ≤ n * ⌊((Nat.log 2 n : ℕ) : ℝ) ^ ((7 : ℝ) / 8)⌋₊ := by
  unfold Sparse Cap
  norm_num

/-- The integer threshold is at most `⌊log₂ n⌋`. -/
lemma F87_le_natLog (n : ℕ) : GateCCalc.F87 n ≤ Nat.log 2 n := by
  unfold GateCCalc.F87
  set L := Nat.log 2 n
  rcases Nat.eq_zero_or_pos L with h | h
  · simp [h]
  · have h8 : L ^ 7 ≤ ((L ^ 2) ^ 2) ^ 2 := by
      calc L ^ 7 ≤ L ^ 8 := Nat.pow_le_pow_right h (by norm_num)
        _ = ((L ^ 2) ^ 2) ^ 2 := by ring
    calc Nat.sqrt (Nat.sqrt (Nat.sqrt (L ^ 7)))
        ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (((L ^ 2) ^ 2) ^ 2))) :=
          Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt h8))
      _ = L := by rw [Nat.sqrt_eq', Nat.sqrt_eq', Nat.sqrt_eq']

/-- A graph in the `7/8` race density range takes the C-HD branch of the dispatch. -/
lemma sparse_le_F87 {n m : ℕ} (h : Sparse 1 (7 / 8) n m) : m ≤ n * GateCCalc.F87 n := by
  have hk : ⌊((Nat.log 2 n : ℕ) : ℝ) ^ ((7 : ℝ) / 8)⌋₊ ≤ GateCCalc.F87 n := by
    unfold GateCCalc.F87
    exact GateCCalc.le_sqrt_sqrt_sqrt_of_real
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have h' : m ≤ n * ⌊((Nat.log 2 n : ℕ) : ℝ) ^ ((7 : ℝ) / 8)⌋₊ := by
    exact_mod_cast sparse_iff.1 h
  exact h'.trans (Nat.mul_le_mul_left n hk)

/-- The cap gives `m ≤ 2 n (log n)^{7/8}`. -/
lemma sparse_le_real {n m : ℕ} (hn : 16 ≤ n) (h : Sparse 1 (7 / 8) n m) :
    (m : ℝ) ≤ 2 * n * Real.log n ^ ((7 : ℝ) / 8) := by
  have hx : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hK := natLog_le_two_log (n := n) (by omega)
  have hK0 : (0 : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL : 0 ≤ Real.log n := by linarith [one_le_log hn]
  have h2 : (2 : ℝ) ^ ((7 : ℝ) / 8) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (7 : ℝ) / 8 ≤ 1 by norm_num)
  calc (m : ℝ) ≤ n * ⌊((Nat.log 2 n : ℕ) : ℝ) ^ ((7 : ℝ) / 8)⌋₊ := sparse_iff.1 h
    _ ≤ n * ((Nat.log 2 n : ℕ) : ℝ) ^ ((7 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg hK0 _)) hx
    _ ≤ n * (2 * Real.log n) ^ ((7 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hK0 hK (by norm_num)) hx
    _ = n * ((2 : ℝ) ^ ((7 : ℝ) / 8) * Real.log n ^ ((7 : ℝ) / 8)) := by
        rw [Real.mul_rpow (by norm_num) hL]
    _ ≤ n * (2 * Real.log n ^ ((7 : ℝ) / 8)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hL _)) hx
    _ = _ := by ring

/-! ### `Tchd` on the `7/8` cap -/

lemma key_eq87 {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (A * B ^ ((7 : ℝ) / 8)) ^ ((1 : ℝ) / 3) * (A * B) ^ ((2 : ℝ) / 3) =
      A * B ^ ((23 : ℝ) / 24) := by
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg hB.le _), Real.mul_rpow hA.le hB.le,
    ← Real.rpow_mul hB.le]
  have e1 : A ^ ((1 : ℝ) / 3) * A ^ ((2 : ℝ) / 3) = A := by
    rw [← Real.rpow_add hA]
    norm_num
  have e2 : B ^ ((7 : ℝ) / 8 * (1 / 3)) * B ^ ((2 : ℝ) / 3) = B ^ ((23 : ℝ) / 24) := by
    rw [← Real.rpow_add hB]
    norm_num
  calc _ = (A ^ ((1 : ℝ) / 3) * A ^ ((2 : ℝ) / 3)) *
        (B ^ ((7 : ℝ) / 8 * (1 / 3)) * B ^ ((2 : ℝ) / 3)) := by ring
    _ = _ := by rw [e1, e2]

/-- On the `7/8` cap, `Tchd n m ≤ 57 · n · (log n)^{23/24}` for `n ≥ 16`. -/
lemma tchd_le {n m : ℕ} (hn : 16 ≤ n) (hm : (m : ℝ) ≤ 2 * n * Real.log n ^ ((7 : ℝ) / 8)) :
    GateCCalc.Tchd n m ≤ 57 * ((n : ℝ) * Real.log n ^ ((23 : ℝ) / 24)) := by
  have hx16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (0 : ℝ) < n := by linarith
  set ℓ := Real.log n with hℓ
  have hℓ1 : 1 ≤ ℓ := one_le_log hn
  have hℓ0 : 0 < ℓ := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h2324 : 1 ≤ ℓ ^ ((23 : ℝ) / 24) := Real.one_le_rpow hℓ1 (by norm_num)
  have h78 : ℓ ^ ((7 : ℝ) / 8) ≤ ℓ ^ ((23 : ℝ) / 24) :=
    Real.rpow_le_rpow_of_exponent_le hℓ1 (by norm_num)
  have h78le : ℓ ^ ((7 : ℝ) / 8) ≤ ℓ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hℓ1 (show (7 : ℝ) / 8 ≤ 1 by norm_num)
  -- First two terms.
  have t1 : (n : ℝ) ≤ n * ℓ ^ ((23 : ℝ) / 24) := le_mul_of_one_le_right hx.le h2324
  have t2 : (m : ℝ) ≤ 2 * (n * ℓ ^ ((23 : ℝ) / 24)) := by
    calc (m : ℝ) ≤ 2 * n * ℓ ^ ((7 : ℝ) / 8) := hm
      _ ≤ 2 * n * ℓ ^ ((23 : ℝ) / 24) := mul_le_mul_of_nonneg_left h78 (by positivity)
      _ = _ := by ring
  -- Third term: `log (m/(n+1) + 2) ≤ 26 ℓ^{1/24}`.
  have hq : (m : ℝ) / (n + 1) ≤ 2 * ℓ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h78le hx.le]
  have harg0 : 0 < (m : ℝ) / (n + 1) + 2 := by positivity
  have hlog : Real.log ((m : ℝ) / (n + 1) + 2) ≤ 26 * ℓ ^ ((1 : ℝ) / 24) := by
    have hle : (m : ℝ) / (n + 1) + 2 ≤ 4 * ℓ := by linarith
    have h4 : Real.log 4 < 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      have := Real.log_two_lt_d9
      linarith
    have hll : Real.log ℓ ≤ ℓ ^ ((1 : ℝ) / 24) / (1 / 24) :=
      Real.log_le_rpow_div hℓ0.le (by norm_num)
    calc Real.log ((m : ℝ) / (n + 1) + 2) ≤ Real.log (4 * ℓ) := Real.log_le_log harg0 hle
      _ = Real.log 4 + Real.log ℓ := Real.log_mul (by norm_num) hℓ0.ne'
      _ ≤ 2 + 24 * ℓ ^ ((1 : ℝ) / 24) := by
          have : ℓ ^ ((1 : ℝ) / 24) / (1 / 24) = 24 * ℓ ^ ((1 : ℝ) / 24) := by ring
          linarith
      _ ≤ 26 * ℓ ^ ((1 : ℝ) / 24) := by
          have h1 : (1 : ℝ) ≤ ℓ ^ ((1 : ℝ) / 24) := Real.one_le_rpow hℓ1 (by norm_num)
          linarith
  have t3 : (m : ℝ) * Real.log ((m : ℝ) / (n + 1) + 2) ≤ 52 * (n * ℓ ^ ((23 : ℝ) / 24)) := by
    have hlog0 : 0 ≤ Real.log ((m : ℝ) / (n + 1) + 2) := Real.log_nonneg (by
      have : 0 ≤ (m : ℝ) / (n + 1) := by positivity
      linarith)
    have e : ℓ ^ ((7 : ℝ) / 8) * ℓ ^ ((1 : ℝ) / 24) = ℓ ^ ((11 : ℝ) / 12) := by
      rw [← Real.rpow_add hℓ0]
      norm_num
    have hstep : ℓ ^ ((11 : ℝ) / 12) ≤ ℓ ^ ((23 : ℝ) / 24) :=
      Real.rpow_le_rpow_of_exponent_le hℓ1 (by norm_num)
    calc (m : ℝ) * Real.log ((m : ℝ) / (n + 1) + 2)
        ≤ (2 * n * ℓ ^ ((7 : ℝ) / 8)) * (26 * ℓ ^ ((1 : ℝ) / 24)) :=
          mul_le_mul hm hlog hlog0 (mul_nonneg (by positivity) (Real.rpow_nonneg hℓ0.le _))
      _ = 52 * (n * (ℓ ^ ((7 : ℝ) / 8) * ℓ ^ ((1 : ℝ) / 24))) := by ring
      _ = 52 * (n * ℓ ^ ((11 : ℝ) / 12)) := by rw [e]
      _ ≤ 52 * (n * ℓ ^ ((23 : ℝ) / 24)) := by
          nlinarith [mul_le_mul_of_nonneg_left hstep hx.le]
  -- Fourth term: `m^{1/3} (n log(n+2))^{2/3} ≤ 2 n ℓ^{23/24}`.
  have hlog2 : Real.log ((n : ℝ) + 2) ≤ 2 * ℓ := by
    have : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * ℓ := by rw [Real.log_pow, ← hℓ]; norm_num
  have t4 : (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) ≤
      2 * (n * ℓ ^ ((23 : ℝ) / 24)) := by
    have hA : (0 : ℝ) < 2 * n := by positivity
    have hlogn2 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
    calc (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3)
        ≤ (2 * n * ℓ ^ ((7 : ℝ) / 8)) ^ ((1 : ℝ) / 3) * (2 * n * ℓ) ^ ((2 : ℝ) / 3) := by
          apply mul_le_mul
          · exact Real.rpow_le_rpow hm0 hm (by norm_num)
          · refine Real.rpow_le_rpow (mul_nonneg hx.le hlogn2) ?_ (by norm_num)
            nlinarith [mul_le_mul_of_nonneg_left hlog2 hx.le]
          · exact Real.rpow_nonneg (mul_nonneg hx.le hlogn2) _
          · exact Real.rpow_nonneg (mul_nonneg hA.le (Real.rpow_nonneg hℓ0.le _)) _
      _ = 2 * n * ℓ ^ ((23 : ℝ) / 24) := key_eq87 hA hℓ0
      _ = _ := by ring
  unfold GateCCalc.Tchd
  linarith

/-! ### `Tdisp F87` on every graph -/

lemma tdisp_nonneg (n m : ℕ) : 0 ≤ GateCTarget.Tdisp GateCCalc.F87 n m := by
  unfold GateCTarget.Tdisp
  split_ifs
  · exact tchd_nonneg n m
  · positivity

/-- `Tdisp F87 ≤ 8 (n+1)(m+1)` on every graph with `n ≥ 1`. -/
lemma tdisp_le_poly {n m : ℕ} (hn : 1 ≤ n) :
    GateCTarget.Tdisp GateCCalc.F87 n m ≤ 8 * (((n : ℝ) + 1) * ((m : ℝ) + 1)) := by
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hP : 0 ≤ ((n : ℝ) + 1) * ((m : ℝ) + 1) := by positivity
  unfold GateCTarget.Tdisp
  split_ifs with hd
  swap
  · linarith
  -- `F87 n ≤ 2 n`.
  have hF : (GateCCalc.F87 n : ℝ) ≤ 2 * n := by
    have h1 : (GateCCalc.F87 n : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) := by
      exact_mod_cast F87_le_natLog n
    have h2 := natLog_le_two_log (n := n) (by omega)
    have h3 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n)
    linarith
  have hmF : (m : ℝ) ≤ n * GateCCalc.F87 n := by exact_mod_cast hd
  have hq : (m : ℝ) / ((n : ℝ) + 1) ≤ 2 * n := by
    rw [div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ GateCCalc.F87 n := Nat.cast_nonneg _
    nlinarith
  -- Third term.
  have t3 : (m : ℝ) * Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) ≤
      2 * (((n : ℝ) + 1) * ((m : ℝ) + 1)) := by
    have hl := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (m : ℝ) / ((n : ℝ) + 1) + 2)
    calc (m : ℝ) * Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) ≤ m * (2 * n + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hm0
      _ ≤ _ := by nlinarith
  -- Fourth term.
  have t4 : (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) ≤
      4 * (((n : ℝ) + 1) * ((m : ℝ) + 1)) := by
    have hy0 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hlog0 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hY : (n : ℝ) * Real.log ((n : ℝ) + 2) ≤ 2 * ((n : ℝ) + 2) ^ ((3 : ℝ) / 2) := by
      have hl : Real.log ((n : ℝ) + 2) ≤ ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) / (1 / 2) :=
        Real.log_le_rpow_div hy0.le (by norm_num)
      have e : ((n : ℝ) + 2) ^ ((3 : ℝ) / 2) = ((n : ℝ) + 2) * ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) := by
        rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hy0, Real.rpow_one]
      have hs : 0 ≤ ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hy0.le _
      have h2x : ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) / (1 / 2) = 2 * ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) := by
        ring
      rw [e]
      calc (n : ℝ) * Real.log ((n : ℝ) + 2) ≤ ((n : ℝ) + 2) * (2 * ((n : ℝ) + 2) ^ ((1 : ℝ) / 2)) := by
            apply mul_le_mul (by linarith) (by linarith) hlog0 (by linarith)
        _ = _ := by ring
    have hYp : ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) ≤ 4 * ((n : ℝ) + 1) := by
      calc ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3)
          ≤ (2 * ((n : ℝ) + 2) ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3) :=
            Real.rpow_le_rpow (mul_nonneg (by positivity) hlog0) hY (by norm_num)
        _ = (2 : ℝ) ^ ((2 : ℝ) / 3) * ((n : ℝ) + 2) := by
            rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hy0.le _), ← Real.rpow_mul hy0.le]
            norm_num
        _ ≤ 2 * ((n : ℝ) + 2) := by
            apply mul_le_mul_of_nonneg_right _ hy0.le
            simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
              (show (2 : ℝ) / 3 ≤ 1 by norm_num)
        _ ≤ 4 * ((n : ℝ) + 1) := by linarith
    have hm13 : (m : ℝ) ^ ((1 : ℝ) / 3) ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        simp
      · have : (1 : ℝ) ≤ m := by exact_mod_cast h0
        simpa using Real.rpow_le_rpow_of_exponent_le this (show (1 : ℝ) / 3 ≤ 1 by norm_num)
    calc (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3)
        ≤ m * (4 * ((n : ℝ) + 1)) :=
          mul_le_mul hm13 hYp (Real.rpow_nonneg (mul_nonneg (by positivity) hlog0) _) hm0
      _ ≤ _ := by nlinarith
  have hnm : (n : ℝ) + m ≤ ((n : ℝ) + 1) * ((m : ℝ) + 1) := by nlinarith
  unfold GateCCalc.Tchd
  linarith

/-! ### The row -/

/-- An exact program within `K · Tdisp F87 n m` on every graph proves the `7/8` row. -/
theorem bound_of_tdisp {P : Program} (hE : P.Exact) {K : ℝ}
    (hR : ∀ (G : Graph) (s : Fin G.n),
      P.RunsWithin G s (K * GateCTarget.Tdisp GateCCalc.F87 G.n G.m)) :
    Bound 1 (7 / 8) 1 (23 / 24) 0 := by
  refine ⟨P, hE, (|K| + 1) * 57, by positivity, 16, le_rfl, ?_, ?_⟩
  · intro G s hn hsp
    have hd : GateCTarget.Tdisp GateCCalc.F87 G.n G.m = GateCCalc.Tchd G.n G.m := by
      unfold GateCTarget.Tdisp
      rw [if_pos (sparse_le_F87 hsp)]
    have h := correctWithin_mono_const (correctWithin_of_exact hE (hR G s)) (tdisp_nonneg _ _)
    refine correctWithin_mono h ?_
    rw [hd]
    have ht := tchd_le hn (sparse_le_real hn hsp)
    have hT : Time 1 (23 / 24) 0 G.n = (G.n : ℝ) * Real.log G.n ^ ((23 : ℝ) / 24) := by
      unfold Time
      norm_num
    rw [hT, mul_assoc]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  · intro G s
    have hn : 1 ≤ G.n := s.pos
    have h := correctWithin_mono_const (correctWithin_of_exact hE (hR G s)) (tdisp_nonneg _ _)
    refine correctWithin_mono h ?_
    have ht := tdisp_le_poly (m := G.m) hn
    have hP : 0 ≤ ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1) := by positivity
    calc (|K| + 1) * GateCTarget.Tdisp GateCCalc.F87 G.n G.m
        ≤ (|K| + 1) * (8 * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ (|K| + 1) * 57 * ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1) := by
          have : 0 ≤ |K| + 1 := by positivity
          nlinarith

/-- **The `7/8` row**: the C-HD witness of the fork, at the `7/8` dispatch threshold, is exact on
every graph, runs within `O(n·(log n)^{23/24})` time on graphs with `16 ≤ n` and at most
`n · ⌊⌊log₂ n⌋^{7/8}⌋` edges, and within the `O(nm)` fallback everywhere. -/
theorem chd_bound87 : Bound 1 (7 / 8) 1 (23 / 24) 0 :=
  bound_of_tdisp Frontier.CHD.Final.chd_exact_within87.1 Frontier.CHD.Final.chd_exact_within87.2

end BigOSpeedrun.DirectedSSSP.Cap87Row

#print axioms BigOSpeedrun.DirectedSSSP.Cap87Row.chd_bound87
