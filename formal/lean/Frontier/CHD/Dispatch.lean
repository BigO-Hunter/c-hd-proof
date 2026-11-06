import Frontier.RAMLogic
import Frontier.GateCCalc
import Frontier.GateC
import Frontier.RAMWitness

/-!
# Frontier.CHD.Dispatch — RAM-level threshold computation for the C-HD dispatcher (owner: agent-10)

NON-GATE.  Layer-B pilot.  A concrete RAM `Stmt` that computes, in word registers,
`pa = Nat.log 2 n` (halving loop) and, when `16 ≤ pa`, `pr = ⌊(pa^3)^(1/4)⌋ = GateCCalc.F n`,
with an exact cost bound.  Register names are prefixed `p` so that they are disjoint from every
other program fragment.
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.Dispatch

open Frontier Frontier.RAM WExpr Stmt

/-! ## Arithmetic facts -/

theorem one_lt_div_pow_of_lt_log {n k : ℕ} (hk : k < Nat.log 2 n) : 1 < n / 2 ^ k := by
  have hn : n ≠ 0 := by intro h; subst h; simp at hk
  have h1 : 2 ^ (k + 1) ≤ n :=
    (Nat.pow_le_pow_right (by norm_num) hk).trans (Nat.pow_log_le_self 2 hn)
  have hp : 0 < 2 ^ k := pow_pos (by norm_num) k
  have h2 : 2 * 2 ^ k ≤ n := by rw [pow_succ] at h1; linarith
  exact (Nat.le_div_iff_mul_le hp).mpr (by linarith)

theorem div_pow_log_lt_two (n : ℕ) : n / 2 ^ Nat.log 2 n < 2 := by
  have hp : 0 < 2 ^ Nat.log 2 n := pow_pos (by norm_num) _
  rw [Nat.div_lt_iff_lt_mul hp]
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  rw [pow_succ] at this
  linarith

/-- `⌊y^(1/4)⌋` as nested integer square roots, and its characterization. -/
def root4 (y : ℕ) : ℕ := Nat.sqrt (Nat.sqrt y)

theorem root4_pow_le (y : ℕ) : root4 y ^ 4 ≤ y := by
  unfold root4
  have h1 := Nat.sqrt_le' (Nat.sqrt y)
  have h2 := Nat.sqrt_le' y
  calc Nat.sqrt (Nat.sqrt y) ^ 4 = (Nat.sqrt (Nat.sqrt y) ^ 2) ^ 2 := by ring
    _ ≤ (Nat.sqrt y) ^ 2 := Nat.pow_le_pow_left h1 2
    _ ≤ y := h2

theorem lt_root4_succ_pow (y : ℕ) : y < (root4 y + 1) ^ 4 := by
  unfold root4
  have h1 := Nat.lt_succ_sqrt' (Nat.sqrt y)
  have h2 := Nat.lt_succ_sqrt' y
  have h3 : Nat.sqrt y + 1 ≤ (Nat.sqrt (Nat.sqrt y) + 1) ^ 2 := h1
  calc y < (Nat.sqrt y + 1) ^ 2 := h2
    _ ≤ ((Nat.sqrt (Nat.sqrt y) + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h3 2
    _ = (Nat.sqrt (Nat.sqrt y) + 1) ^ 4 := by ring

theorem pow4_le_of_le_root4 {k y : ℕ} (hk : k ≤ root4 y) : k ^ 4 ≤ y :=
  (Nat.pow_le_pow_left hk 4).trans (root4_pow_le y)

theorem F_eq_root4 (n : ℕ) : GateCCalc.F n = root4 (Nat.log 2 n * Nat.log 2 n * Nat.log 2 n) := by
  unfold GateCCalc.F root4
  congr 2
  ring

/-- `⌊y^(1/8)⌋` as three nested integer square roots, and its characterization.  This is the
`7/8`-cap analogue of `root4`: `root8 (a^7) = ⌊(log₂ n)^(7/8)⌋` when `a = log₂ n`. -/
def root8 (y : ℕ) : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt y))

theorem root8_pow_le (y : ℕ) : root8 y ^ 8 ≤ y := by
  unfold root8
  have h1 := Nat.sqrt_le' (Nat.sqrt (Nat.sqrt y))
  have h2 := Nat.sqrt_le' (Nat.sqrt y)
  have h3 := Nat.sqrt_le' y
  calc Nat.sqrt (Nat.sqrt (Nat.sqrt y)) ^ 8
      = ((Nat.sqrt (Nat.sqrt (Nat.sqrt y)) ^ 2) ^ 2) ^ 2 := by ring
    _ ≤ ((Nat.sqrt (Nat.sqrt y) ^ 2) ^ 2) := by
        apply Nat.pow_le_pow_left
        apply Nat.pow_le_pow_left
        exact h1
    _ ≤ (Nat.sqrt y) ^ 2 := by
        apply Nat.pow_le_pow_left
        exact h2
    _ ≤ y := h3

theorem lt_root8_succ_pow (y : ℕ) : y < (root8 y + 1) ^ 8 := by
  unfold root8
  have h1 := Nat.lt_succ_sqrt' (Nat.sqrt (Nat.sqrt y))
  have h2 := Nat.lt_succ_sqrt' (Nat.sqrt y)
  have h3 : Nat.sqrt y + 1 ≤ (Nat.sqrt (Nat.sqrt y) + 1) ^ 2 :=
    Nat.lt_succ_sqrt' (Nat.sqrt y)
  have h4 : Nat.sqrt (Nat.sqrt y) + 1 ≤
      (Nat.sqrt (Nat.sqrt (Nat.sqrt y)) + 1) ^ 2 := h1
  calc y < (Nat.sqrt y + 1) ^ 2 := Nat.lt_succ_sqrt' y
    _ ≤ ((Nat.sqrt (Nat.sqrt y) + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h3 2
    _ ≤ (((Nat.sqrt (Nat.sqrt (Nat.sqrt y)) + 1) ^ 2) ^ 2) ^ 2 :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left h4 2) 2
    _ = (Nat.sqrt (Nat.sqrt (Nat.sqrt y)) + 1) ^ 8 := by ring

theorem pow8_le_of_le_root8 {k y : ℕ} (hk : k ≤ root8 y) : k ^ 8 ≤ y :=
  (Nat.pow_le_pow_left hk 8).trans (root8_pow_le y)

/-- `⌊(a⁷)^(1/8)⌋ ≤ a` — the `7/8` threshold never exceeds `log₂ n`. -/
theorem root8_le (a : ℕ) : root8 (a ^ 7) ≤ a := by
  by_contra h
  push_neg at h
  have h1 : (a + 1) ^ 8 ≤ root8 (a ^ 7) ^ 8 := Nat.pow_le_pow_left h 8
  have h2 := root8_pow_le (a ^ 7)
  have h3 : a ^ 7 < (a + 1) ^ 8 := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0; norm_num
    · have ha1 : a ≤ a + 1 := by omega
      have hb : 1 < a + 1 := by omega
      exact lt_of_le_of_lt (Nat.pow_le_pow_left ha1 7)
        (Nat.pow_lt_pow_right hb (by norm_num))
  exact absurd (h1.trans h2) (not_le.mpr h3)

/-- `a ^ k ≤ a ^ 7` for `1 ≤ k ≤ 7` (needed to keep `a^7`'s partial products inside the word). -/
theorem pow_le_seven {a k : ℕ} (h1 : 1 ≤ k) (hk : k ≤ 7) : a ^ k ≤ a ^ 7 := by
  rcases Nat.eq_zero_or_pos a with h | hp
  · subst h
    simp [Nat.zero_pow (by omega : 0 < k)]
  · exact Nat.pow_le_pow_right hp hk

theorem F87_eq_root8 (n : ℕ) : GateCCalc.F87 n = root8 (Nat.log 2 n ^ 7) := rfl

/-! ## The program -/

/-- Halving loop body: `px := px / 2; pa := pa + 1`. -/
def halveBody : Stmt :=
  seq (wset "px" (div (var "px") (lit 2))) (wset "pa" (add (var "pa") (lit 1)))

/-- `pa := Nat.log 2 n` (with `px` as scratch). -/
def logProg : Stmt :=
  seq (wset "px" (var "n")) (seq (wset "pa" (lit 0)) (.while (lt (lit 1) (var "px")) halveBody))

/-- `(pr + 1)^4` as a word expression. -/
def succPow4 : WExpr :=
  mul (mul (add (var "pr") (lit 1)) (add (var "pr") (lit 1)))
    (mul (add (var "pr") (lit 1)) (add (var "pr") (lit 1)))

/-- `pr := ⌊py^(1/4)⌋` by linear search. -/
def rootProg : Stmt :=
  seq (wset "pr" (lit 0))
    (.while (lt succPow4 (add (var "py") (lit 1))) (wset "pr" (add (var "pr") (lit 1))))

/-- `py := pa^3` then `pr := ⌊py^(1/4)⌋`. -/
def thrProg : Stmt :=
  seq (wset "py" (mul (mul (var "pa") (var "pa")) (var "pa"))) rootProg

/-- `(pr + 1)^8 = ((pr + 1)^4)^2` as a word expression (two copies of `succPow4`). -/
def succPow8 : WExpr := mul succPow4 succPow4

/-- `pr := ⌊py^(1/8)⌋` by linear search (the `7/8`-cap root loop). -/
def rootProg8 : Stmt :=
  seq (wset "pr" (lit 0))
    (.while (lt succPow8 (add (var "py") (lit 1))) (wset "pr" (add (var "pr") (lit 1))))

/-- `pa^7 = (pa·pa·pa)·(pa·pa·(pa·pa))` as a word expression. -/
def pa7 : WExpr :=
  mul (mul (mul (var "pa") (var "pa")) (var "pa"))
    (mul (mul (var "pa") (var "pa")) (mul (var "pa") (var "pa")))

/-- `py := pa^7` then `pr := ⌊py^(1/8)⌋ = F87 n`. -/
def thrProg87 : Stmt := seq (wset "py" pa7) rootProg8

/-! ## Correctness of the halving loop -/

variable {V : Type} {ops : VOps V}

/-- Registers other than the listed scratch names are untouched. -/
def Agree (xs : List String) (s t : State V) : Prop :=
  (∀ x, x ∉ xs → t.w x = s.w x) ∧ t.v = s.v ∧ t.wa = s.wa ∧ t.va = s.va ∧ t.wlen = s.wlen ∧
    t.vlen = s.vlen ∧ t.cap = s.cap ∧ t.space = s.space ∧ t.procs = s.procs

theorem Agree.refl (xs : List String) (s : State V) : Agree xs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Agree.trans {xs : List String} {s t u : State V} (h1 : Agree xs s t) (h2 : Agree xs t u) :
    Agree xs s u := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, h1, i1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, h2, i2⟩ := h2
  exact ⟨fun x hx => (a2 x hx).trans (a1 x hx), b2.trans b1, c2.trans c1, d2.trans d1,
    e2.trans e1, f2.trans f1, g2.trans g1, h2.trans h1, i2.trans i1⟩

theorem Agree.setW {xs : List String} {s t : State V} (h : Agree xs s t) {x : String} (hx : x ∈ xs)
    (a : ℕ) : Agree xs s (t.setW x a) := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, h1, i1⟩ := h
  refine ⟨fun y hy => ?_, b1, c1, d1, e1, f1, g1, h1, i1⟩
  have : y ≠ x := fun h => hy (h ▸ hx)
  simp [State.setW, this, a1 y hy]

theorem Agree.charge {xs : List String} {s t : State V} (h : Agree xs s t) (k : ℕ) :
    Agree xs s (t.charge k) := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, h1, i1⟩ := h
  exact ⟨fun y hy => a1 y hy, b1, c1, d1, e1, f1, g1, h1, i1⟩

theorem Agree.mono {xs ys : List String} (hxy : ∀ x, x ∈ xs → x ∈ ys) {s t : State V}
    (h : Agree xs s t) : Agree ys s t := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, h1, i1⟩ := h
  exact ⟨fun y hy => a1 y (fun hx => hy (hxy y hx)), b1, c1, d1, e1, f1, g1, h1, i1⟩

/-- Scratch names of the dispatcher. -/
def scratch : List String := ["px", "pa", "py", "pr", "pq"]

theorem logProg_runs (s : State V) (n : ℕ) (hn : s.w "n" = n) (hcap : n + 2 < s.cap) :
    Runs ops logProg s (fun r => r.w "pa" = Nat.log 2 n ∧ Agree ["px", "pa"] s r ∧
      r.cost = s.cost + 3 + 3 * Nat.log 2 n) := by
  unfold logProg
  refine runs_seq (runs_wset (a := n) (by rw [evalW_var, hn]) ?_)
  set s1 := (s.setW "px" n).charge 1 with hs1
  have hcap1 : s1.cap = s.cap := rfl
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hcap1]; omega)) ?_)
  set s2 := (s1.setW "pa" 0).charge 1 with hs2
  have hA2 : Agree ["px", "pa"] s s2 :=
    (((Agree.refl _ s).setW (by simp) n).charge 1).setW (by simp) 0 |>.charge 1
  refine runs_while (fun k t => t.w "px" = n / 2 ^ k ∧ t.w "pa" = k ∧ Agree ["px", "pa"] s t ∧
      t.cost = s.cost + 2 + 3 * k) (Nat.log 2 n) _ ?_ ?_ s2
    ⟨by simp [hs2, hs1, State.setW, State.charge], by simp [hs2, State.setW, State.charge], hA2,
      by simp [hs2, hs1, State.setW, State.charge]⟩
  · intro k hk t ⟨hx, ha, hA, hc⟩
    have htcap : t.cap = s.cap := hA.2.2.2.2.2.2.1
    have h1 : 1 < n / 2 ^ k := one_lt_div_pow_of_lt_log hk
    have hle : n / 2 ^ k ≤ n := Nat.div_le_self _ _
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := 1) (y := n / 2 ^ k) (evalW_lit_of (by rw [htcap]; omega))
        (by rw [evalW_var, hx]) (by rw [htcap]; omega)]
      simp [h1]
    · unfold halveBody
      have hc1 : (t.charge 1).cap = s.cap := htcap
      refine runs_seq (runs_wset (a := n / 2 ^ k / 2) ?_ ?_)
      · simp only [evalW, State.charge, hx, fit, Option.bind_eq_bind, Option.bind_some,
          htcap]
        have : 2 < s.cap := by omega
        simp [this]
      · set t1 := ((t.charge 1).setW "px" (n / 2 ^ k / 2)).charge 1 with ht1
        have hk1 : k + 1 < s.cap := by
          have : k < Nat.log 2 n := hk
          have hlog : Nat.log 2 n ≤ n := (Nat.log_lt_self 2 (by omega : n ≠ 0)).le
          omega
        refine runs_wset (a := k + 1) (evalW_add_of (x := k) (y := 1)
          (by simp [ht1, State.setW, State.charge, ha])
          (evalW_lit_of (by simp [ht1, State.setW, State.charge, htcap]; omega))
          (by simp [ht1, State.setW, State.charge, htcap]; omega)) ?_
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [ht1, State.setW, State.charge, Nat.div_div_eq_div_mul, pow_succ]
        · simp [State.setW, State.charge]
        · exact (((hA.charge 1).setW (by simp) _).charge 1).setW (by simp) _ |>.charge 1
        · simp [ht1, State.setW, State.charge, hc]; ring
  · intro t ⟨hx, ha, hA, hc⟩
    have htcap : t.cap = s.cap := hA.2.2.2.2.2.2.1
    have h2 : n / 2 ^ Nat.log 2 n < 2 := div_pow_log_lt_two n
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [evalW_lt_of (x := 1) (y := n / 2 ^ Nat.log 2 n) (evalW_lit_of (by rw [htcap]; omega))
        (by rw [evalW_var, hx]) (by rw [htcap]; omega)]
      have : ¬ (1 < n / 2 ^ Nat.log 2 n) := by omega
      simp [this]
    · simp [State.charge, ha]
    · exact hA.charge 1
    · simp [State.charge, hc]; ring


/-! ## Correctness of the fourth-root loop -/

theorem evalW_mul_of {s : State V} {a b : WExpr} {x y : ℕ} (ha : evalW s a = some x)
    (hb : evalW s b = some y) (hc : x * y < s.cap) :
    evalW s (.mul a b) = some (x * y) := by
  simp [evalW, ha, hb, fit, hc]

theorem evalW_sub_of {s : State V} {a b : WExpr} {x y : ℕ} (ha : evalW s a = some x)
    (hb : evalW s b = some y) : evalW s (.sub a b) = some (x - y) := by
  simp [evalW, ha, hb]

theorem evalW_div_of {s : State V} {a b : WExpr} {x y : ℕ} (ha : evalW s a = some x)
    (hb : evalW s b = some y) (hy : y ≠ 0) : evalW s (.div a b) = some (x / y) := by
  simp [evalW, ha, hb, hy]

theorem evalW_succPow4 {s : State V} {k : ℕ} (hk : s.w "pr" = k) (hc : (k + 1) ^ 4 < s.cap) :
    evalW s succPow4 = some ((k + 1) ^ 4) := by
  have h1 : 1 ≤ k + 1 := by omega
  have hpow : (k + 1) ≤ (k + 1) ^ 4 := by
    calc k + 1 = (k + 1) ^ 1 := by ring
      _ ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
  have hsq : (k + 1) * (k + 1) ≤ (k + 1) ^ 4 := by
    calc (k + 1) * (k + 1) = (k + 1) ^ 2 := by ring
      _ ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
  have hlit : evalW s (lit 1) = some 1 := evalW_lit_of (by omega)
  have hadd : evalW s (add (var "pr") (lit 1)) = some (k + 1) :=
    evalW_add_of (by rw [evalW_var, hk]) hlit (by omega)
  have hm : evalW s (mul (add (var "pr") (lit 1)) (add (var "pr") (lit 1))) = some ((k + 1) * (k + 1)) :=
    evalW_mul_of hadd hadd (by omega)
  have := evalW_mul_of hm hm (by
    calc (k + 1) * (k + 1) * ((k + 1) * (k + 1)) = (k + 1) ^ 4 := by ring
      _ < s.cap := hc)
  unfold succPow4
  rw [this]
  congr 1
  ring

theorem evalW_succPow8 {s : State V} {k : ℕ} (hk : s.w "pr" = k) (hc : (k + 1) ^ 8 < s.cap) :
    evalW s succPow8 = some ((k + 1) ^ 8) := by
  have h4 : evalW s succPow4 = some ((k + 1) ^ 4) :=
    evalW_succPow4 hk (by
      have h : (k + 1) ^ 4 ≤ (k + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega)
  unfold succPow8
  rw [evalW_mul_of h4 h4 (by
    calc (k + 1) ^ 4 * (k + 1) ^ 4 = (k + 1) ^ 8 := by ring
      _ < s.cap := hc)]
  congr 1
  ring

theorem rootProg_runs (s : State V) (y : ℕ) (hy : s.w "py" = y) (hcap : 16 * y + 16 < s.cap) :
    Runs ops rootProg s (fun r => r.w "pr" = root4 y ∧ r.w "py" = y ∧ Agree ["pr"] s r ∧
      r.cost = s.cost + 2 + 2 * root4 y) := by
  unfold rootProg
  have hK4 : root4 y ^ 4 ≤ y := root4_pow_le y
  have hK4' : y < (root4 y + 1) ^ 4 := lt_root4_succ_pow y
  have hKb : (root4 y + 1) ^ 4 ≤ 16 * y + 16 := by
    rcases Nat.eq_zero_or_pos (root4 y) with h0 | hpos
    · rw [h0]; omega
    · have : root4 y + 1 ≤ 2 * root4 y := by omega
      calc (root4 y + 1) ^ 4 ≤ (2 * root4 y) ^ 4 := Nat.pow_le_pow_left this 4
        _ = 16 * root4 y ^ 4 := by ring
        _ ≤ 16 * y + 16 := by omega
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by omega)) ?_)
  set s1 := (s.setW "pr" 0).charge 1 with hs1
  have hA1 : Agree ["pr"] s s1 := ((Agree.refl _ s).setW (by simp) 0).charge 1
  refine runs_while (fun k t => t.w "pr" = k ∧ t.w "py" = y ∧ Agree ["pr"] s t ∧
      t.cost = s.cost + 1 + 2 * k) (root4 y) _ ?_ ?_ s1
    ⟨by simp [hs1, State.setW, State.charge], by simp [hs1, State.setW, State.charge, hy], hA1,
      by simp [hs1, State.setW, State.charge]⟩
  · intro k hk t ⟨hr, hyt, hA, hc⟩
    have htcap : t.cap = s.cap := hA.2.2.2.2.2.2.1
    have hk4 : (k + 1) ^ 4 ≤ y := pow4_le_of_le_root4 (by omega)
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := (k + 1) ^ 4) (y := y + 1) (evalW_succPow4 hr (by rw [htcap]; omega))
        (evalW_add_of (by rw [evalW_var, hyt]) (evalW_lit_of (by rw [htcap]; omega))
          (by rw [htcap]; omega)) (by rw [htcap]; omega)]
      have : (k + 1) ^ 4 < y + 1 := by omega
      simp [this]
    · have hk1 : k + 1 < s.cap := by
        have : k + 1 ≤ (k + 1) ^ 4 := by
          calc k + 1 = (k + 1) ^ 1 := by ring
            _ ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
        omega
      refine runs_wset (a := k + 1) (evalW_add_of (by simp [State.charge, hr])
        (evalW_lit_of (by simp [State.charge, htcap]; omega)) (by simp [State.charge, htcap]; omega)) ?_
      refine ⟨by simp [State.setW, State.charge], by simp [State.setW, State.charge, hyt], ?_, ?_⟩
      · exact ((hA.charge 1).setW (by simp) _).charge 1
      · simp [State.setW, State.charge, hc]; ring
  · intro t ⟨hr, hyt, hA, hc⟩
    have htcap : t.cap = s.cap := hA.2.2.2.2.2.2.1
    refine ⟨?_, by simp [State.charge, hr], by simp [State.charge, hyt], hA.charge 1, ?_⟩
    · rw [evalW_lt_of (x := (root4 y + 1) ^ 4) (y := y + 1) (evalW_succPow4 hr (by rw [htcap]; omega))
        (evalW_add_of (by rw [evalW_var, hyt]) (evalW_lit_of (by rw [htcap]; omega))
          (by rw [htcap]; omega)) (by rw [htcap]; omega)]
      have : ¬ ((root4 y + 1) ^ 4 < y + 1) := by omega
      simp [this]
    · simp [State.charge, hc]; ring


/-! ## Correctness of the eighth-root loop -/

theorem rootProg8_runs (s : State V) (y : ℕ) (hy : s.w "py" = y) (hcap : 256 * y + 256 < s.cap) :
    Runs ops rootProg8 s (fun r => r.w "pr" = root8 y ∧ r.w "py" = y ∧ Agree ["pr"] s r ∧
      r.cost = s.cost + 2 + 2 * root8 y) := by
  unfold rootProg8
  have hK8 : root8 y ^ 8 ≤ y := root8_pow_le y
  have hK8' : y < (root8 y + 1) ^ 8 := lt_root8_succ_pow y
  have hKb : (root8 y + 1) ^ 8 ≤ 256 * y + 256 := by
    rcases Nat.eq_zero_or_pos (root8 y) with h0 | hpos
    · rw [h0]; omega
    · have : root8 y + 1 ≤ 2 * root8 y := by omega
      calc (root8 y + 1) ^ 8 ≤ (2 * root8 y) ^ 8 := Nat.pow_le_pow_left this 8
        _ = 256 * root8 y ^ 8 := by ring
        _ ≤ 256 * y + 256 := by omega
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by omega)) ?_)
  set s1 := (s.setW "pr" 0).charge 1 with hs1
  have hA1 : Agree ["pr"] s s1 := ((Agree.refl _ s).setW (by simp) 0).charge 1
  refine runs_while (fun k t => t.w "pr" = k ∧ t.w "py" = y ∧ Agree ["pr"] s t ∧
      t.cost = s.cost + 1 + 2 * k) (root8 y) _ ?_ ?_ s1
    ⟨by simp [hs1, State.setW, State.charge], by simp [hs1, State.setW, State.charge, hy], hA1,
      by simp [hs1, State.setW, State.charge]⟩
  · intro k hk t ⟨hr, hyt, hA, hc⟩
    have htcap : t.cap = s.cap := hA.2.2.2.2.2.2.1
    have hk8 : (k + 1) ^ 8 ≤ y :=
      (Nat.pow_le_pow_left (by omega : k + 1 ≤ root8 y) 8).trans hK8
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := (k + 1) ^ 8) (y := y + 1) (evalW_succPow8 hr (by rw [htcap]; omega))
        (evalW_add_of (by rw [evalW_var, hyt]) (evalW_lit_of (by rw [htcap]; omega))
          (by rw [htcap]; omega)) (by rw [htcap]; omega)]
      have : (k + 1) ^ 8 < y + 1 := by omega
      simp [this]
    · have hk1 : k + 1 < s.cap := by
        have : k + 1 ≤ (k + 1) ^ 8 := by
          calc k + 1 = (k + 1) ^ 1 := by ring
            _ ≤ (k + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
        omega
      refine runs_wset (a := k + 1) (evalW_add_of (by simp [State.charge, hr])
        (evalW_lit_of (by simp [State.charge, htcap]; omega)) (by simp [State.charge, htcap]; omega)) ?_
      refine ⟨by simp [State.setW, State.charge], by simp [State.setW, State.charge, hyt], ?_, ?_⟩
      · exact ((hA.charge 1).setW (by simp) _).charge 1
      · simp [State.setW, State.charge, hc]; ring
  · intro t ⟨hr, hyt, hA, hc⟩
    have htcap : t.cap = s.cap := hA.2.2.2.2.2.2.1
    refine ⟨?_, by simp [State.charge, hr], by simp [State.charge, hyt], hA.charge 1, ?_⟩
    · rw [evalW_lt_of (x := (root8 y + 1) ^ 8) (y := y + 1)
        (evalW_succPow8 hr (by rw [htcap]; omega))
        (evalW_add_of (by rw [evalW_var, hyt]) (evalW_lit_of (by rw [htcap]; omega))
          (by rw [htcap]; omega)) (by rw [htcap]; omega)]
      have : ¬ ((root8 y + 1) ^ 8 < y + 1) := by omega
      simp [this]
    · simp [State.charge, hc]; ring


/-! ## `py := pa^3; pr := ⌊py^(1/4)⌋` -/

theorem thrProg_runs (s : State V) (a : ℕ) (ha : s.w "pa" = a)
    (hcap : 16 * (a * a * a) + 16 < s.cap) :
    Runs ops thrProg s (fun r => r.w "pr" = root4 (a * a * a) ∧ Agree ["py", "pr"] s r ∧
      r.cost = s.cost + 3 + 2 * root4 (a * a * a)) := by
  unfold thrProg
  have hm1 : evalW s (mul (var "pa") (var "pa")) = some (a * a) := by
    refine evalW_mul_of (by rw [evalW_var, ha]) (by rw [evalW_var, ha]) ?_
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; omega
    · have : a * a ≤ a * a * a := Nat.le_mul_of_pos_right _ h
      omega
  have hm2 : evalW s (mul (mul (var "pa") (var "pa")) (var "pa")) = some (a * a * a) :=
    evalW_mul_of hm1 (by rw [evalW_var, ha]) (by omega)
  refine runs_seq (runs_wset (a := a * a * a) hm2 ?_)
  set s1 := (s.setW "py" (a * a * a)).charge 1 with hs1
  have hA1 : Agree ["py", "pr"] s s1 := ((Agree.refl _ s).setW (by simp) _).charge 1
  refine (rootProg_runs s1 (a * a * a) (by simp [hs1, State.setW, State.charge])
    (by simp [hs1, State.setW, State.charge]; omega)).mono ?_
  rintro r ⟨hr, hy, hA, hc⟩
  refine ⟨hr, hA1.trans (hA.mono (by simp)), ?_⟩
  simp [hs1, State.setW, State.charge] at hc; omega


/-! ## `py := pa^7; pr := ⌊py^(1/8)⌋` -/

theorem evalW_pa7 {s : State V} {a : ℕ} (ha : s.w "pa" = a)
    (hcap : 256 * a ^ 7 + 256 < s.cap) : evalW s pa7 = some (a ^ 7) := by
  have hpa : evalW s (var "pa") = some a := by rw [evalW_var, ha]
  have h7 : a ^ 7 < s.cap := by omega
  have hp2 : a * a < s.cap := by
    rw [show a * a = a ^ 2 by ring]
    exact lt_of_le_of_lt (pow_le_seven (by norm_num) (by norm_num)) h7
  have hp3 : a * a * a < s.cap := by
    rw [show a * a * a = a ^ 3 by ring]
    exact lt_of_le_of_lt (pow_le_seven (by norm_num) (by norm_num)) h7
  have hp4 : (a * a) * (a * a) < s.cap := by
    rw [show (a * a) * (a * a) = a ^ 4 by ring]
    exact lt_of_le_of_lt (pow_le_seven (by norm_num) (by norm_num)) h7
  have h2 : evalW s (mul (var "pa") (var "pa")) = some (a * a) := evalW_mul_of hpa hpa hp2
  have h3 : evalW s (mul (mul (var "pa") (var "pa")) (var "pa")) = some (a * a * a) :=
    evalW_mul_of h2 hpa hp3
  have h4 : evalW s (mul (mul (var "pa") (var "pa")) (mul (var "pa") (var "pa"))) =
      some ((a * a) * (a * a)) := evalW_mul_of h2 h2 hp4
  unfold pa7
  rw [evalW_mul_of h3 h4 (by
    rw [show (a * a * a) * ((a * a) * (a * a)) = a ^ 7 by ring]; exact h7)]
  congr 1
  ring

theorem thrProg87_runs (s : State V) (a : ℕ) (ha : s.w "pa" = a)
    (hcap : 256 * a ^ 7 + 256 < s.cap) :
    Runs ops thrProg87 s (fun r => r.w "pr" = root8 (a ^ 7) ∧ Agree ["py", "pr"] s r ∧
      r.cost = s.cost + 3 + 2 * root8 (a ^ 7)) := by
  unfold thrProg87
  have he : evalW s pa7 = some (a ^ 7) := evalW_pa7 ha hcap
  refine runs_seq (runs_wset (a := a ^ 7) he ?_)
  set s1 := (s.setW "py" (a ^ 7)).charge 1 with hs1
  have hA1 : Agree ["py", "pr"] s s1 := ((Agree.refl _ s).setW (by simp) _).charge 1
  refine (rootProg8_runs s1 (a ^ 7) (by simp [hs1, State.setW, State.charge])
    (by simp [hs1, State.setW, State.charge]; omega)).mono ?_
  rintro r ⟨hr, hy, hA, hc⟩
  refine ⟨hr, hA1.trans (hA.mono (by simp)), ?_⟩
  simp [hs1, State.setW, State.charge] at hc; omega


/-! ## The dispatcher and its composition theorem -/

/-- `pq := ⌈m / n⌉` (for `n ≥ 1`). -/
def ceilProg : Stmt := wset "pq" (div (add (var "m") (sub (var "n") (lit 1))) (var "n"))

/-- **A threshold program**: from `pa = log₂ n` it writes `pr = F n` and touches only `py`, `pr`, at
cost `≤ 2 log₂ n + 6` (the shape both the `3/4` dispatcher `thrProg` and the `7/8` dispatcher
`thrProg87` have). -/
def ThrSpec (thr : Stmt) (F : ℕ → ℕ) (capNeed : ℕ → ℕ) : Prop :=
  ∀ (s : State ℝ≥0) (n a : ℕ), a = Nat.log 2 n → s.w "pa" = a → capNeed n < s.cap →
    Runs realOps thr s (fun r => r.w "pr" = F n ∧ Agree ["py", "pr"] s r ∧
      r.cost ≤ s.cost + 2 * a + 6)

/-- Small `n` (`log₂ n < 16`) or dense inputs (`F n < ⌈m/n⌉`) go to `bf`; the rest to `chd`. -/
def dispatchProgOf (thr chd bf : Stmt) : Stmt :=
  seq logProg (ite (lt (var "pa") (lit 16)) bf
    (seq thr (seq ceilProg (ite (lt (var "pr") (var "pq")) bf chd))))

/-- The `3/4` dispatcher: the threshold program is `thrProg` (`pr := ⌊(pa³)^{1/4}⌋ = F n`). -/
def dispatchProg (chd bf : Stmt) : Stmt := dispatchProgOf thrProg chd bf

/-- The initial state for word exponent `e` (it depends on the program only through `e`). -/
noncomputable def init0 (e : ℕ) (ps : List Stmt) (G : Graph) (s : Fin G.n) : State ℝ≥0 :=
  initState ⟨Stmt.skip, e, ps⟩ G s

theorem initState_eq (c : Stmt) (e : ℕ) (ps : List Stmt) (G : Graph) (s : Fin G.n) :
    initState ⟨c, e, ps⟩ G s = init0 e ps G s := rfl

/-- States that agree with the initial state except on the dispatcher's scratch registers
(and the cost counter). -/
def InitLike (e : ℕ) (ps : List Stmt) (G : Graph) (s : Fin G.n) (st : State ℝ≥0) : Prop :=
  Agree scratch (init0 e ps G s) st

/-- Specification of a program body started in an initial-like state. -/
def BodySpec (e : ℕ) (ps : List Stmt) (c : Stmt) (pre : Graph → Prop) (T : ℕ → ℕ → ℝ) : Prop :=
  ∀ (G : Graph) (s : Fin G.n) (st : State ℝ≥0), InitLike e ps G s st → pre G →
    Runs realOps c st (fun r => r.Solves G s ∧ (r.cost : ℝ) ≤ st.cost + T G.n G.m)

theorem Tchd_ge (n m : ℕ) : (n : ℝ) + m ≤ GateCCalc.Tchd n m := by
  unfold GateCCalc.Tchd
  have h1 : 0 ≤ Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) := by
    apply Real.log_nonneg
    have : 0 ≤ (m : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have h2 : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) := by
    have : 0 ≤ (n : ℝ) * Real.log ((n : ℝ) + 2) := by
      have : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
      positivity
    positivity
  have h3 : 0 ≤ (m : ℝ) * Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) := by positivity
  linarith

theorem root4_le (a : ℕ) : root4 (a * a * a) ≤ a := by
  by_contra h
  push Not at h
  have h1 : (a + 1) ^ 4 ≤ root4 (a * a * a) ^ 4 := Nat.pow_le_pow_left h 4
  have h2 := root4_pow_le (a * a * a)
  have h3 : a * a * a < (a + 1) ^ 4 := by nlinarith [Nat.zero_le a]
  omega


theorem ceil_le_iff {m n F : ℕ} (hn : 1 ≤ n) : (m + (n - 1)) / n ≤ F ↔ m ≤ n * F := by
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by omega)]
  constructor
  · intro h
    have : m + (n - 1) < n * F + n := by rw [Nat.succ_mul] at h; linarith
    omega
  · intro h
    rw [Nat.succ_mul]
    have : m + (n - 1) < n * F + n := by omega
    linarith

theorem cap_ge (e : ℕ) (he : 3 ≤ e) (n m : ℕ) : (n + m + 2) ^ 4 ≤ (n + m + 2) ^ (e + 1) :=
  Nat.pow_le_pow_right (by omega) (by omega)

/-- **Dispatcher composition, threshold-parametric.**  If the threshold program computes `F` from
`pa = log₂ n` (`ThrSpec`, given `capNeed n` words of capacity), the C-HD body meets its specification
on the inputs routed to it, and the fallback meets a Bellman-Ford-type bound on all inputs, then the
dispatcher runs within `C * Tdisp F n m` and is exact. -/
theorem dispatch_runs_of (e : ℕ) (he : 3 ≤ e) (ps : List Stmt) (thr chd bf : Stmt)
    (F : ℕ → ℕ) (capNeed : ℕ → ℕ) (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hcapNeed : ∀ n m : ℕ, 16 ≤ n → capNeed n < (n + m + 2) ^ (e + 1))
    (hthr : ThrSpec thr F capNeed)
    (hchd : BodySpec e ps chd (fun G => G.m ≤ G.n * F G.n ∧ 16 ≤ Nat.log 2 G.n)
      (fun n m => C₁ * GateCCalc.Tchd n m))
    (hbf : BodySpec e ps bf (fun _ => True) (fun n m => C₂ * (((n : ℝ) + 1) * ((m : ℝ) + 1))))
    (G : Graph) (s : Fin G.n) :
    Runs realOps (dispatchProgOf thr chd bf) (init0 e ps G s) (fun r => r.Solves G s ∧
      (r.cost : ℝ) ≤ (C₁ + 65536 * C₂ + 100) * GateCTarget.Tdisp F G.n G.m) := by
  have hn1 : 1 ≤ G.n := s.pos
  set st0 := init0 e ps G s with hst0
  have hcap0 : st0.cap = (G.n + G.m + 2) ^ (e + 1) := rfl
  have hcap4 := cap_ge e he G.n G.m
  have hN3 : 3 ≤ G.n + G.m + 2 := by omega
  have hN4 : (G.n + G.m + 2) * 27 ≤ (G.n + G.m + 2) ^ 4 := by
    have : 27 ≤ (G.n + G.m + 2) ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ (G.n + G.m + 2) ^ 3 := Nat.pow_le_pow_left hN3 3
    calc (G.n + G.m + 2) * 27 ≤ (G.n + G.m + 2) * (G.n + G.m + 2) ^ 3 := Nat.mul_le_mul_left _ this
      _ = (G.n + G.m + 2) ^ 4 := by ring
  have hw0 : st0.w "n" = G.n := by simp [hst0, init0, initState]
  have hwm0 : st0.w "m" = G.m := by simp [hst0, init0, initState]
  have hTchd : ((G.n : ℝ) + G.m) ≤ GateCCalc.Tchd G.n G.m := Tchd_ge G.n G.m
  have hn1R : (1 : ℝ) ≤ G.n := by exact_mod_cast hn1
  have hTd1 : 1 ≤ GateCTarget.Tdisp F G.n G.m := by
    unfold GateCTarget.Tdisp
    split_ifs
    · have : (0 : ℝ) ≤ G.m := Nat.cast_nonneg G.m
      linarith
    · have : (0 : ℝ) ≤ G.m := Nat.cast_nonneg G.m
      nlinarith
  unfold dispatchProgOf
  refine runs_seq ((logProg_runs st0 G.n hw0 (by rw [hcap0]; omega)).mono ?_)
  rintro s1 ⟨ha1, hA1, hc1⟩
  set a := Nat.log 2 G.n with ha_def
  have hs1cap : s1.cap = st0.cap := hA1.2.2.2.2.2.2.1
  have hc16 : 16 < s1.cap := by rw [hs1cap, hcap0]; omega
  have htest : evalW s1 (lt (var "pa") (lit 16)) = some (if a < 16 then 1 else 0) :=
    evalW_lt_of (by rw [evalW_var, ha1]) (evalW_lit_of hc16) (by omega)
  have hInit1 : InitLike e ps G s (s1.charge 1) :=
    (hA1.mono (by simp [scratch])).charge 1
  by_cases hsmall : a < 16
  · -- small G.n: fallback
    refine runs_ite_true htest (by simp [hsmall]) ?_
    refine (hbf G s (s1.charge 1) hInit1 trivial).mono ?_
    rintro r ⟨hsol, hcost⟩
    refine ⟨hsol, ?_⟩
    have hnlt : G.n < 65536 := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) G.n
      have h2 : 2 ^ (a + 1) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← ha_def] at this
      have : G.n < 2 ^ 16 := lt_of_lt_of_le this h2
      simpa using this
    have hc1' : ((s1.charge 1).cost : ℝ) ≤ 52 := by
      have : (s1.charge 1).cost = 3 + 3 * a + 1 := by simp [State.charge, hc1, hst0, init0, initState]
      rw [this]; have h15 : a ≤ 15 := by omega
      have h15' : (a : ℝ) ≤ 15 := by exact_mod_cast h15
      push_cast; linarith
    have hbfb : ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1) ≤ 65536 * GateCTarget.Tdisp F G.n G.m := by
      have hnR : (G.n : ℝ) + 1 ≤ 65536 := by exact_mod_cast hnlt
      unfold GateCTarget.Tdisp
      split_ifs
      · have : (0 : ℝ) ≤ G.m := Nat.cast_nonneg G.m
        nlinarith
      · have : (0 : ℝ) ≤ G.m := Nat.cast_nonneg G.m
        nlinarith
    calc (r.cost : ℝ) ≤ ((s1.charge 1).cost : ℝ) + C₂ * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1)) := hcost
      _ ≤ 52 + C₂ * (65536 * GateCTarget.Tdisp F G.n G.m) := by
          gcongr
      _ ≤ (C₁ + 65536 * C₂ + 100) * GateCTarget.Tdisp F G.n G.m := by nlinarith
  · -- large G.n
    refine runs_ite_false (by rw [htest]; simp [hsmall]) ?_
    have ha16 : 16 ≤ a := by omega
    have han : a ≤ G.n := (Nat.log_lt_self 2 (by omega : G.n ≠ 0)).le
    have hn16 : 65536 ≤ G.n := by
      have := Nat.pow_log_le_self 2 (by omega : G.n ≠ 0)
      rw [← ha_def] at this
      have h2 : 2 ^ 16 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha16
      have : 2 ^ 16 ≤ G.n := h2.trans this
      simpa using this
    have hcapT : capNeed G.n < (s1.charge 1).cap := by
      show capNeed G.n < s1.cap
      rw [hs1cap, hcap0]
      exact hcapNeed G.n G.m (by omega)
    refine runs_seq ((hthr (s1.charge 1) G.n a rfl (by simp [State.charge, ha1]) hcapT).mono ?_)
    rintro s2 ⟨hr2, hA2, hc2⟩
    have hA12 : Agree scratch st0 s2 :=
      ((hA1.mono (by simp [scratch])).charge 1).trans (hA2.mono (by simp [scratch]))
    have hs2n : s2.w "n" = G.n := by rw [hA12.1 "n" (by simp [scratch])]; exact hw0
    have hs2m : s2.w "m" = G.m := by rw [hA12.1 "m" (by simp [scratch])]; exact hwm0
    have hs2cap : s2.cap = st0.cap := hA12.2.2.2.2.2.2.1
    -- pq := ⌈G.m/G.n⌉
    set q := (G.m + (G.n - 1)) / G.n with hq_def
    have hqe : evalW s2 (div (add (var "m") (sub (var "n") (lit 1))) (var "n")) = some q := by
      have hl1 : evalW s2 (lit 1) = some 1 := evalW_lit_of (by rw [hs2cap, hcap0]; omega)
      have hsub : evalW s2 (sub (var "n") (lit 1)) = some (G.n - 1) :=
        evalW_sub_of (by rw [evalW_var, hs2n]) hl1
      have hadd : evalW s2 (add (var "m") (sub (var "n") (lit 1))) = some (G.m + (G.n - 1)) :=
        evalW_add_of (by rw [evalW_var, hs2m]) hsub (by rw [hs2cap, hcap0]; omega)
      exact evalW_div_of hadd (by rw [evalW_var, hs2n]) (by omega)
    refine runs_seq (runs_wset (a := q) hqe ?_)
    set s3 := (s2.setW "pq" q).charge 1 with hs3
    have hs3cap : s3.cap = st0.cap := hs2cap
    have hs3r : s3.w "pr" = F G.n := by simp [hs3, State.setW, State.charge, hr2]
    have hs3q : s3.w "pq" = q := by simp [hs3, State.setW, State.charge]
    have hA3 : Agree scratch st0 s3 := (hA12.setW (by simp [scratch]) _).charge 1
    have htest2 : evalW s3 (lt (var "pr") (var "pq")) =
        some (if F G.n < q then 1 else 0) :=
      evalW_lt_of (by rw [evalW_var, hs3r]) (by rw [evalW_var, hs3q])
        (by rw [hs3cap, hcap0]; omega)
    -- the threshold program costs `≤ 2 log₂ n + 6`: total prefix `≤ 5 n + 13`
    have hprefix : ((s3.charge 1).cost : ℝ) ≤ 13 + 5 * (G.n : ℝ) := by
      have hexp : (s3.charge 1).cost = s2.cost + 1 + 1 := by simp [hs3, State.setW, State.charge]
      have hlog1 : (s1.charge 1).cost = 3 + 3 * a + 1 := by
        simp [State.charge, hc1, hst0, init0, initState]
      have hnat : (s3.charge 1).cost ≤ 5 * G.n + 13 := by omega
      have hcast : ((s3.charge 1).cost : ℝ) ≤ ((5 * G.n + 13 : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at hcast
      linarith
    by_cases hdense : F G.n < q
    · -- dense: fallback
      refine runs_ite_true htest2 (by simp [hdense]) ?_
      have hInit3 : InitLike e ps G s (s3.charge 1) := hA3.charge 1
      refine (hbf G s (s3.charge 1) hInit3 trivial).mono ?_
      rintro r ⟨hsol, hcost⟩
      refine ⟨hsol, ?_⟩
      have hnd : ¬ (G.m ≤ G.n * F G.n) := by
        intro hle
        have h1 : q ≤ F G.n := by rw [hq_def]; exact (ceil_le_iff hn1).mpr hle
        omega
      have hT : GateCTarget.Tdisp F G.n G.m = ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1) := by
        unfold GateCTarget.Tdisp; simp [hnd]
      rw [hT]
      have hm0 : (0 : ℝ) ≤ G.m := Nat.cast_nonneg G.m
      calc (r.cost : ℝ) ≤ ((s3.charge 1).cost : ℝ) + C₂ * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1)) := hcost
        _ ≤ (13 + 5 * (G.n : ℝ)) + C₂ * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1)) := by gcongr
        _ ≤ (C₁ + 65536 * C₂ + 100) * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1)) := by nlinarith
    · -- C-HD branch
      refine runs_ite_false (by rw [htest2]; simp [hdense]) ?_
      have hInit3 : InitLike e ps G s (s3.charge 1) := hA3.charge 1
      have hsp : G.m ≤ G.n * F G.n := by
        have hqle : q ≤ F G.n := by omega
        rw [hq_def] at hqle
        exact (ceil_le_iff hn1).mp hqle
      refine (hchd G s (s3.charge 1) hInit3 ⟨hsp, by simpa using ha16⟩).mono ?_
      rintro r ⟨hsol, hcost⟩
      refine ⟨hsol, ?_⟩
      have hT : GateCTarget.Tdisp F G.n G.m = GateCCalc.Tchd G.n G.m := by
        unfold GateCTarget.Tdisp; simp [hsp]
      rw [hT]
      have hm0 : (0 : ℝ) ≤ G.m := Nat.cast_nonneg G.m
      calc (r.cost : ℝ) ≤ ((s3.charge 1).cost : ℝ) + C₁ * GateCCalc.Tchd G.n G.m := hcost
        _ ≤ (13 + 5 * (G.n : ℝ)) + C₁ * GateCCalc.Tchd G.n G.m := by gcongr
        _ ≤ (C₁ + 65536 * C₂ + 100) * GateCCalc.Tchd G.n G.m := by nlinarith


/-- **`thrProg` computes the `3/4` threshold** (`pr := ⌊(pa³)^{1/4}⌋ = F n`) within `2 log₂ n + 6`. -/
theorem thrProg_thrSpec :
    ThrSpec thrProg GateCCalc.F (fun n => 16 * (Nat.log 2 n * Nat.log 2 n * Nat.log 2 n) + 16) := by
  intro s n a ha hpa hcap
  have hcap' : 16 * (a * a * a) + 16 < s.cap := by rw [ha]; exact hcap
  have h := thrProg_runs (V := ℝ≥0) (ops := realOps) s a hpa hcap'
  refine h.mono ?_
  rintro r ⟨hr, hA, hc⟩
  have hF : GateCCalc.F n = root4 (a * a * a) := by rw [F_eq_root4, ha]
  have h4 : root4 (a * a * a) ≤ a := root4_le a
  exact ⟨by rw [hr, hF], hA, by rw [hc]; omega⟩

/-- The capacity the `3/4` threshold program needs, below the word capacity at `e ≥ 3`. -/
theorem capNeed_thrProg_lt (e : ℕ) (he : 3 ≤ e) (n m : ℕ) (hn : 16 ≤ n) :
    16 * (Nat.log 2 n * Nat.log 2 n * Nat.log 2 n) + 16 < (n + m + 2) ^ (e + 1) := by
  set N := n + m + 2 with hN
  have hN18 : 18 ≤ N := by omega
  have hlog : Nat.log 2 n ≤ N := by
    have h1 : Nat.log 2 n ≤ n := (Nat.log_lt_self 2 (by omega : n ≠ 0)).le
    omega
  have h3 : Nat.log 2 n * Nat.log 2 n * Nat.log 2 n ≤ N ^ 3 := by
    have h4 : Nat.log 2 n ^ 3 ≤ N ^ 3 := Nat.pow_le_pow_left hlog 3
    rwa [show Nat.log 2 n * Nat.log 2 n * Nat.log 2 n = Nat.log 2 n ^ 3 by ring]
  have h4 : 16 * N ^ 3 + 16 < N ^ 4 := by
    have h17 : 17 ≤ N := by omega
    have hpos : 16 ≤ N ^ 3 := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 17 ^ 3 := by norm_num
        _ ≤ N ^ 3 := Nat.pow_le_pow_left h17 3
    have h16 : 16 < N ^ 3 := lt_of_lt_of_le (by norm_num : (16 : ℕ) < 18 ^ 3)
      (Nat.pow_le_pow_left hN18 3)
    calc 16 * N ^ 3 + 16 < 17 * N ^ 3 := by nlinarith
      _ ≤ N * N ^ 3 := Nat.mul_le_mul_right (N ^ 3) h17
      _ = N ^ 4 := by ring
  have h5 : N ^ 4 ≤ N ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  calc 16 * (Nat.log 2 n * Nat.log 2 n * Nat.log 2 n) + 16 ≤ 16 * N ^ 3 + 16 := by nlinarith
    _ < N ^ 4 := h4
    _ ≤ N ^ (e + 1) := h5

/-- **Dispatcher composition.**  If the C-HD body meets its specification on the inputs routed to it
and the fallback meets a Bellman-Ford-type bound on all inputs, the dispatcher runs within
`C * Tdisp F n m` and is exact. -/
theorem dispatch_runs (e : ℕ) (he : 3 ≤ e) (ps : List Stmt) (chd bf : Stmt) (C₁ C₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hchd : BodySpec e ps chd (fun G => G.m ≤ G.n * GateCCalc.F G.n ∧ 16 ≤ Nat.log 2 G.n)
      (fun n m => C₁ * GateCCalc.Tchd n m))
    (hbf : BodySpec e ps bf (fun _ => True) (fun n m => C₂ * (((n : ℝ) + 1) * ((m : ℝ) + 1))))
    (G : Graph) (s : Fin G.n) :
    Runs realOps (dispatchProg chd bf) (init0 e ps G s) (fun r => r.Solves G s ∧
      (r.cost : ℝ) ≤ (C₁ + 65536 * C₂ + 100) * GateCTarget.Tdisp GateCCalc.F G.n G.m) :=
  dispatch_runs_of e he ps thrProg chd bf GateCCalc.F
    (fun n => 16 * (Nat.log 2 n * Nat.log 2 n * Nat.log 2 n) + 16) C₁ C₂ hC₁ hC₂
    (fun n m hn => capNeed_thrProg_lt e he n m hn) thrProg_thrSpec hchd hbf G s

/-! ## The `7/8` dispatcher (`F87`) -/

/-- **`thrProg87` computes the `7/8` threshold** (`pr := ⌊(pa⁷)^{1/8}⌋ = F87 n`) within
`2 log₂ n + 6`. -/
theorem thrProg87_thrSpec :
    ThrSpec thrProg87 GateCCalc.F87 (fun n => 256 * Nat.log 2 n ^ 7 + 256) := by
  intro s n a ha hpa hcap
  have hcap' : 256 * a ^ 7 + 256 < s.cap := by rw [ha]; exact hcap
  have h := thrProg87_runs (V := ℝ≥0) (ops := realOps) s a hpa hcap'
  refine h.mono ?_
  rintro r ⟨hr, hA, hc⟩
  have hF : GateCCalc.F87 n = root8 (a ^ 7) := by rw [F87_eq_root8, ha]
  have h8 : root8 (a ^ 7) ≤ a := root8_le a
  exact ⟨by rw [hr, hF], hA, by rw [hc]; omega⟩

/-- The capacity the `7/8` threshold program needs, below the word capacity at `e ≥ 160`
(the word exponent of the C-HD witness, `Final.chdProgram`). -/
theorem capNeed_thrProg87_lt (e : ℕ) (he : 160 ≤ e) (n m : ℕ) (hn : 16 ≤ n) :
    256 * Nat.log 2 n ^ 7 + 256 < (n + m + 2) ^ (e + 1) := by
  set N := n + m + 2 with hN
  have hN2 : 2 ≤ N := by omega
  have hlog : Nat.log 2 n ≤ N := by
    have h1 : Nat.log 2 n ≤ n := (Nat.log_lt_self 2 (by omega : n ≠ 0)).le
    omega
  have hp : Nat.log 2 n ^ 7 ≤ N ^ 7 := Nat.pow_le_pow_left hlog 7
  have hN7 : 1 ≤ N ^ 7 := Nat.one_le_pow 7 N (by omega)
  have h1 : 256 * Nat.log 2 n ^ 7 + 256 ≤ 512 * N ^ 7 := by nlinarith
  have h2 : 512 < N ^ 153 := by
    have hpow : (2 : ℕ) ^ 153 ≤ N ^ 153 := Nat.pow_le_pow_left hN2 153
    have hlt : (2 : ℕ) ^ 9 < 2 ^ 153 :=
      Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by norm_num : 9 < 153)
    have h9 : (512 : ℕ) = 2 ^ 9 := by norm_num
    omega
  have h3 : 512 * N ^ 7 < N ^ 153 * N ^ 7 :=
    Nat.mul_lt_mul_of_pos_right h2 (pow_pos (by omega : 0 < N) 7)
  have h4 : N ^ 153 * N ^ 7 = N ^ 160 := by rw [← pow_add]
  have hNpos : 0 < N := by omega
  have hexp : 160 ≤ e + 1 := by omega
  have h5 : N ^ 160 ≤ N ^ (e + 1) := Nat.pow_le_pow_right hNpos hexp
  omega

/-- **Dispatcher composition at the `7/8` cap.**  Same shape as `dispatch_runs`, with `F87` as the
dispatch threshold and the `7/8` threshold program `thrProg87`. -/
theorem dispatch_runs87 (e : ℕ) (he : 160 ≤ e) (ps : List Stmt) (chd bf : Stmt) (C₁ C₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hchd : BodySpec e ps chd (fun G => G.m ≤ G.n * GateCCalc.F87 G.n ∧ 16 ≤ Nat.log 2 G.n)
      (fun n m => C₁ * GateCCalc.Tchd n m))
    (hbf : BodySpec e ps bf (fun _ => True) (fun n m => C₂ * (((n : ℝ) + 1) * ((m : ℝ) + 1))))
    (G : Graph) (s : Fin G.n) :
    Runs realOps (dispatchProgOf thrProg87 chd bf) (init0 e ps G s) (fun r => r.Solves G s ∧
      (r.cost : ℝ) ≤ (C₁ + 65536 * C₂ + 100) * GateCTarget.Tdisp GateCCalc.F87 G.n G.m) :=
  dispatch_runs_of e (by omega) ps thrProg87 chd bf GateCCalc.F87
    (fun n => 256 * Nat.log 2 n ^ 7 + 256) C₁ C₂ hC₁ hC₂
    (fun n m hn => capNeed_thrProg87_lt e he n m hn) thrProg87_thrSpec hchd hbf G s


/-! ## The Bellman–Ford fallback meets its body specification -/

theorem bf_bodySpec (e : ℕ) (ps : List Stmt) :
    BodySpec e ps BF.prog (fun _ => True) (fun n m => 9 * (((n : ℝ) + 1) * ((m : ℝ) + 1))) := by
  intro G s st hInit _
  have hA := hInit
  have h0 : BF.InputFrame G s st := by
    obtain ⟨hw, hv, hwa, hva, hwlen, hvlen, hcap, hsp, hpr⟩ := hA
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hw "n" (by simp [scratch])]; simp [init0, initState]
    · rw [hw "m" (by simp [scratch])]; simp [init0, initState]
    · rw [hw "s" (by simp [scratch])]; simp [init0, initState]
    · rw [hcap]; simp only [init0, initState]
      calc G.n + G.m + 2 = (G.n + G.m + 2) ^ 1 := (pow_one _).symm
        _ ≤ (G.n + G.m + 2) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    · intro j h; rw [hwa]; simp [init0, initState, h]
    · intro j h; rw [hwa]; simp [init0, initState, h]
    · intro j h; rw [hva]; simp [init0, initState, h]
    · rw [hwlen]; simp [init0, initState]
    · rw [hwlen]; simp [init0, initState]
    · rw [hvlen]; simp [init0, initState]
  refine (BF.prog_runs_gen s st h0).mono ?_
  rintro r ⟨hF, hl, hc⟩
  refine ⟨⟨hF.hreachL, hF.hdistL, fun v => ?_⟩, ?_⟩
  · calc r.label v = BF.lab G r v := rfl
      _ = BF.rounds G s G.n v := congrFun hl v
      _ = G.dist s v := BF.rounds_n_eq_dist s v
  · have hc' : (r.cost : ℝ) ≤ st.cost + 2 * G.n + 4 + (9 * G.m + 4) * G.n + 1 := by
      exact_mod_cast hc
    have hn0 : (0 : ℝ) ≤ G.n := Nat.cast_nonneg _
    have hm0 : (0 : ℝ) ≤ G.m := Nat.cast_nonneg _
    nlinarith

/-- **The dispatcher reduces the frozen Gate-C target to a specification of the C-HD body.**
Any RAM body `chd` (with procedure table `ps`, word exponent `e ≥ 3`) that, from every initial-like
state of a graph with `m ≤ n·F n` and `log₂ n ≥ 16`, terminates with the exact labeled output
within `C₁ · Tchd n m`, yields `CHDTarget F`. -/
theorem chdTarget_of_body (e : ℕ) (he : 3 ≤ e) (ps : List Stmt) (chd : Stmt) (C₁ : ℝ)
    (hC₁ : 0 ≤ C₁)
    (hchd : BodySpec e ps chd (fun G => G.m ≤ G.n * GateCCalc.F G.n ∧ 16 ≤ Nat.log 2 G.n)
      (fun n m => C₁ * GateCCalc.Tchd n m)) :
    GateCTarget.CHDTarget GateCCalc.F := by
  have hruns := dispatch_runs e he ps chd BF.prog C₁ 9 hC₁ (by norm_num) hchd (bf_bodySpec e ps)
  refine ⟨⟨dispatchProg chd BF.prog, e, ps⟩, ?_, C₁ + 65536 * 9 + 100, ?_⟩
  · intro G s
    obtain ⟨f, r, hr, hsol, -⟩ := hruns G s
    exact ⟨f, r, hr, hsol⟩
  · intro G s
    obtain ⟨f, r, hr, -, hc⟩ := hruns G s
    exact ⟨f, r, hr, hc⟩

/-- **The dispatcher reduces the Gate-C target `CHDTarget F` to a specification of the C-HD body**,
for an arbitrary threshold program `thr` computing `F` (this is the shape every cap row uses). -/
theorem chdTarget_of_bodyOf (e : ℕ) (he : 3 ≤ e) (ps : List Stmt) (chd : Stmt) (thr : Stmt)
    (F capNeed : ℕ → ℕ) (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hcapNeed : ∀ n m : ℕ, 16 ≤ n → capNeed n < (n + m + 2) ^ (e + 1))
    (hthr : ThrSpec thr F capNeed)
    (hchd : BodySpec e ps chd (fun G => G.m ≤ G.n * F G.n ∧ 16 ≤ Nat.log 2 G.n)
      (fun n m => C₁ * GateCCalc.Tchd n m)) :
    GateCTarget.CHDTarget F := by
  have hruns := dispatch_runs_of e he ps thr chd BF.prog F capNeed C₁ 9 hC₁ (by norm_num)
    hcapNeed hthr hchd (bf_bodySpec e ps)
  refine ⟨⟨dispatchProgOf thr chd BF.prog, e, ps⟩, ?_, C₁ + 65536 * 9 + 100, ?_⟩
  · intro G s
    obtain ⟨f, r, hr, hsol, -⟩ := hruns G s
    exact ⟨f, r, hr, hsol⟩
  · intro G s
    obtain ⟨f, r, hr, -, hc⟩ := hruns G s
    exact ⟨f, r, hr, hc⟩

/-- **The dispatcher reduces the `7/8` Gate-C target to a specification of the C-HD body.** -/
theorem chdTarget_of_body87 (e : ℕ) (he : 160 ≤ e) (ps : List Stmt) (chd : Stmt) (C₁ : ℝ)
    (hC₁ : 0 ≤ C₁)
    (hchd : BodySpec e ps chd (fun G => G.m ≤ G.n * GateCCalc.F87 G.n ∧ 16 ≤ Nat.log 2 G.n)
      (fun n m => C₁ * GateCCalc.Tchd n m)) :
    GateCTarget.CHDTarget GateCCalc.F87 := by
  have hruns := dispatch_runs87 e he ps chd BF.prog C₁ 9 hC₁ (by norm_num) hchd (bf_bodySpec e ps)
  refine ⟨⟨dispatchProgOf thrProg87 chd BF.prog, e, ps⟩, ?_, C₁ + 65536 * 9 + 100, ?_⟩
  · intro G s
    obtain ⟨f, r, hr, hsol, -⟩ := hruns G s
    exact ⟨f, r, hr, hsol⟩
  · intro G s
    obtain ⟨f, r, hr, -, hc⟩ := hruns G s
    exact ⟨f, r, hr, hc⟩

end Frontier.CHD.Dispatch

#print axioms Frontier.CHD.Dispatch.dispatch_runs
#print axioms Frontier.CHD.Dispatch.chdTarget_of_body
