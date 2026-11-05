import Frontier.CHD.MasterCost

/-!
# Frontier.CHD.Cap87 — the `7/8` cap (`F87 n = ⌊(log₂ n)^(7/8)⌋`) meets the master cost interface

The master cost theorem (`BM.master_cost_D`) asks a cap for exactly two arithmetic facts, neither of
which mentions the cap itself:

* `dd n m ≤ lgN n + 1` on the window `m ≤ n · F n`;
* `lgN n ≤ 256 · t¹²` on the same window (the plan's `2^{1/(1-α)} t^{3/(2(1-α))}` at `α = 7/8`).

This file proves both for `GateCCalc.F87` and instantiates the master cost theorem at `F87` — the
same `cMaster`, hence the same total-cost constant as the `3/4` cap.  Nothing above this file needs
to change for a new cap: a new row only needs its own `F`, its root power (`F^8 ≤ (log₂ n)^7`), and a
dispatcher program that computes it.
-/

namespace Frontier.CHD.Cap87

open Frontier Frontier.CostSkeleton

/-- **The root power of the `7/8` cap**: `⌊(log₂ n)^{7/8}⌋⁸ ≤ (log₂ n)⁷`. -/
theorem F87_pow_eight_le (n : ℕ) : GateCCalc.F87 n ^ 8 ≤ Nat.log 2 n ^ 7 := by
  unfold GateCCalc.F87
  set b := Nat.log 2 n ^ 7 with hb
  have h1 : Nat.sqrt b * Nat.sqrt b ≤ b := Nat.sqrt_le b
  have h2 : Nat.sqrt (Nat.sqrt b) * Nat.sqrt (Nat.sqrt b) ≤ Nat.sqrt b := Nat.sqrt_le _
  have h3 : Nat.sqrt (Nat.sqrt (Nat.sqrt b)) * Nat.sqrt (Nat.sqrt (Nat.sqrt b)) ≤
      Nat.sqrt (Nat.sqrt b) := Nat.sqrt_le _
  have e1 : Nat.sqrt (Nat.sqrt (Nat.sqrt b)) ^ 2 ≤ Nat.sqrt (Nat.sqrt b) := by
    rw [pow_two]; exact h3
  have e2 : Nat.sqrt (Nat.sqrt b) ^ 2 ≤ Nat.sqrt b := by rw [pow_two]; exact h2
  have e3 : Nat.sqrt b ^ 2 ≤ b := by rw [pow_two]; exact h1
  calc Nat.sqrt (Nat.sqrt (Nat.sqrt b)) ^ 8
      = ((Nat.sqrt (Nat.sqrt (Nat.sqrt b)) ^ 2) ^ 2) ^ 2 := by ring
    _ ≤ ((Nat.sqrt (Nat.sqrt b) ^ 2) ^ 2) := by
        apply Nat.pow_le_pow_left
        apply Nat.pow_le_pow_left
        exact e1
    _ ≤ (Nat.sqrt b) ^ 2 := by
        apply Nat.pow_le_pow_left
        exact e2
    _ ≤ b := e3

/-- The cap condition: `⌊lg^{7/8}⌋ ≤ lg`. -/
theorem F87_le_lgN (n : ℕ) : GateCCalc.F87 n ≤ lgN n := by
  have h8 := F87_pow_eight_le n
  have hle : Nat.log 2 n ≤ lgN n := le_max_right _ _
  have hl1 : 1 ≤ lgN n := one_le_lgN n
  have h : GateCCalc.F87 n ^ 8 ≤ lgN n ^ 8 := by
    calc GateCCalc.F87 n ^ 8 ≤ Nat.log 2 n ^ 7 := h8
      _ ≤ lgN n ^ 7 := Nat.pow_le_pow_left hle 7
      _ ≤ lgN n ^ 8 := Nat.pow_le_pow_right hl1 (by norm_num)
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h

/-- The density interface at the `7/8` cap. -/
theorem dd_le_lgN_add_one_F87 (n m : ℕ) (hn : 1 ≤ n) (hw : m ≤ n * GateCCalc.F87 n) :
    dd n m ≤ lgN n + 1 :=
  dd_le_lgN_add_one_of _ n m (F87_le_lgN n) hn hw

/-- **The cap strength at the `7/8` cap**: `lgN ≤ 256 t¹²` on the window. -/
theorem mc_lgN_le_F87 (n m : ℕ) (hdd : dd n m ≤ GateCCalc.F87 n + 1) :
    lgN n ≤ 256 * tF n m ^ 12 :=
  lgN_le_tF_pow12 GateCCalc.F87 n m hdd (F87_pow_eight_le n)

/-- The insertion charge at the `7/8` cap (same constant `3826`). -/
theorem mc_ins_le_F87 (n m δ : ℕ) (hδ : δ ≤ 5 * dd n m) (hdd : dd n m ≤ GateCCalc.F87 n + 1) :
    211 * Nat.log 2 (8 * BM.chdRho (tF n m) δ (LF n m) + 8) + 441 ≤ 3826 * tF n m :=
  BM.mc_ins_le_pow GateCCalc.F87 n m δ 256 (by norm_num) hδ hdd (F87_le_lgN n) (mc_lgN_le_F87 n m hdd)

end Frontier.CHD.Cap87

/-! ## The master cost theorem at the `7/8` cap -/

namespace Frontier.CHD.BM

open Frontier.CostSkeleton

variable {G : Graph} {s : Fin G.n} {out : Fin G.n → List (Fin G.m)} {hins hext : ℕ}

/-- **The master cost theorem for the `7/8` window** `m ≤ n · F87 n`: the concrete DLazy run costs at
most `5100 · cMaster · 56 · Tchd n m`, with the SAME constants as the `3/4` cap. -/
theorem master_cost_D_F87 (hout : ∀ u e, e ∈ out u ↔ G.src e = u)
    (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup) {n m δ : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 1)
    (hGn : G.n ≤ 2 * n) (hGm : G.m ≤ 2 * m) (hm0 : 0 < G.m)
    (hdeg : ∀ u, (Eout G {u}).card ≤ δ) (hδ : δ ≤ 5 * dd n m)
    (hwin : m ≤ n * Frontier.GateCCalc.F87 n) {a : ℕ}
    (ha : fpA (kF n m) hins hext ≤ a * (kF n m + 1))
    {DCb : DCost} {cb : ℕ}
    (hbins : DCb.bins ≤ cb * (Nat.log 2 (tF n m + 1) + Nat.log 2 (dd n m + 1) + 1 + 1))
    (hbext : DCb.bext ≤ cb * (Nat.log 2 (tF n m + 1) + Nat.log 2 (dd n m + 1) + 1 + 1))
    {T : ℕ → ℕ} {Blow : WLab G s} (hlow : Blow ≤ initLabels s s) {φ φ' : Finset (Fin G.m)}
    (hI : DelInv G s φ) {res : ResultD G s} {gE : DGl G s} {lg : Log G s (FPData G s)}
    (hrel : BMSSPD G s (dlOps G s) (fpC G s out (kF n m) hins hext) DCb T (chdM (tF n m)) (chdTau (tF n m))
      (LF n m) Blow ⊤ {s} (initLabels s) φ DGl.init res φ' gE lg) :
    (lg.cost : ℝ) ≤ 5100 * (cMaster a cb : ℕ) * ((56 : ℕ) : ℝ) * Frontier.GateCCalc.Tchd n m := by
  have hdd : dd n m ≤ lgN n + 1 := Cap87.dd_le_lgN_add_one_F87 n m hn hwin
  have hphys : lgN n ≤ 256 * tF n m ^ 12 :=
    Cap87.mc_lgN_le_F87 n m (dd_le_of_window _ n m hn hwin)
  exact master_cost_D hout hsort hsimp hn hm hnm hGn hGm hm0 hdeg hδ hdd hphys ha hbins hbext
    hlow hI hrel

end Frontier.CHD.BM

#print axioms Frontier.CHD.Cap87.F87_pow_eight_le
#print axioms Frontier.CHD.Cap87.mc_lgN_le_F87
#print axioms Frontier.CHD.BM.master_cost_D_F87
