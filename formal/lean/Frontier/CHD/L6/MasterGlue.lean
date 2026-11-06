import Frontier.CHD.L6.CoreSpecProof
import Frontier.CHD.L6.MasterSpecProof

/-!
# `MasterSpec` and the C-HD target from the spine alone (agent-10)

agent-06's `masterSpec_of_goodP` (L6.MasterSpecProof) is `MasterSpec` under `1 ≤ H.m`, which
`MasterIn.mpos` supplies (`coreTop` answers `gM = 0` itself).  Hence, for every admissible cost
parameter choice `P` (`GoodP`), `SpineSpec` is the only remaining hypothesis of `CHDTarget F`.
NON-GATE (glue).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM

theorem kmaster_nonneg (ch ce cb : ℕ) : 0 ≤ kmaster ch ce cb := by
  unfold kmaster; positivity

/-- **`MasterSpec` for every admissible `P`** (agent-06's theorem with `MasterIn.mpos`). -/
theorem masterSpec_of_good {P : ℕ → ℕ → CostPar} {ch ce cb : ℕ} (hP : GoodP P ch ce cb) :
    MasterSpec P (kmaster ch ce cb) :=
  fun H src cn cm hM => masterSpec_of_goodP hP H src cn cm hM hM.mpos

/-- **The C-HD target from the RAM spine alone, threshold-parametric**: for any admissible cost
parameters `P` (`GoodP`), `SpineSpec e ps spine P Ks Kb Kpol` with a word exponent `e ≥ 160` large
enough for the constants and a threshold program `thr` computing `F` gives `CHDTarget F`. -/
theorem chdTarget_of_spine_good_of (F capNeed : ℕ → ℕ) (thr : Stmt)
    (hFl : ∀ n, F n ≤ CostSkeleton.lgN n) (hcap8 : ∀ n, F n ^ 8 ≤ Nat.log 2 n ^ 7)
    (e : ℕ) (he : 160 ≤ e) (ps : List Stmt) (spine : Stmt)
    {P : ℕ → ℕ → CostPar} {ch ce cb : ℕ} (hP : GoodP P ch ce cb) (Ks Kb Kpol : ℝ) (Dp : ℕ)
    (hDp : 2 ≤ Dp) (hKs : 0 ≤ Ks)
    (hbig : 12 + Ks * (kmaster ch ce cb + 1) + |Kb| + |Kpol| ≤ (4 : ℝ) ^ (e + 1 - Dp))
    (hcapNeed : ∀ n m : ℕ, 16 ≤ n → capNeed n < (n + m + 2) ^ (e + 1))
    (hthr : Dispatch.ThrSpec thr F capNeed)
    (hsp : SpineSpec e ps spine P Ks Kb Kpol (kmaster ch ce cb) Dp) :
    GateCTarget.CHDTarget F :=
  chdTarget_of_spine_of F capNeed thr hFl hcap8 e he ps spine P Ks Kb Kpol (kmaster ch ce cb) Dp
    hDp hKs (kmaster_nonneg ch ce cb) hbig hcapNeed hthr hsp (masterSpec_of_good hP)

theorem chdTarget_of_spine_good (e : ℕ) (he : 32 ≤ e) (ps : List Stmt) (spine : Stmt)
    {P : ℕ → ℕ → CostPar} {ch ce cb : ℕ} (hP : GoodP P ch ce cb) (Ks Kb Kpol : ℝ) (Dp : ℕ)
    (hDp : 2 ≤ Dp) (hKs : 0 ≤ Ks)
    (hbig : 12 + Ks * (kmaster ch ce cb + 1) + |Kb| + |Kpol| ≤ (4 : ℝ) ^ (e + 1 - Dp))
    (hsp : SpineSpec e ps spine P Ks Kb Kpol (kmaster ch ce cb) Dp) :
    GateCTarget.CHDTarget GateCCalc.F :=
  chdTarget_of_spine e he ps spine P Ks Kb Kpol (kmaster ch ce cb) Dp hDp hKs
    (kmaster_nonneg ch ce cb) hbig
    hsp (masterSpec_of_good hP)

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.masterSpec_of_good
#print axioms Frontier.CHD.L6.chdTarget_of_spine_good_of
#print axioms Frontier.CHD.L6.chdTarget_of_spine_good
