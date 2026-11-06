import Frontier.CHD.L6.Body
import Frontier.AuditBridge

/-!
# The named witness program of the C-HD route (agent-10; reviewer #1's checklist item 1)

`chdProg e ps core := ⟨dispatchProg (chdBody core) BF.prog, e, ps⟩` is the RAM program behind
`chdTarget_of_core`.  `chdProg_exact_within`: from `CoreSpec e ps core Kc` this NAMED program is
exact on every graph and runs within `(bodyC Kc + 65536·9 + 100) · Tdisp F n m`; `chdTarget_of_named`
repackages it as `CHDTarget F`.  NON-GATE (glue).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM WExpr Stmt

/-- **The C-HD witness program** for a core `core`, word exponent `e`, procedure table `ps`. -/
def chdProg (e : ℕ) (ps : List Stmt) (core : Stmt) : Program :=
  ⟨Dispatch.dispatchProg (chdBody core) Frontier.RAM.BF.prog, e, ps⟩

/-- **The C-HD witness program for a given dispatch threshold program `thr`** (the `7/8` dispatcher
`thrProg87` is the instance that matters for the wider cap rows). -/
def chdProgOf (thr : Stmt) (e : ℕ) (ps : List Stmt) (core : Stmt) : Program :=
  ⟨Dispatch.dispatchProgOf thr (chdBody core) Frontier.RAM.BF.prog, e, ps⟩

/-- **`chdProgOf` is exact and runs within a constant times `Tdisp F n m`**, for any threshold
program `thr` computing `F` (`ThrSpec`) with the cap facts `F ≤ lgN` and `F⁸ ≤ (log₂ n)⁷`. -/
theorem chdProg_exact_within_of (thr : Stmt) (F capNeed : ℕ → ℕ) (e : ℕ) (he : 160 ≤ e)
    (ps : List Stmt) (core : Stmt) (Kc : ℝ) (hKc : 0 ≤ Kc)
    (hFl : ∀ n, F n ≤ CostSkeleton.lgN n) (hcap8 : ∀ n, F n ^ 8 ≤ Nat.log 2 n ^ 7)
    (hcapNeed : ∀ n m : ℕ, 16 ≤ n → capNeed n < (n + m + 2) ^ (e + 1))
    (hthr : Dispatch.ThrSpec thr F capNeed) (hcore : CoreSpec e ps core Kc) :
    (chdProgOf thr e ps core).Exact ∧ ∀ (G : Graph) (s : Fin G.n),
      (chdProgOf thr e ps core).RunsWithin G s
        ((bodyC Kc + 65536 * 9 + 100) * GateCTarget.Tdisp F G.n G.m) := by
  have hruns := Dispatch.dispatch_runs_of e (by omega) ps thr (chdBody core) Frontier.RAM.BF.prog F
    capNeed (bodyC Kc) 9 (by unfold bodyC; linarith) (by norm_num) hcapNeed hthr
    (body_spec_of F e (by omega) ps core Kc hKc hFl hcap8 hcore)
    (Dispatch.bf_bodySpec e ps)
  refine ⟨fun G s => ?_, fun G s => ?_⟩
  · obtain ⟨f, r, hr, hsol, -⟩ := hruns G s
    exact ⟨f, r, hr, hsol⟩
  · obtain ⟨f, r, hr, -, hc⟩ := hruns G s
    exact ⟨f, r, hr, hc⟩

/-- **The Gate-C target from a threshold-parametric witness.** -/
theorem chdTarget_of_named_of (thr : Stmt) (F capNeed : ℕ → ℕ) (e : ℕ) (he : 160 ≤ e)
    (ps : List Stmt) (core : Stmt) (Kc : ℝ) (hKc : 0 ≤ Kc)
    (hFl : ∀ n, F n ≤ CostSkeleton.lgN n) (hcap8 : ∀ n, F n ^ 8 ≤ Nat.log 2 n ^ 7)
    (hcapNeed : ∀ n m : ℕ, 16 ≤ n → capNeed n < (n + m + 2) ^ (e + 1))
    (hthr : Dispatch.ThrSpec thr F capNeed) (hcore : CoreSpec e ps core Kc) :
    GateCTarget.CHDTarget F :=
  ⟨chdProgOf thr e ps core, (chdProg_exact_within_of thr F capNeed e he ps core Kc hKc hFl hcap8
      hcapNeed hthr hcore).1, bodyC Kc + 65536 * 9 + 100,
    (chdProg_exact_within_of thr F capNeed e he ps core Kc hKc hFl hcap8 hcapNeed hthr hcore).2⟩

theorem chdProg_exact_within (e : ℕ) (he : 3 ≤ e) (ps : List Stmt) (core : Stmt) (Kc : ℝ)
    (hKc : 0 ≤ Kc) (hcore : CoreSpec e ps core Kc) :
    (chdProg e ps core).Exact ∧ ∀ (G : Graph) (s : Fin G.n),
      (chdProg e ps core).RunsWithin G s
        ((bodyC Kc + 65536 * 9 + 100) * GateCTarget.Tdisp GateCCalc.F G.n G.m) := by
  have hruns := Dispatch.dispatch_runs e he ps (chdBody core) Frontier.RAM.BF.prog (bodyC Kc) 9
    (by unfold bodyC; linarith) (by norm_num) (body_spec e he ps core Kc hKc hcore)
    (Dispatch.bf_bodySpec e ps)
  refine ⟨fun G s => ?_, fun G s => ?_⟩
  · obtain ⟨f, r, hr, hsol, -⟩ := hruns G s
    exact ⟨f, r, hr, hsol⟩
  · obtain ⟨f, r, hr, -, hc⟩ := hruns G s
    exact ⟨f, r, hr, hc⟩

theorem chdTarget_of_named (e : ℕ) (he : 3 ≤ e) (ps : List Stmt) (core : Stmt) (Kc : ℝ)
    (hKc : 0 ≤ Kc) (hcore : CoreSpec e ps core Kc) : GateCTarget.CHDTarget GateCCalc.F :=
  ⟨chdProg e ps core, (chdProg_exact_within e he ps core Kc hKc hcore).1,
    bodyC Kc + 65536 * 9 + 100, (chdProg_exact_within e he ps core Kc hKc hcore).2⟩

/-- **Space**: the named witness's terminating run on every graph also uses space (allocated cells)
at most `(bodyC Kc + 65536·9 + 100) · Tdisp F n m` (space ≤ cost in the RAM model). -/
theorem chdProg_space (e : ℕ) (he : 3 ≤ e) (ps : List Stmt) (core : Stmt) (Kc : ℝ)
    (hKc : 0 ≤ Kc) (hcore : CoreSpec e ps core Kc) (G : Graph) (s : Fin G.n) :
    ∃ fuel r, (chdProg e ps core).run fuel G s = some r ∧
      (r.space : ℝ) ≤ (bodyC Kc + 65536 * 9 + 100) * GateCTarget.Tdisp GateCCalc.F G.n G.m := by
  obtain ⟨fuel, r, hr, hc⟩ := (chdProg_exact_within e he ps core Kc hKc hcore).2 G s
  refine ⟨fuel, r, hr, ?_⟩
  have h := Frontier.Audit.RAMAudit.run_space_le_cost (chdProg e ps core) fuel G s r hr
  have h' : (r.space : ℝ) ≤ r.cost := by exact_mod_cast h
  linarith

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.chdProg_exact_within_of
#print axioms Frontier.CHD.L6.chdTarget_of_named_of
#print axioms Frontier.CHD.L6.chdProg_exact_within
#print axioms Frontier.CHD.L6.chdProg_space
