# `Submission/` — the race rows of the C-HD proof

This directory is NOT part of the `Frontier` library target.  It holds

* `SsspStatement.lean` — **vendored verbatim** from the Big-O-Speedrun verifier tree
  (`challenges/directed-sssp/VerifierStatement.lean`, sha256
  `cf5752049bcffcdbd9f2368cac10a57fc392881d2754a5fa60e7741519d2a6ca`), which is not in this
  checkout.  It defines `Cap`, `Sparse`, `Time`, `CorrectWithin`, `Bound` — the trusted target.
  Do not edit it; re-vendor it if the verifier's file changes.
* `Cap87Row.lean` — **the `7/8` row**: `Bound 1 (7/8) 1 (23/24) 0`, i.e. "with at most
  `n · ⌊⌊log₂ n⌋^{7/8}⌋` edges the time is `O(n · (log n)^{23/24})`", proved from
  `Frontier.CHD.Final.chd_exact_within87` (the `7/8` dispatcher `thrProg87` + the `F87` cap).

It imports only the vendored statement and the `Frontier` library — in particular it does **not**
import the untrusted `Submission/Validation.lean` of the verifier tree; the four glue lemmas it
needs (`correctWithin_mono`, `correctWithin_of_exact`, `one_le_log`, `natLog_le_two_log`) and
`tchd_nonneg` are proved locally.

## How to check it

The directory is deliberately not a `lake_lib`, so that this repository's `lakefile.toml` keeps a
single target while the verifier pins stay untouched.  Build it by hand:

```bash
cd formal/lean
lake env lean -o Submission/SsspStatement.olean Submission/SsspStatement.lean
LEAN_PATH=".:$LEAN_PATH" lake env lean Submission/Cap87Row.lean
# expect: no output except  '...chd_bound87' depends on axioms: [propext, Classical.choice, Quot.sound]
```

To make it part of a lake build instead (what the verifier harness does), either add

```toml
[[lean_lib]]
name = "Submission"
```

to `lakefile.toml` and `import Submission.Cap87Row` from your `Submission.lean`, or point the
harness's own `Submission/` at this file — it only needs `Submission/SsspStatement.lean` next to it.

## The row

```lean
theorem chd_bound87 : Bound 1 (7 / 8) 1 (23 / 24) 0
```

The witness program is `Frontier.CHD.Final.chdProgram87` (the C-HD program with the `7/8`
dispatcher, word exponent 160).  The bound constant is `(|K| + 1) * 57` where
`K = bodyC KcC + 65536 * 9 + 100` is the program's own cost constant.

## The two analytic facts (both with room to spare)

On the cap (`m ≤ 2 n ℓ^{7/8}`, `ℓ = log n`):

1. **the density log**: `log(m/(n+1) + 2) ≤ log(4ℓ) ≤ 2 + 24·ℓ^{1/24}`
   (`Real.log_le_rpow_div` at `s = 1/24`), so
   `m · log(m/(n+1)+2) ≤ 2nℓ^{7/8} · (2 + 24ℓ^{1/24}) ≤ 52 · n · ℓ^{11/12} ≤ 52 · n · ℓ^{23/24}`
   — the `1/24`-slack leaves the exponent at `11/12`, one notch below the row's `23/24`.
2. **the `2/3`-power term**: `m^{1/3}(n log(n+2))^{2/3} ≤ (2nℓ^{7/8})^{1/3}(2nℓ)^{2/3}
   = 2n · ℓ^{7/24 + 2/3} = 2n · ℓ^{23/24}` — an equality, which is exactly why the row's
   exponent is `23/24` and not smaller.

Together with the first two terms (`n + m ≤ 3 n ℓ^{23/24}`) this gives
`Tchd n m ≤ 57 · n · (log n)^{23/24}` on the cap, and `Tdisp F87 ≤ 8 (n+1)(m+1)` everywhere
(Bellman–Ford fallback), which is the `Bound` quintuple.

## Honest notes

* `Tdisp F87` is *not* monotone-dominated by `Tdisp F`: on the middle density range
  `n·F n < m ≤ n·F87 n` the `3/4` dispatcher would send the input to Bellman–Ford while
  `Tdisp F87 = Tchd` there.  The dispatch program therefore really must be `thrProg87`; this row is
  not a re-labelling of the `3/4` row.
* `N = 16` is the `Bound` convention's floor.  The proofs of `tchd_le`, `tdisp_le_poly` and
  `sparse_le_real` all use `n ≥ 16` (in particular `log n ≥ 1` and `log(n+2) ≤ 2 log n`), so the
  row's `N` cannot be lowered without redoing those constants.
* Stretch rows (`1 (19/20) 1 (59/60) 0`, plan M4) need `tphys` at `p = 10`: `lgN ≤ C t^{15}`, i.e.
  `F^10`-style root powers, and the master-cost constant `cI = 3826` no longer absorbs
  `211·(3p+4)` — see the M1 report's `α ≤ 7/8` ceiling.  Not attempted here.
