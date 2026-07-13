# Exported working agreements (user feedback memories)

Standing rules the user (Cody Tapscott, Julia compiler dev) has given across sessions.
Exported 2026-07-11 for machine migration — the new machine may differ (check whether
it is shared, where builds run, etc.), but the intent carries over.

## Git / publishing
- **Never push to GitHub.** No `git push`, force-push, or PR creation — work is local
  only. Don't even offer to push. Finish at the local commit.
- **Live checkout — no destructive git.** The user edits, rebases, and amends
  concurrently in the same checkout. Before any `reset --hard`, `checkout --`, rebase,
  or branch surgery: check `git status` for changes you didn't make and check for
  `.git/rebase-merge`/`rebase-apply`; if present, stop and coordinate. Never
  `git stash drop/clear/pop` without an explicit ref you created (the user keeps a
  deep stash stack). Prefer `git stash create` snapshots before surgery.
- **Never bare `git commit`.** The user keeps their own files staged (currently
  `JuliaLowering/src/precompile.jl`). Always commit by pathspec
  (`git commit <paths>` / `--amend --only <paths>`).
- Commits: "component: Brief summary" title, prose body, AI co-author trailer
  (`Co-Authored-By: ...`), disclose generative-AI assistance on any PR (per AGENTS.md).

## Process / autonomy
- **Questions are not instructions.** When the user asks a question or critiques,
  answer or propose only; edit/commit only on an explicit go-ahead ("please do X",
  "go ahead", "fix it").
- **Never spawn agents/workflows without explicit permission** — not even to
  parallelize mechanical work. Do it inline or propose the delegation plan first.
- **Share progress as you go.** The user wants to know what's happening and what
  progress is being made during long debugging, not a report at the end.
- **Builds:** on the old machine, `make -j8 release -C src` after runtime-only C/C++
  changes was explicitly authorized to run directly; full `make`/sysimage rebuilds
  should be asked about first (2–3+ min, user prefers to control them). Julia-side
  changes (base/, stdlib/, Compiler/) need the full rebuild to take effect —
  `make -C src` does NOT regenerate the sysimage.
- **Shared machine hygiene** (old machine was a shared 128-core box): never
  pgrep/pkill by name or pattern; capture PIDs at spawn and wait on those
  (`tail --pid=`), `nice` + `timeout` everything; if a build seems hung, report
  rather than kill.

## Measurement / evidence standards
- **Report per-change deltas**, not cumulative totals, for stacked changes — each
  commit is judged on its own baseline→after. Label series totals explicitly.
- **No stale data after behavior-changing fixes.** Re-measure every curve the fix can
  affect; when trimming a sweep for time, say which axes were dropped — never backfill
  from pre-fix numbers.
- **Litmus tests need a negative control first** — show the problem occurs WITHOUT the
  change before showing it fixed with it. Also make sure synthetic/duplicated test
  arms aren't provably dead (GVN can delete a vacuous `cond && guard` duplicate arm;
  use independent guards like `SCALE_GUARD[n]::Bool`).
- **Reproduce GC/runtime bugs empirically** before claiming a cause or fix — reasoning
  from code alone has repeatedly been wrong here. Build the smallest repro; add a
  temporary `jl_safe_printf` for hard-to-trigger paths; cross-check the stock build to
  distinguish regression from pre-existing bug; never conclude "can't happen" without
  testing.
- **Verify codegen claims against actual source** (src/codegen.cpp, src/gf.c, ...)
  rather than first principles.
- **Fast MWE iteration:** once a hypothesis is targeted, switch to a seconds-scale
  repro instead of multi-minute pipeline runs; estimate per-iteration cost × runs up
  front (>~10 min total ⇒ find a tighter repro). `make -C src` relink is a fast loop.

## Terminology / style
- Never say "tie"/"tied" for method dispatch — use "ambiguous"/"ambiguity".
- Don't inject component `-I` dirs (e.g. mmtk) into `LLVM_CFLAGS`/`LLVM_CXXFLAGS` in
  src/Makefile — use a dedicated variable (e.g. `MMTK_CPPFLAGS`) at the front of the
  individual compile recipes.
