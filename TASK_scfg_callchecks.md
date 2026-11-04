# TASK: SimplifyCFG keeps CALL success checks (call_checks_ok)

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: venom/passes/simplify_cfg/proofs/simplifyCfgCallChecksScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem simplify_cfg_call_checks_ok:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn ==>
  call_checks_ok (simplify_cfg_fn fn)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

Supporting definitions (do not change them): `call_checks_ok`,
`calls_flagged`, `flag_path`, `flag_fails`, `revert_path`, `fn_shape_ok`,
`inst_shape_ok`, `label_positions_ok` in
`venom/compiler/unitShapeDefsScript.sml`; the pass in
`venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml`
(`simplify_cfg_fn fn = FST (simplify_cfg_fn_with_labels fn)`);
`wf_function`, `fn_inst_wf` in `venom/defs/venomWfScript.sml`;
`first_block_no_preds` (rg).

## Completion Criteria

1. `simplifyCfgCallChecksTheory` builds with no cheat. Replace only the
   `cheat` of `simplify_cfg_call_checks_ok`; put helper lemmas in
   `simplifyCfgCallChecksScript.sml` (or new theories under
   `venom/passes/simplify_cfg/proofs/`), adding Ancestors as needed.
2. Leave every definition, `venom/compiler/`, simplifyCfgProofScript.sml,
   simplifyCfgCorrectnessScript.sml and the other proof theories alone,
   except dropping `[local]` from a lemma you need.
3. No duplicate or near-duplicate lemmas: reuse what's already proved.

**If the theorem is false as stated:** produce a HOL4 counterexample
(`EVAL` on a concrete function), state the tightest sufficient fix, and stop.

## Build

```
holbuild --gcthreads 1 --max-heap 7000 -j2 build simplifyCfgCallChecksTheory
```

(`--gcthreads 1` works around a holbuild startup GC crash on this box;
the `holbuild` on PATH for this run already adds it.)

## Background

`call_checks_ok fn`: in every block, after each CALL/STATICCALL, the rest
of the block reaches a failing instruction (ASSERT of the flag or a copy;
JNZ on it into a revert path; JMP into a revert path; REVERT) before any
INVOKE, tracking the flag's ASSIGN copies and dropping them on state writes.
A revert path is a block with no INVOKE ending in REVERT or in a JMP to a
revert path, bounded by the block count.

SimplifyCFG (Vyper's `simplify_cfg.py`) removes unreachable blocks, merges a
block into its sole predecessor (the predecessor ends in JMP to it; its PHIs
become ASSIGNs/NOPs), bypasses single-JMP blocks (`do_merge_jump`, which
retargets the predecessor's terminator and canonicalizes `jnz c @L @L` to
`jmp @L` via `canon_jnz_inst`), renames labels and fixes PHIs, iterated
(bounded by the block count).

## Domain Constraints

- holbuild only; never raise the tactic timeout; no `TRY`/`ORELSE`
  around metis or other search; no `let` in statements.
- Proofs under ~50 lines each; split into helper lemmas.
- Read `AGENTS.md` at the project root.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Pass definitions | venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml | all pass pieces |
| Per-step invariant framework | venom/passes/simplify_cfg/proofs/simplifyCfgInvariantScript.sml | `simplify_cfg_fn_with_labels_every`, `simplify_cfg_fn_with_labels_opcodes`: lifting per-step facts through the iteration |
| Structural lemmas | venom/passes/simplify_cfg/proofs/simplifyCfg{LabelProps,Struct,Shape,LocalShape,CollapseShape,GraphShape,Opaque,PhiShape,Jnzdist}Script.sml | label maps, merge/bypass/removal shape preservation, JNZ distinct targets through the pass |
| Analogous proof for another pass | venom/passes/dft/proofs/dftCallChecksScript.sml | how DFT's preservation of call_checks_ok is proved (calls_flagged / flag_path / revert_path lemmas) |
| CFG transforms | venom/defs/cfgTransformScript.sml | `subst_label_inst`, `bb_succs`, `block_preds` |

## Notes

- Sketch of why it holds (checked by reading the definitions; not proof
  guidance): a merge appends a revert-path block's instructions after a JMP
  that was the failing instruction, so the path then ends at that block's
  REVERT or JMP-to-revert-path, which ignore the flag variables; bypass
  replaces a fail target b = [JMP T] by T, which is a revert path iff b is;
  canon_jnz turns JNZ c l l into JMP l with the same revert-path need;
  removal keeps every block reachable from a kept block, and the shorter
  block list still bounds an acyclic revert chain.
- Weakly frozen: any helper lemma statement may change.
