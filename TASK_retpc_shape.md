# TASK: Lowering shape proof with per-function return PCs (retpc_shape_ok)

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: lowering/proofs/ (loweringShapeDefsScript.sml, loweringShapeRulesScript.sml, loweringShapePropsScript.sml)

## Theorem Statement (FROZEN)

```sml
Theorem lower_vyper_runtime_unit_source_unit_ok_names:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ immutable_free_program tops ==>
    o1_source_unit_ok unit
```

and, unchanged from before this task:

```sml
Theorem run_lowering_source_unit_ok:
  !selectors external_fns internal_fns fallback_fn rpolicy bucket_count
   fn_metadata_bytes dense_buckets entry_info unit.
    run_lowering selectors external_fns internal_fns fallback_fn rpolicy
      bucket_count fn_metadata_bytes dense_buckets entry_info "__entry" =
      SOME unit /\
    EVERY (\(sel, lbl, z). isPREFIX "fn_" lbl) selectors /\
    EVERY external_fn_shape_ok external_fns /\
    fallback_shape_ok fallback_fn /\
    EVERY internal_fn_shape_ok internal_fns /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) ==>
    o1_source_unit_ok unit
```

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

What changed: `fn_shape_ok` (venom/compiler/unitShapeDefsScript.sml) now has
the conjunct `retpc_shape_ok fn` (every RET's last operand is a `retpc_var`
of the same function; no PHI mixes return-PC and other variables), so
`o1_source_unit_ok` is stronger. To prove it of the lowering, the shape
invariant in `loweringShapeDefsScript.sml` was changed (these definitions are
frozen too: `internal_label_ok`, `fn_suffix`, `cur_fn_insts`, `rets_scoped`,
`retpc_operand`, `shape_state`, `shape_extends`), and the statements of these
lemmas were changed to match (weakly frozen: keep them unless one is false,
then fix it minimally and say why in a comment):
- loweringShapeRules: `shape_step_new_block` (+ `~internal_label_ok lbl`),
  `shape_append_inst` (+ RET hypothesis), generic emits exclude `RET`
  (`~MEM opc [GAS; RETPC_PARAM; RET]`), `ret_append_ok` and
  `shape_step_emit_inst_ret` (last operand must be `retpc_operand`, no longer
  plain).
- loweringShapeProps: `cenv_shape_ok` (return pc must be a `PtrVar` of a
  `retpc_operand`), `cenv_static_ok_shape_ok` (+ `ce_return_pc = NONE`),
  every `retpc_operand st pc \/ plain_operand st pc` became
  `retpc_operand st pc`, `lowered_fn_ok`, `internal_fns_ok`,
  `lowered_unit_source_ok` (+ `rets_scoped (entry ++ FLAT segs)`), and the new
  `rets_scoped_segments` (stated with `cheat`).

Every proof in the three theories that these changes break must be repaired,
and the cheat in `rets_scoped_segments` removed. Helper lemmas may be added
anywhere in the three theories.

## Completion Criteria

1. The build command below passes with zero CHEAT warnings and zero failures.
2. No proof replaced by `cheat`; no `TRY`/`ORELSE` around `metis_tac` or other
   search; no tactic-timeout changes; no new axioms.
3. No duplicate or near-duplicate lemmas.

**If a statement is false as stated:**
- Produce a counterexample.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build loweringShapePropsTheory unitShapeChecksTheory o1SourceUnitCheckTheory
```

Then the consumers (must still build):

```
holbuild -j4 build vyperLoweringCorrectTheory intCallLookupTheory e2eCorrectnessTheory o1PipelineComposeTheory o1ComposeSupportTheory o1FnScheduleDecompHelpersTheory evalCompilerSourceShapeTheory
```

## Background

The raw Vyper→Venom lowering emits all functions into one block stream: the
entry code (labels `__entry`, `fn_...`, compiler labels `@...`), then one
segment per internal function, which starts with a block labelled
`internal ...` (`internal_label_ok`) and opens only compiler-labelled blocks
after it. An internal function's prologue emits `RETPC_PARAM` and installs
`ce_return_pc := SOME (PtrVar return_pc 0)`; every RET of its body returns to
that variable. `fn_suffix (all_blocks st)` is the blocks of the function being
compiled, and `cur_fn_insts st` their instructions; `retpc_operand st op`
now requires its RETPC_PARAM output to be in `cur_fn_insts st`, which stays
true across steps because steps never open an `internal ...` block
(`shape_extends`). `rets_scoped` (in `shape_state`) records, per RET, that
its last operand came from its own function's prefix of the stream, which is
what `rets_scoped_segments` turns into a per-segment fact at the end.

## Domain Constraints

- HOL4 via holbuild only. Default tactic timeout (2.5 s per step); a step
  over it is a proof performance bug: split it or cut the rewrite set.
- Proof scripts use `Theorem ... Proof ... QED`; never `g`/`e` sessions.
- Proofs at most ~50 lines; long cases go into helper lemmas.
- Don't depend on generated names; use `rename1`.
- Don't change definitions outside `lowering/proofs/loweringShape*` or the
  executable lowering (`lowering/defs`).

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Shape defs | lowering/proofs/loweringShapeDefsScript.sml | invariant, `fn_suffix`, `rets_scoped`, mono lemmas |
| Shape rules | lowering/proofs/loweringShapeRulesScript.sml | `shape_step` rules, `shape_append_inst`, emit lemmas |
| Shape props | lowering/proofs/loweringShapePropsScript.sml | per-generator shape lemmas, final assembly (`lowered_fn_ok`, `internal_fns_ok`, `lowered_unit_source_ok`, `run_lowering_source_unit_ok`) |
| Unit shape | venom/compiler/unitShapeDefsScript.sml | `fn_shape_ok`, `retpc_shape_ok`, `copy_phi_var` (rule `copy_phi_var_seed`) |
| compile state | lowering/defs/compileEnvScript.sml | `cs_extends`, `new_block`, `compiler_labels_future` |
| Return lowering | lowering/defs/stmtLoweringScript.sml (`compile_internal_return`), lowering/defs/moduleLoweringScript.sml (`compile_internal_function`) | where RET and RETPC_PARAM come from |
| Proof lessons | docs/HOL4_PROOF_CONTROL_LESSONS.md, AGENTS.md | project proof style |

## Notes

The theories are big (Props is ~12.8k lines); build the lowest failing
theory first (Defs, then Rules, then Props).
