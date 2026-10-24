# TASK: frag_exec loop rule

## Meta
Status: planned
Priority: P1
Created: 2026-10-25
Location: lowering/ (file lowering/fragExecScript.sml)

## Theorem Statement (FROZEN)

```sml
Theorem frag_exec_loop:
  !ctx st0 st1 sth stj st2 stb ste st3 stx hdr body exit cnd
   x0 x1 x2 x3 x4 x5 I J N R.
    emit_inst JMP [Label hdr] [] st0 = (x0, st1) /\
    new_block hdr st1 = (x1, sth) /\
    emit_inst JNZ [cnd; Label exit; Label body] [] stj = (x2, st2) /\
    new_block body st2 = (x3, stb) /\
    emit_inst JMP [Label hdr] [] ste = (x4, st3) /\
    new_block exit st3 = (x5, stx) /\
    cs_extends sth stj /\ cs_extends stb ste /\
    (!k s l. I k s ==> I k (jump_to l s)) /\
    (!k s l. J k s ==> J k (jump_to l s)) /\
    (!k. k <= N ==> frag_exec ctx sth stj (I k) (J k) R) /\
    (!k s. k <= N /\ J k s ==>
           ?w. eval_operand cnd s = SOME w /\ (w = 0w <=> k < N)) /\
    (!k. k < N ==> frag_exec ctx stb ste (J k) (I (SUC k)) R) ==>
    frag_exec ctx st0 stx (I 0) (J N) R
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build fragExecTheory` passes with no CHEAT for `frag_exec_loop` and no failures.
2. No duplicate lemmas; helpers go in `lowering/fragExecScript.sml` next to the existing rules.
3. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. No proof over ~50 lines; no step near the 2.5 s tactic timeout (never raise it).

**If the theorem is false as stated:** give a concrete counterexample and the tightest fix. Do NOT weaken the statement.

## Build

```
holbuild -j4 build fragExecTheory
```
(run from the project root, the directory containing holproject.toml)

## Background

`frag_exec ctx st st' P Q R` (lowering/fragExecScript.sml) is the fragment judgment for code the compile monad emits between compile states st and st'. This lemma is the rule for loops as the ABI encoder (`compile_abi_encode_dyn_loop`, `compile_abi_encode_dyn_static_loop` in lowering/defs/abiEncoderScript.sml) emits them: JMP to a fresh header block, header code ending in JNZ to exit or body, the body fragment (may contain blocks of its own), JMP back to the header, then the exit block. It will be used to prove the ABI encoder correct over multiple blocks.

## Domain Constraints

- Project rules in AGENTS.md at the project root: holbuild only, no interactive g/e sessions, use rename1 rather than generated names.
- Don't edit files under semantics/ or venom/.
- Don't change existing theorems; add helpers.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| frag_exec, run_from, fn_has_code, cs_extends, emitted_blocks | lowering/fragExecScript.sml | definitions and existing rules: frag_exec_seq, frag_exec_enter, run_from_jump, run_from_jump_result, run_from_step, fn_has_code_split/start/mid/new_block, cs_extends_* |
| compile monad primitives | lowering/defs/compileEnvScript.sml (emit, new_block, fresh_id), lowering/defs/emitHelperScript.sml (emit_inst) | |
| step_inst_base (JMP, JNZ) | venom/defs/venomExecSemanticsScript.sml (~line 600-640) | JNZ [c; l1; l2] jumps to l1 if c ≠ 0w, else l2 |
| jump_to | venom/defs/venomStateScript.sml:292 | |
| exec_block, run_blocks | venom/defs/venomExecSemanticsScript.sml | |
| example multi-block proofs using frag_exec | lowering/loweringSliceScript.sml, lowering/stmtLoweringPropsScript.sml | |
