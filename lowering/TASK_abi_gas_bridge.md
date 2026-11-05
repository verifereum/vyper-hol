# TASK: Counted paths for GAS-free fragments

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/exprSimAbiGasBridgeScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem frag_exec_gas_path:
  !ctx sa sb P Q R fn s.
    frag_exec ctx sa sb P Q R /\ cs_extends sa sb /\ frag_gas_free sa sb /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\ (!h. ~R (Halt h)) /\
    fn_has_code sa sb fn /\ P s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?r. gas_marked_path F ctx fn s 0 r /\ exit_result r /\ R r)

Theorem abi_decode_sim_gas_path:
  !ctx sa sb Q fn s.
    (!fn. fn_has_code sa sb fn ==>
       ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           abi_decode_sim ctx fn s t) /\
    cs_extends sa sb /\ frag_gas_free sa sb /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    fn_has_code sa sb fn /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
```

Do not modify these statements. Prove them as-is, or produce a counterexample. `frag_code_def` and `frag_gas_free_def` in the same file are frozen with them.

## Completion Criteria

- Both theorems are proved with no `cheat`, in `lowering/exprSimAbiGasBridgeScript.sml` or in new helper theories named `exprSimAbiGasBridge<Part>`.
- No new axioms, admissions or definitions beyond proof-only helpers in those theories.
- `holbuild -j4 build exprSimAbiGasBridgeTheory` passes at the default step limit.
- Commit checked work with the trailer `Bot: opus (Claude Opus 5.5)`; do not push.

## Build

From the project root:

```sh
holbuild -j4 build exprSimAbiGasBridgeTheory
```

Default tactic timeout and memory limits; no other targets.

## Background

The counted expression judgments of the compiler proof need an actual `gas_marked_path` (`lowering/fragGasModeScript.sml`) through the code a fragment emitted. Older fragment proofs, including the ABI encoder and decoder executions, conclude `frag_exec` (`lowering/fragExecScript.sml`) or `abi_decode_sim` (`lowering/abiDecoderLoopScript.sml`) instead. These say what running the fragment reaches, as a run_from simulation. `lowering/fragGasPathScript.sml` has only the converse direction (`gas_path_normal`, `gas_path_exit`). These two theorems are the missing bridge for fragments that run no GAS, INVOKE or PHI, never jump back to the block they start in, and end in a block of a label they did not finish (`frag_gas_free`).

`frag_exec` quantifies over every function with `fn_has_code`. That is what makes the bridge possible: a function that keeps only the fragment's blocks and puts STOP right after the fragment's end turns the simulation into a halting run.

## Domain Constraints

- Don't change any existing theory. Helpers go only in `exprSimAbiGasBridge*` theories.
- No TRY/ORELSE around proof search, no timeout overrides, no unsafe tactics.

## Available Resources

- `lowering/fragExecScript.sml`: `run_from`, `exit_result`, `emitted_blocks`, `fn_has_code`, `frag_exec`, and the jump lemmas `run_from_jump_target`/`run_from_jump_result`/`frag_exec_enter`.
- `lowering/fragGasPathScript.sml`: `gas_path_edge`, `gas_path` and its lemmas.
- `lowering/fragGasModeScript.sml`, `lowering/fragGasSeqScript.sml`: `gas_marked_path` and straight-line paths (`tuple_run_inst_seq_gas_path`).
- `lowering/abiDecoderLoopScript.sml`: `abi_decode_sim`.
- `lowering/exprLoweringPropsScript.sml`: `emitted_insts`, `same_blocks`.
- `lowering/defs/compileEnvScript.sml`: `cs_extends`.
- `venom/defs/venomExecSemanticsScript.sml`, `venom/defs/venomStateScript.sml`: step semantics, STOP, `halt_state`, `jump_to`.
- `lowering/alan-ref/abiArgsObservation.sml.txt` (reference copy, not a build input): `abi_frag_halting_observer`, a related observer construction from earlier work, for ideas.

## Notes

The statements build with `cheat` (ancestors restored from cache). An independent read-only check found two counterexamples to an earlier draft, now excluded by the PHI and end-label clauses of `frag_gas_free`. With those it judged both statements provable. It also noted the proof needs a lemma that a non-Error `run_from` result in INVOKE-free code has a `gas_path`, and that lemma does not exist yet.

Proof idea (not binding): instantiate `frag_exec` at an observer function holding only the fragment's blocks, with the end block truncated to `sb.cs_current_insts ++ [STOP]`. There `run_from` halts, giving a `gas_path`. Cut it at the first visit of the end position and transfer the prefix to `fn`.
