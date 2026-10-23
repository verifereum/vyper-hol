# TASK: AbiCopy encodes a static value with one MCOPY

## Meta
Status: planned
Priority: P1
Created: 2026-10-23
Location: lowering/ (project root is the directory holding holproject.toml)

## Theorem Statement (FROZEN)

In `lowering/abiEncoderPropsScript.sml`:

```sml
Theorem compile_abi_encode_copy_frag:
  ∀ctx dst src mem_size st op st' s0 dst_w src_w tenv ty tv v av R.
    compile_abi_encode_to_buf dst src (AbiCopy mem_size) st = (op, st') ∧
    evaluate_type tenv ty = SOME tv ∧
    ¬is_dynamic (vyper_to_abi_type tenv ty) ∧
    mem_size = type_memory_size tv ∧
    mem_size < dimword (:256) ∧
    value_has_type tv v ∧
    vyper_to_abi tenv ty v = SOME av ∧
    eval_operand dst s0 = SOME dst_w ∧
    eval_operand src s0 = SOME src_w ∧
    val_in_memory tv v (w2n src_w) s0.vs_memory
    ⇒
    frag_exec ctx st st' (λs. s = s0)
      (λs. eval_operand op s = SOME (n2w mem_size) ∧
           mem_bytes_at (w2n dst_w) mem_size s.vs_memory =
             enc (vyper_to_abi_type tenv ty) av ∧
           (∀x w. not_fresh_at st x ∧ lookup_var x s0 = SOME w ⇒
                  lookup_var x s = SOME w) ∧
           s.vs_allocas = s0.vs_allocas ∧
           (∀a. a < LENGTH s0.vs_memory ∧
                (a < w2n dst_w ∨ w2n dst_w + mem_size ≤ a) ⇒
                EL a s.vs_memory = EL a s0.vs_memory) ∧
           LENGTH s0.vs_memory ≤ LENGTH s.vs_memory) R
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. The build below passes with no CHEAT for `compile_abi_encode_copy_frag`
   and none in any helper you add.
2. Other cheats in `abiEncoderPropsScript.sml` (the Resume blocks of
   `compile_abi_encode_to_buf_correct`, `compile_abi_decode_static_correct`)
   are out of scope: leave them and their comments as they are.
3. No duplicate or near-duplicate lemmas; each helper exists once in its most
   general form, in the theory where it belongs (memory-layout facts about
   `val_in_memory` belong with the other value-encoding lemmas, e.g.
   `lowering/proofs/valueEncodingProofsScript.sml` /
   `lowering/valueEncodingPropsScript.sml`; generic MCOPY/run facts next to
   their peers).
4. Don't edit any existing theorem statement or definition.

**If the theorem is false as stated:** produce a HOL4 counterexample, state
the tightest sufficient fix, and stop. Do NOT weaken the statement.

## Build

```
holbuild -j4 build --allow-cache-timeout-discrepancy abiEncoderPropsTheory
```

`--allow-cache-timeout-discrepancy` is needed only because an unrelated
ancestor (`vyperInterpreterTheory`) was built without the step timeout; it does
not change the timeout for theories you edit.

## Background

The Vyper→Venom lowering ABI-encodes a value whose ABI type is static by
copying its memory image to the output buffer with a single MCOPY
(`compile_abi_encode_to_buf` on `AbiCopy`). This theorem states that this
fragment, run from `s0`, writes exactly the ABI encoding of the value at the
destination, leaves variables and allocations alone, leaves memory outside the
destination range unchanged, and only grows memory. It is stated over
`frag_exec`, the lowering's fragment-execution judgment.

A statement check found it true for every ABI-static type: bool, uintN,
intN, decimal, address, bytesN, flags, static tuples and structs, and fixed
arrays including sparse `SArrayV` values, where absent indices hold the
element type's default (`val_in_memory` requires that).

## Domain Constraints

- holbuild only; never raise the tactic timeout (2.5 s per step). A slow step
  is a proof bug: split it or cut the rewrite set.
- No `TRY`/`ORELSE` around `metis_tac` or other search tactics.
- No `let` in theorem statements. No new axioms.
- Never use `g`/`e` REPL sessions; probe via the build (a scratch lemma ending
  in `cheat`, or `goalStack.print_tac`), and remove probes when done.
- Read `AGENTS.md` at the project root before starting.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Codegen | `lowering/defs/abiEncoderScript.sml` (`compile_abi_encode_to_buf_def`, AbiCopy clause) | the single `emit_void MCOPY [dst; src; Lit (n2w mem_size)]` |
| Emit/monad | `lowering/defs/` (`rg 'Definition emit_void_def\|Definition emit_def'`) | compile monad, `emitted_insts`, `fresh_id` |
| frag_exec | `lowering/fragExecScript.sml` (`frag_exec_def` ~:128, `frag_exec_run_inst_seq` ~:477) | reduces a straight-line fragment to `run_inst_seq` |
| Venom MCOPY | `venom/defs/venomExecSemanticsScript.sml` (`mcopy_def` :80, MCOPY step ~:597) | reads source, then `write_memory_with_expansion` |
| Venom memory | `venom/defs/venomStateScript.sml` (`read_memory`, `write_memory_with_expansion`) | |
| Memory layout | `lowering/defs/valueEncodingScript.sml` (`val_in_memory_def`, `mem_bytes_at_def`, `type_memory_size_def`) | |
| Value-encoding lemmas | `lowering/proofs/valueEncodingProofsScript.sml`, `lowering/valueEncodingPropsScript.sml` | `val_in_memory_sarray`, `mem_bytes_at` lemmas, `val_wf_default_value_proof` |
| Prim/flag encoding | `lowering/abiEncoderPropsScript.sml` (`val_in_memory_prim_enc`, `val_in_memory_flag_enc`) | one-word cases; they assume `off + 32 ≤ LENGTH mem`, which this theorem does not give |
| ABI | `.holbuild/src/verifereum/util/contractABIScript.sml` (`enc_def`, `is_dynamic_def`, `static_length_def`, `has_type_def`, `enc_has_static_length`) | |
| Vyper→ABI | `semantics/vyperABIScript.sml` (`vyper_to_abi_def`, `vyper_to_abi_type_def`, sparse-array conversion) | |
| Types/values | `semantics/vyperValueScript.sml` (`evaluate_type_def`, `default_value`), `semantics/prop/vyperTypingScript.sml` (`value_has_type`) | |
| Freshness | `lowering/defs/compileEnvScript.sml` (`not_fresh_at_def`) | |
| Related proof | `lowering/abiEncoderPropsScript.sml`, `Resume compile_abi_encode_to_buf_correct[prim]` | proof of the one-word case of the older run_inst_seq-style lemma |
| Related frag lemmas | `lowering/loweringSliceScript.sml` | `frag_exec` proofs built with `frag_exec_run_inst_seq` |

## Notes

- `mem_size < dimword (:256)` is needed: `evaluate_type` bounds slot size, not
  memory size (`uint256[2^255]`).
- `value_has_type` is needed: e.g. `IntV (-1)` at `uint256` is stored as
  `i2w (-1)` but ABI-encodes differently.
