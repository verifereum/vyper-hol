# TASK: Migrate ABI decoder proofs to bounded memory positions

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: lowering/abiBuiltinValidSourceScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem lower_abi_decode_valid_source:
  lower_abi_decode data (type_to_abi_dec_info sf ce ty) min_size max_size
    (type_memory_bytes ce ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf ty tv /\ evaluate_abi_decode env ty bs = INL v /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) src_base initial.vs_memory /\
  eval_operand data initial = SOME (n2w src_base) /\ abi_decoder_operand_live start.cs_next_var data /\
  abi_builtin_decode_resources start first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) src_base d b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st d (type_memory_bytes ce ty)
      b cap initial actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual

Theorem lower_abi_decode_valid_unwrap:
  let wrapped = (unwrap /\ needs_external_call_wrap ty) in
  let wrapped_ty = if wrapped then TupleT [ty] else ty in
  abi_decoder_coherent ce (get_tenv cx) sf ty tv /\
  evaluate_type_builtin cx (AbiDecode unwrap) ty arg_tys [vyperValue$BytesV bs] = INL v /\
  lower_abi_decode data (type_to_abi_dec_info sf ce wrapped_ty) min_size max_size
    (type_memory_bytes ce wrapped_ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) p initial.vs_memory /\
  eval_operand data initial = SOME (n2w p) /\ abi_decoder_operand_live start.cs_next_var data /\
  abi_builtin_decode_resources start first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) p d b cap initial /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st d (type_memory_bytes ce ty)
      b cap initial actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
```


Do not modify these statements. Prove them as-is, or produce a counterexample.
Their semantic predicates (resources, coherence, effects, source success, value
representation) may not be strengthened or weakened to make the proof pass.
Existing proofs remain in place. Internal compiler equations and helper interfaces
are weakly frozen only for the actual new base/position parameter and emitted code;
retain coverage and semantic guarantees. Surface a genuinely false semantic claim
before changing it. These statements have not been parsed on this new emitter:
ancestors still use the old arity. An independent owner preflight is required
before this task launches.

## Completion Criteria

- Migrate the existing helper chain through both frozen endpoints to emitter
  f1974b2ed. Preserve calldata/code coverage and memory success coverage.
- Replace the memory bytes copying argument with the actual runtime-length copy
  and padded last-word zeroing. Do not claim full-capacity bytes were copied.
- Build both target theories and every changed helper, at default tactic timeout.
- Migrate and build the two encountered-bug tests in abiDecodeBoundsTestTheory:
  wrapping offset rejection and rejection before an out-of-bounds length load.
- No new admissions/axioms, lost proof code, unsafe tactics or timeout overrides.
  Leave inherited unrelated admissions alone and list consumed ones.
- Commit checked source with trailer `Bot: astra (OpenAI GPT-6 Astra)`; do not push.

## Build

```sh
holbuild -j2 build abiBuiltinValidSourceTheory abiBuiltinValidUnwrapTheory abiDecodeBoundsTestTheory
```

Build changed lower prerequisites first. Normal checkpoints, default2.5s tactic
limit, shared wrapper/default memory. Tool wall timeout up to7200s is permitted;
never remove a live lock or start duplicate builds. Owner does final forced replay.

## Background

The new emitter keeps a buffer base separate from a scalar source position.
Memory bounds are payload sizes; range guards compare positions before forming
base+position addresses for reads/copies. Calldata/code use base=Lit0w and retain
absolute positions and existing full-capacity copies. Memory Bytes decodes zero
the last padded word then copy32+runtime length, matching the upstream overread
repair. lower_abi_decode still consumes a dynamic Bytes memory value, returning
the same decoded value. Its setup no longer emits pointer hi=data_ptr+data_len.

Previous guard-phase work (56454826f..079a0695c) is applied as a starting point,
not a checked proof for this emitter. Shared range helper is unchanged, but all
compiler applications require the new base argument; phase/counter equations
must reflect additional address ADD instructions. Many successful old-emitter
proofs may be reusable. Do not restore old executable definitions.

## Domain Constraints

- No executable/source semantics edits. Keep f1974b2ed emitter unchanged.
- No new source-valid/resource assumptions on the frozen endpoints, directly or
  through their predicates. No canonical-input or alias workaround.
- No TRY/ORELSE around proof search. Do not raise/remove the tactic timeout.
- Do not work on full compile_abi_decode_case/compile_abi_encode_case, checker
  domain, encoder allocation migration, target/place or val_footprint.
- Proof helpers describing emitted code may change with that code. Retain
  substantive semantic results; report any false old helper with its consumers.
- Working TASK/PLAN/STATE/REFERENCE files stay out of the final PR.

## Available Resources

- lowering/defs/abiEncoderScript.sml: compile_abi_dec_addr, range check, recursive
  decoder with new base argument after load_opc before hi_op.
- lowering/defs/builtinAbiScript.sml: lower_abi_decode new position0 entry.
- lowering/defs/exprLoweringScript.sml: return decoder payload-size bound.
- lowering/abiDecoderRangeScript.sml: reusable scalar range execution boundary.
- lowering/abiDecoderBytes{Bound,Frame,Typed}Script.sml and abiDecoderBytesScript.sml:
  previous phase boundaries; memory copy conclusion needs actual new behavior.
- lowering/abiBuiltinDecode{Setup,Effect,Resources}Script.sml and
  abiBuiltinValidSourceScript.sml / abiBuiltinValidUnwrapScript.sml: source wrapper.
- lowering/abiDecoder{Counters,Contract,ArrayInitExec,ReentryPointer}Script.sml:
  existing helper chain and phase obligations.
- REFERENCE_prior_guard_migration.patch: old-emitter proof work, reference only.

## Notes

This is a source-success proof migration, not the arbitrary-input rejection case.
All final statements and their semantic hypotheses stay frozen. The two existing
runtime regressions are retained; exact abort instruction indices may change with
the new generated code, but rejection must still precede the invalid load.
