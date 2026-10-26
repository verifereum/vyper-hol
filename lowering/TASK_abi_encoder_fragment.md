# TASK: Derive the source-value encoder fragment contract

## Meta

Status: planned
Priority: P1
Location: lowering/abiEncoderFragmentScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_abi_encode_to_buf_frag:
  !dst src ei st op st' ctx env ty tv v av s0 dst_w src_w lo top.
    compile_abi_encode_to_buf dst src ei st = (op, st') /\
    abi_enc_plan env ty ei /\
    evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\
    eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
    enc_pre st st' [dst; src] lo top tv v (w2n src_w)
      [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env ty) av))] s0 ==>
    frag_exec ctx st st' (\s. s = s0)
      (\s. mem_bytes_at (w2n dst_w)
             (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
           enc (vyper_to_abi_type env ty) av /\
           eval_operand op s =
             SOME (n2w (LENGTH (enc (vyper_to_abi_type env ty) av))) /\
           enc_frame st st' lo top
             [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env ty) av))] s0 s)
      (\r. F)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Prove the frozen theorem without admissions, axioms or kernel oracle calls.
- Derive the result from the recursive descriptor/window encoder results;
  do not build a second independent recursive execution proof.
- No dependency on the admitted legacy `compile_abi_encode_frag`, including
  through other admitted theorems. Existing unrelated ancestors may contain
  admissions, but no proof of this result may use one.
- Keep existing proven statements and definitions unchanged. Add genuinely
  needed source/frame/effect bridging results in suitable separate theories.
- If false, give a concrete HOL counterexample and the exact failing claim;
  do not add a precondition or a supported-language restriction.

## Build

```sh
holbuild --max-heap 7000 -j4 build abiEncoderFragmentTheory
```

Run builds from the project root. No whole-project build or parity rollup.
Validate any new shared helper machinery before using it in the final proof.

## Background

The existing external-return composition consumes the to-buffer clause of a
legacy mutual encoder theorem. The recursive descriptor/window encoder
already establishes exact ABI bytes and continuation simulation. This task
connects that result to typed source memory and the precise existing frame.
The new theorem preserves the external-return clause exactly.

## Domain Constraints

- Use holbuild, not interactive HOL or Holmake.
- Keep the existing tactic timeout; fix expensive steps instead of raising it.
- Never wrap proof search in TRY or ORELSE.
- Do not change lowering, source semantics or public hypotheses to make a
  bridge hold. Report a real mismatch instead.
- No new `let` in theorem statements; use tuples or records for shared context.
- Preserve audit and non-vacuity theories.
- Commit proof milestones with trailer `Bot: sol (OpenAI GPT-6.1 Sol)`.

## Available Resources

- `lowering/abiEncoderCorrectRecursiveScript.sml`: recursive closure for
  admissible descriptors and translated descriptors.
- `lowering/abiScratchEncoderRecursiveScript.sml`: precise physical scratch
  ownership variant of the same recursive encoder.
- `lowering/abiScratchEncoderContractScript.sml`,
  `lowering/abiScratchEffectScript.sml`,
  `lowering/abiScratchFootprintScript.sml`: exact scratch frame and allocation
  evolution contracts.
- `lowering/abiEncoderInputScript.sml`: complete recursive source windows.
- `lowering/abiEncoderAdmissibleScript.sml`: descriptor invariant.
- `lowering/abiEncoderPropsScript.sml`: `abi_enc_plan`, `enc_pre`, `enc_frame`
  and the admitted legacy mutual theorem. Its second clause is the target
  API; its dynamic-loop clause describes an obsolete helper convention.
- `lowering/valueEncodingPropsScript.sml`,
  `lowering/defs/valueEncodingScript.sml`: source representation, including
  omitted fixed-array defaults, and static ABI correspondence.
- `lowering/abiDecoderLoopScript.sml`, `lowering/fragExecScript.sml`:
  continuation simulation and fragment execution.
- `lowering/abiDecoderReentryScript.sml`,
  `lowering/abiDecoderVarExtendScript.sml`: variable pruning and restoration.
- `lowering/abiEncoderPhiScript.sml`,
  `lowering/abiEncoderMemberCodeScript.sml`,
  `lowering/abiEncoderArrayLoopLayoutScript.sml`: generated block shapes.
- `lowering/abiCallerAllocationScript.sml`,
  `lowering/abiScratchEncoderCallerScript.sml`: allocator bridges.
- `lowering/loweringHaltScript.sml`: external-return consumer.
- `lowering/defs/abiEncoderScript.sml`: actual encoder code.
- `git show 4ad8c0b0:lowering/abiEncoderPropsScript.sml`: reusable encoder
  frame, prefix and label-preservation lemmas for the earlier loop shape.
  Reuse applicable lemmas without reviving its independent recursive proof.

## Notes

Do not alter existing theorem statements. The final integration will replace
the external-return consumer's use of the admitted mutual theorem with this
new standalone to-buffer theorem. Helper decomposition belongs to the prover.
