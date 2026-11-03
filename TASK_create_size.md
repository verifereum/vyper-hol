# TASK: Repair proofs after the parent-frame CREATE initcode limit

## Meta
Status: prepared; guard and exact corrected contracts independently audited PROVABLE
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

The executable guard definitions and corrected contracts below are frozen:

```sml
Definition exec_create_def:
  exec_create inst s value offset sz salt_opt =
    case inst.inst_outputs of
      [out] =>
        if w2n sz > 2 * max_code_size then
          Abort ExHalt_abort (halt_state (set_returndata [] s))
        else let rq = venom_create_request s value offset sz salt_opt;
                 (output, s') = consume_create_outcome rq s
             in OK (update_var out output s')
    | _ => Error "create requires single output"
End

Definition asm_exec_create_def:
  asm_exec_create s =
    case s.as_stack of
      value :: offset :: sz :: stk =>
        let off = w2n offset in
        let size = w2n sz in
        if size > 2 * max_code_size then AsmFault (s with as_returndata := []) else
        let mem = asm_expand_memory (off + size) s.as_memory in
        let init_code = TAKE size (DROP off mem) in
        let sender = s.as_call_ctx.cc_address in
        let nonce = (lookup_account sender s.as_accounts).nonce in
        let new_addr = address_for_create sender nonce in
        let gas = s.as_call_ctx.cc_gas -
                  s.as_call_ctx.cc_gas DIV 64 in
        let evm_s = make_asm_create_state s new_addr gas
                      (w2n value) init_code in
        (case extract_asm_result s (w2w new_addr) 0 0
                (run evm_s) of
           SOME (output, s') =>
             AsmOK (asm_next (s' with as_stack := output :: stk))
         | NONE => AsmError "create: non-terminating")
    | _ => AsmError "create: stack underflow"
End

Definition asm_exec_create2_def:
  asm_exec_create2 s =
    case s.as_stack of
      value :: offset :: sz :: salt :: stk =>
        let off = w2n offset in
        let size = w2n sz in
        if size > 2 * max_code_size then AsmFault (s with as_returndata := []) else
        let mem = asm_expand_memory (off + size) s.as_memory in
        let init_code = TAKE size (DROP off mem) in
        let sender = s.as_call_ctx.cc_address in
        let new_addr = address_for_create2 sender salt init_code in
        let gas = s.as_call_ctx.cc_gas -
                  s.as_call_ctx.cc_gas DIV 64 in
        let evm_s = make_asm_create_state s new_addr gas
                      (w2n value) init_code in
        (case extract_asm_result s (w2w new_addr) 0 0
                (run evm_s) of
           SOME (output, s') =>
             AsmOK (asm_next (s' with as_stack := output :: stk))
         | NONE => AsmError "create2: non-terminating")
    | _ => AsmError "create2: stack underflow"
End

Definition build_create_code_def:
  build_create_code tenv CreateMinimalProxy ops accounts ctor_tys blueprint_size =
    (case ops.co_code_src of
     | AddressCodeSource target => SOME <|
         cc_initcode := minimal_proxy_initcode target;
         cc_source_ok := T;
         cc_size_ok := T
       |>
     | _ => NONE) /\
  build_create_code tenv CreateCopyOf ops accounts ctor_tys blueprint_size =
    (case ops.co_code_src of
     | AddressCodeSource target =>
         let code = (lookup_account target accounts).code in
         SOME <| cc_initcode := create_copy_initcode code;
                 cc_source_ok := (code <> []);
                 cc_size_ok := T |>
     | _ => NONE) /\
  build_create_code tenv (CreateFromBlueprint raw_args) ops accounts ctor_tys blueprint_size =
    (case (ops.co_code_src, ops.co_code_offset) of
     | (AddressCodeSource target, SOME code_offset) =>
         let code = (lookup_account target accounts).code in
         let args_enc_opt =
           if raw_args then
             case ops.co_ctor_args of [BytesV bs] => SOME bs | _ => NONE
           else encode_create_ctor_args tenv ctor_tys ops.co_ctor_args
         in
           (case args_enc_opt of
            | NONE => NONE
            | SOME args_enc =>
                let n = case blueprint_size of
                        | NONE => blueprint_copy_size code_offset code
                        | SOME n => n in
                let size_ok = (n + LENGTH args_enc <= 2 * max_code_size) in
                SOME <|
                  cc_initcode := if size_ok then
                    blueprint_initcode n code_offset code args_enc else [];
                  cc_source_ok := blueprint_size_ok n;
                  cc_size_ok := size_ok
                |>)
     | _ => NONE) /\
  build_create_code tenv RawCreate ops accounts ctor_tys blueprint_size =
    (case ops.co_code_src of
     | BytecodeCodeSource bytecode =>
         (case encode_create_ctor_args tenv ctor_tys ops.co_ctor_args of
          | NONE => NONE
          | SOME args_enc => SOME <|
              cc_initcode := raw_create_initcode bytecode args_enc;
              cc_source_ok := T;
              cc_size_ok :=
                (LENGTH (raw_create_initcode bytecode args_enc) <= 2 * max_code_size)
            |>)
     | _ => NONE)
End

Theorem exec_create_single:
  inst.inst_outputs = [out] ==>
  exec_create inst s v off sz salt =
    if w2n sz > 2 * max_code_size then
      Abort ExHalt_abort (halt_state (set_returndata [] s))
    else OK (update_var out
      (FST (consume_create_outcome (venom_create_request s v off sz salt) s))
      (SND (consume_create_outcome (venom_create_request s v off sz salt) s)))

Theorem exec_create_success_regression:
  inst.inst_outputs = [out] /\ s.vs_outcomes = outcome::rest /\
  outcome.co_success ==>
  exec_create inst s value offset sz salt =
    if w2n sz > 2 * max_code_size then
      Abort ExHalt_abort (halt_state (set_returndata [] s))
    else OK (update_var out (w2w outcome.co_created)
      (s with <| vs_outcomes := rest;
        vs_requests := s.vs_requests ++
          [venom_create_request s value offset sz salt];
        vs_accounts := outcome.co_accounts;
        vs_transient := outcome.co_tStorage;
        vs_logs := s.vs_logs ++ outcome.co_logs;
        vs_pending_deletions := outcome.co_toDelete ++ s.vs_pending_deletions;
        vs_returndata := outcome.co_returnData |>))

Theorem exec_create_failure_regression:
  inst.inst_outputs = [out] /\ s.vs_outcomes = outcome::rest /\
  ~outcome.co_success ==>
  exec_create inst s value offset sz salt =
    if w2n sz > 2 * max_code_size then
      Abort ExHalt_abort (halt_state (set_returndata [] s))
    else OK (update_var out 0w
      (s with <| vs_outcomes := rest;
        vs_requests := s.vs_requests ++
          [venom_create_request s value offset sz salt];
        vs_accounts := outcome.co_accounts;
        vs_transient := outcome.co_tStorage;
        vs_logs := s.vs_logs;
        vs_pending_deletions := s.vs_pending_deletions;
        vs_returndata := outcome.co_returnData |>))

Theorem exec_create_preentry_failure_regression:
  inst.inst_outputs = [out] /\ s.vs_outcomes = outcome::rest /\
  ~outcome.co_success /\ outcome.co_returnData = [] ==>
  exec_create inst s value offset sz salt =
    if w2n sz > 2 * max_code_size then
      Abort ExHalt_abort (halt_state (set_returndata [] s))
    else OK (update_var out 0w
      (s with <| vs_outcomes := rest;
        vs_requests := s.vs_requests ++
          [venom_create_request s value offset sz salt];
        vs_accounts := outcome.co_accounts;
        vs_transient := outcome.co_tStorage;
        vs_logs := s.vs_logs;
        vs_pending_deletions := s.vs_pending_deletions;
        vs_returndata := [] |>))

Theorem exec_create_exhausted_regression:
  inst.inst_outputs = [out] /\ s.vs_outcomes = [] ==>
  exec_create inst s value offset sz salt =
    if w2n sz > 2 * max_code_size then
      Abort ExHalt_abort (halt_state (set_returndata [] s))
    else OK (update_var out 0w
      (s with <| vs_requests := s.vs_requests ++
          [venom_create_request s value offset sz salt];
        vs_returndata := [] |>))

Theorem compile_create_dispatch_unchecked_execution:
  ∀code_ptr code_len value_op salt cs result cs' s v p n salt_value.
  compile_create_dispatch code_ptr code_len value_op salt F cs = (result,cs') ∧
  eval_operand value_op s = SOME v ∧
  eval_operand code_ptr s = SOME p ∧ eval_operand code_len s = SOME n ∧
  OPTREL (λop w. eval_operand op s = SOME w) salt salt_value ⇒
  ∃out.
    result = Var out ∧
    let consumed = consume_create_outcome (venom_create_request s v p n salt_value) s in
    run_inst_seq (emitted_insts cs cs') s =
      (if w2n n > 2 * max_code_size then
         Abort ExHalt_abort (halt_state (set_returndata [] s))
       else OK (update_var out (FST consumed) (SND consumed))) ∧
    eval_operand result (update_var out (FST consumed) (SND consumed)) =
      SOME (FST consumed)

Theorem step_inst_base_abort_opcodes:
  !inst vs a vs'.
    step_inst_base inst vs = Abort a vs' ==>
    inst.inst_opcode = REVERT \/
    inst.inst_opcode = INVALID \/
    inst.inst_opcode = ASSERT \/
    inst.inst_opcode = ASSERT_UNREACHABLE \/
    inst.inst_opcode = CREATE \/
    inst.inst_opcode = CREATE2 \/
    inst.inst_opcode = RETURNDATACOPY

Theorem step_inst_abort_opcodes:
  !fuel ctx inst vs a vs'.
    step_inst fuel ctx inst vs = Abort a vs' ==>
    inst.inst_opcode = REVERT \/
    inst.inst_opcode = INVALID \/
    inst.inst_opcode = ASSERT \/
    inst.inst_opcode = ASSERT_UNREACHABLE \/
    inst.inst_opcode = CREATE \/
    inst.inst_opcode = CREATE2 \/
    inst.inst_opcode = RETURNDATACOPY \/
    inst.inst_opcode = INVOKE

Definition opcode_fail_class_def:
  opcode_fail_class ASSERT = CanRevert /\
  opcode_fail_class ASSERT_UNREACHABLE = CanExHalt /\
  opcode_fail_class RETURNDATACOPY = CanExHalt /\
  opcode_fail_class CREATE = CanExHalt /\
  opcode_fail_class CREATE2 = CanExHalt /\
  opcode_fail_class INVALID = CanExHalt /\
  opcode_fail_class INVOKE = AnyFail /\
  opcode_fail_class _ = NoFail
End

Theorem step_inst_base_abort_opcode:
  !inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode ==>
    inst.inst_opcode = ASSERT \/
    inst.inst_opcode = ASSERT_UNREACHABLE \/
    inst.inst_opcode = CREATE \/
    inst.inst_opcode = CREATE2 \/
    inst.inst_opcode = RETURNDATACOPY
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
All existing public theorem statements outside the nine explicitly corrected contracts above are also frozen. The six test statements in `tests/createSizeBoundaryTestScript.sml` and all existing witness statements in `tests/createSizeClassificationCounterexampleScript.sml` are frozen. The local lowerDloadClassify abort classification is also corrected to include CREATE/CREATE2.

## Completion Criteria

1. Build the targets below with the default 2.5-second proof-step budget.
2. Repair proof consumers of the new exceptional CREATE/CREATE2 path without any new admission, axiom, stronger hypothesis, timeout override, or oracle-truth assumption.
3. Keep all other executable definitions unchanged.
4. Preserve unaffected exported theorem statements and substantive results.

## Build

```sh
holbuild -j2 build createSizeClassificationCounterexampleTheory createSizeBoundaryTestTheory createOracleExecutionTheory createDispatchExecutionTheory opcodeClassTheory venomMemProofsTheory passSharedFrameTheory passSharedVarFrameTheory removeUnusedProofsTheory lowerDloadClassifyTheory mem2varBlockSimHelpersTheory concretizeMemLocProofsTheory ssaRenamedSimTheory genBlockSimTheory vyperCreateFrameTheory
```

## Background

The EVM rejects CREATE/CREATE2 initcode exceeding 49,152 bytes in the parent frame, before a constructor is entered. The old Venom oracle helper and assembly constructor bridge omitted that opcode guard. Source RawCreate also omitted its complete initcode size check. Those three executable repairs are already made and independently checked against the pinned EVM; their definition theories built at the default budget. New tests check the encountered 49,153-byte failure and the 49,152-byte inclusive boundary.

The nine old exported contracts above were false after the repair. Their replacements retain identical hypotheses, make CREATE results conditional on the size guard, and classify CREATE/CREATE2 among aborting opcodes. Existing proof bodies remain. The owner independently audited these exact replacements. Statements have not all been reached by a build yet; consumers still contain obsolete unconditional no-Abort assertions about CREATE.

## Domain Constraints

- Scope is proof repair for this size boundary, including proof-only helpers and existing consumers. Do not change lowering, typing rules, source semantics, codegen, pass contracts, or other executable definitions.
- Existing local helper assertions that CREATE can never Abort are false. Replace them truthfully with the exact size/output-shape characterization, or remove only the false local conjunct while preserving the substantive valid classifications. No new hypothesis on an exported theorem.
- Existing no-Halt/no-IntRet and successful-result frame statements remain unchanged.
- Do not work on the separate DALLOCA/FMP invariant or the admitted main `compile_create_sim`/`body_create_case` cases here.
- Retain unrelated inherited admissions, but add none and do not use them to replace proofs.
- No TRY/ORELSE around proof search; no proof-step timeout changes.

## Available Resources

| Resource | Location | Purpose |
| --- | --- | --- |
| Venom guard | `venom/defs/venomExecSemanticsScript.sml` | Frozen exec_create and instruction dispatch |
| Assembly guards | `venom/codegen/defs/asmSemScript.sml` | Frozen CREATE/CREATE2 behavior |
| Source creation | `semantics/vyperCreateScript.sml` | Frozen complete RawCreate initcode check |
| Boundary tests | `tests/createSizeBoundaryTestScript.sml` | Inclusive/oversized source, Venom, assembly cases |
| Oracle execution | `lowering/createOracleExecutionScript.sml` | Frozen corrected result contracts and frames |
| Dispatch | `lowering/createDispatchExecutionScript.sml` | Frozen corrected unchecked dispatch equality |
| Opcode classification | `venom/codegen/proofs/opcodeClassScript.sml` | Frozen public abort-opcode conclusions |
| Block codegen | `venom/codegen/proofs/genBlockSimScript.sml` | Existing assembly simulation |
| Plan generation | `venom/codegen/defs/stackPlanGenScript.sml` | Actual output/dead-output codegen |
| Memory frames | `venom/proofs/venomMemProofsScript.sml` | Existing terminal/frame helpers |
| Pass frames | `venom/passes/shared/proofs/passSharedFrameScript.sml` | Existing helper assertions |
| Variable frames | `venom/passes/shared/proofs/passSharedVarFrameScript.sml` | Existing helper assertions |
| Unused removal | `venom/passes/remove_unused/proofs/removeUnusedProofsScript.sml` | Existing helper assertions |
| Dload classification | `venom/passes/lower_dload/proofs/lowerDloadClassifyScript.sml` | Existing helper assertions |
| Mem2var | `venom/passes/mem2var/proofs/mem2varBlockSimHelpersScript.sml` | Existing helper assertions |
| Source frames | `semantics/prop/vyperCreateFrameScript.sml` | Source creation frame consumers |

## Notes

Independent audit found the old unconditional CREATE-not-Abort assertions false. Malformed instruction outputs retain their old Error precedence. A successful `OK` CREATE result retains its old frame. This task establishes the missing parent-frame boundary and repairs its consumers; it must not assert complete constructor/oracle/assembly correctness beyond the existing contracts.

Owner amendment after the first run: argon approved CREATE/CREATE2 CanExHalt metadata and the additional same-hypothesis abort classification. The old singular classification is kernel-refuted by the retained witness; that exact old formula is no longer a requested result. The corrected metadata removes a false NoFail classification and preserves all commutation theorem statements. No stage assumption is added. New metadata definition and corrected ninth public contract are frozen above. Resume remaining proof consumers; retain checked earlier components.
