(*
 * Codegen End-to-End Correctness — Theorem Statements
 *
 * Composes venomToAsm and asmToBytecode to state: if Venom IR
 * execution halts/reverts, then EVM execution of the codegen output
 * (byte list) produces a corresponding result.
 *
 * TOP-LEVEL:
 *   codegen_correct    — planned S7 (run_context vs run_call/frame outcome)
 *   initial_ctx_rel, venom_frame_rel — exact initial/terminal frame interfaces
 *   TASK056: obsolete positioned codegen admission retired (inactive archive).
 *
 * codegen_correct composes codegenEntrySim$codegen_entry_asm_sim
 * (Venom to assembly) with codegenAsmRunCall$codegen_asm_run_call
 * (assembly to the EVM frame).  The entry relations are defined in
 * codegenEntryRel and re-exported here under their own names.
 *
 * MEMTOP Exclusion
 * ===============
 * MEMTOP correspondence is excluded: asm/EVM memory may be longer
 * than Venom memory due to spill slot expansion. Vyper never exposes
 * MEMTOP to user code (used internally for free memory pointer).
 * See memory_rel in codegenRelScript.sml.
 *
 * EVM Exception Classification
 * ============================
 * How each EVM exception is handled in the correctness argument:
 *
 * OutOfGas and StackOverflow — resource-starvation disjuncts of S7.
 *   No existential sufficient-gas bound or generated-stack bound is claimed.
 *
 * StackUnderflow — discharged by construction (codegen stack model
 *   tracks height; well-formed plans never underflow).
 *
 * InvalidJumpDest — discharged by construction (label_offset_consistent,
 *   assemble_parse_correct ensure all jump targets are valid JUMPDESTs).
 *
 * Reverted — handled explicitly (separate case in theorem conclusion).
 *
 * WriteInStaticContext — initial_ctx_rel excludes static entry frames.
 *   Venom does not demote writes to nops; no static-write simulation is claimed.
 *
 * OutOfBoundsRead — RETURNDATACOPY past returndata length. Should be
 *   discharged by construction: Venom ExHalt maps to this. The proof
 *   that Vyper lowering never generates OOB reads is a separate
 *   lowering correctness obligation. NOTE: if future Vyper versions
 *   expose raw returndata access to users, this may require a runtime
 *   bounds check instead.
 *
 * AddressCollision — CREATE-specific. Handled by a separate entry
 *   point (create_vyper_contract) that includes the collision check.
 *   TODO: define create_vyper_contract alongside call_vyper_contract.
 *
 * InvalidContractPrefix — CREATE code starts with 0xEF. Similar to
 *   AddressCollision: handled via create_vyper_contract.
 *
 * InvalidParameter, KZGProofError — precompile-internal failures.
 *   Contained within the CALL frame (returns 0 on stack). Never
 *   propagates to the calling contract's execution.
 *)

Theory codegenCorrectness
Ancestors
  codegenEntryRel codegenEntrySim codegenAsmRunCall
  asmToBytecodeProps venomToAsmProps codegen vfmExecution
  codegenRel asmSem asmWf stackPlanGen stackPlanTypes planExec
  symbolResolve venomExecSemantics venomState venomInst contextCodegenRel
  stackOpSim fnPlanDecomp list rich_list finite_map arithmetic
  frameOutcome callTrace unitShapeDefs vfmExecutionProp
Libs
  BasicProvers

(* ===== Context Correspondence Helpers ===== *)

Theorem msg_ctx_rel_def = codegenEntryRelTheory.msg_ctx_rel_def

Theorem tx_ctx_rel_def = codegenEntryRelTheory.tx_ctx_rel_def

Theorem block_ctx_rel_def = codegenEntryRelTheory.block_ctx_rel_def

Theorem blockhash_rel_def = codegenEntryRelTheory.blockhash_rel_def

Theorem stack_params_rel_def = codegenEntryRelTheory.stack_params_rel_def

(* ===== Initial State Correspondence ===== *)

Theorem initial_state_rel_def = codegenEntryRelTheory.initial_state_rel_def

Theorem initial_state_rel_entry_clauses[local]:
  ∀cp prog off fn vs es ctxt rb rest.
    initial_state_rel cp prog off fn vs es /\
    es.contexts = (ctxt, rb) :: rest ==>
    context_memory_rel cp vs.vs_memory (buffer_to_list ctxt.memory) /\
    ctxt.pc = asm_pc_to_offset prog off
Proof
  rpt strip_tac >> gvs[initial_state_rel_def]
QED

(* ===== Return Value Correspondence ===== *)

(* After execution: return data and side effects match. *)
Definition final_state_rel_def:
  final_state_rel vs es ⇔
    (case es.contexts of
       (ctxt, rb) :: _ =>
         ctxt.returnData = vs.vs_returndata ∧
         ctxt.logs = vs.vs_logs ∧
         es.rollback.accounts = vs.vs_accounts ∧
         es.rollback.tStorage = vs.vs_transient ∧
         es.rollback.toDelete = vs.vs_pending_deletions
     | [] => F)
End

(* entry_fn_no_ret is defined in contextCodegenRel so context-wide
   obligations and this correctness interface share one constant. *)

(* ===== Composition Helpers ===== *)

(* Terminal state composition: venom_asm_terminal_rel + asm_evm_rel → final_state_rel.
   After asm execution ends at a terminal, the asm state relates to both Venom (terminal_rel)
   and EVM (evm_rel). Composing these gives the end-to-end final_state_rel. *)
Theorem terminal_asm_evm_final[local]:
  !prog vs' as' es'.
    venom_asm_terminal_rel vs' as' /\
    asm_evm_rel prog as' es' ==>
    final_state_rel vs' es'
Proof
  rpt gen_tac >> strip_tac >>
  fs[venom_asm_terminal_rel_def, asm_evm_rel_def, final_state_rel_def] >>
  every_case_tac >> gvs[]
QED

(* The obsolete single-function codegen unfolding is intentionally absent:
   context codegen is exposed through [codegen_assembly] and the selected
   region is located by [ops_contain_at]. *)

(* Prefix of a list is an asm_block_at position 0 *)
Theorem asm_block_at_prefix[local]:
  !xs ys. asm_block_at (xs ++ ys) 0 xs
Proof
  Induct >> simp[asm_block_at_def, EL_APPEND1]
QED

(* Bridge from a positioned context-region entry to an assembly state. *)
Theorem initial_state_bridge[local]:
  ∀cp prog off fn vs es ctx i r unit lo.
    initial_state_rel cp prog off fn vs es /\
    generate_context_plan ctx = SOME cp /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\
    EL i cp.cp_regions = r /\
    ops_contain_at off
      (execute_plan cp.cp_initial_fmp (context_plan_ops cp))
      (execute_plan cp.cp_initial_fmp r.sr_plan) /\
    prog = execute_plan cp.cp_initial_fmp (context_plan_ops cp) ++
           data_segment_asm unit.cu_data_segment /\
    lo = SND (compute_label_offsets prog) /\
    (case es.contexts of
       (ctxt, rb) :: _ =>
         ctxt.msgParams.code = assemble prog /\
         ctxt.msgParams.parsed = parse_code 0 FEMPTY (assemble prog)
     | [] => F) ==>
    ∃as0.
      context_venom_asm_rel cp lo
        (fn_init_ps fn r.sr_spill_base) vs as0 /\
      asm_evm_rel prog as0 es /\
      asm_block_at prog off
        (execute_plan cp.cp_initial_fmp r.sr_plan) /\
      as0.as_pc = off
Proof
  rpt gen_tac >> strip_tac >>
  every_case_tac >> gvs[] >>
  rename1 `es.contexts = (ctxt, rb) :: rest` >>
  qexists_tac `<| as_stack := ctxt.stack;
                   as_memory := buffer_to_list ctxt.memory;
                   as_accounts := vs.vs_accounts;
                   as_transient := vs.vs_transient;
                   as_returndata := vs.vs_returndata;
                   as_logs := vs.vs_logs;
                   as_pc := off;
                   as_call_ctx := vs.vs_call_ctx;
                   as_tx_ctx := vs.vs_tx_ctx;
                   as_block_ctx := vs.vs_block_ctx;
                   as_code := vs.vs_code;
                   as_prev_hashes := vs.vs_prev_hashes;
                   as_outcomes := vs.vs_outcomes;
                   as_requests := vs.vs_requests;
                   as_pending_deletions := vs.vs_pending_deletions;
                   as_gas_readings := vs.vs_gas_readings |>` >>
  gvs[initial_state_rel_def, msg_ctx_rel_def, tx_ctx_rel_def,
      block_ctx_rel_def, blockhash_rel_def, stack_params_rel_def,
      context_venom_asm_rel_def, fn_init_ps_def,
      init_plan_state_def, init_spill_alloc_def, LET_THM,
      plan_spill_rel_def, FLOOKUP_DEF, asm_evm_rel_def] >>
  conj_tac >- suspend "plan_stack" >>
  conj_tac >- (rpt gen_tac >> simp[CONJ_ASSOC]) >>
  gvs[asm_block_at_def, ops_contain_at_def, EL_APPEND1]
QED

Resume initial_state_bridge[plan_stack]:
  simp[plan_stack_rel_def, operand_val_def] >>
  rpt strip_tac >>
  rename1 `j < LENGTH ctxt.stack` >>
  simp[EL_REVERSE, EL_MAP, operand_val_def, FLOOKUP_DEF] >>
  qpat_x_assum `!k. k < LENGTH ctxt.stack ==> _`
    (qspec_then `PRE (LENGTH ctxt.stack - j)` mp_tac) >>
  simp[EL_REVERSE] >>
  `PRE (LENGTH ctxt.stack - PRE (LENGTH ctxt.stack - j)) = j` by simp[] >>
  simp[]
QED

Finalise initial_state_bridge

(* run_blocks never returns OK — it always terminates with
   Halt/Abort/IntRet/Error. Induction on fuel: base returns Error,
   step either recurses (smaller fuel) or passes through non-OK. *)
Theorem run_blocks_never_ok[local]:
  !fuel ctx fn s vs1. run_blocks fuel ctx fn s <> OK vs1
Proof
  Induct >- simp[Once run_blocks_def] >>
  simp[Once run_blocks_unfold] >>
  rpt gen_tac >> every_case_tac
QED

(* run_function never returns OK — unfolds to run_blocks. *)
Theorem run_function_never_ok[local]:
  !fuel ctx fn vs vs1. run_function fuel ctx fn vs <> OK vs1
Proof
  simp[run_function_def] >>
  rpt gen_tac >> every_case_tac >> simp[run_blocks_never_ok]
QED

(* run_context also never returns OK — it either dispatches to
   run_function (which never returns OK) or returns Error. *)
Theorem run_context_never_ok[local]:
  !fuel ctx vs vs1. run_context fuel ctx vs <> OK vs1
Proof
  rpt gen_tac >> simp[Once run_context_def] >>
  every_case_tac >> simp[run_function_never_ok]
QED

(* ===== Whole-Context Frame Interface ===== *)

Theorem initial_codegen_state_rel_def = codegenEntryRelTheory.initial_codegen_state_rel_def

Theorem initial_ctx_rel_def = codegenEntryRelTheory.initial_ctx_rel_def

(* Terminal oracle leftovers are not observable. Only success compares the
   executed requests/effects/logs; each abort has its precise frame clause. *)
Definition venom_frame_rel_def:
  venom_frame_rel es r es' res <=>
    case res of
      Halt vs' =>
        frame_outcome es r es' NONE vs'.vs_returndata vs'.vs_logs /\
        es'.rollback.accounts = vs'.vs_accounts /\
        es'.rollback.toDelete = vs'.vs_pending_deletions /\
        es'.rollback.tStorage = vs'.vs_transient /\
        vs'.vs_requests = call_requests es
    | Abort Revert_abort vs' =>
        ?lgs. frame_outcome es r es' (SOME Reverted) vs'.vs_returndata lgs
    | Abort ExHalt_abort vs' =>
        ?exc lgs. exc <> Reverted /\ frame_outcome es r es' (SOME exc) [] lgs
    | Error _ => T
    | OK _ => F
    | IntRet _ _ => F
End

(* S7, proved from its two halves: the Venom-to-assembly simulation
   (codegenEntrySim) and the assembly-to-EVM frame run (codegenAsmRunCall).
   Compose frame-aware Venom/assembly simulation with the observed EVM run.
   Venom starts with the frame's GAS readings (gas_readings es); generated
   assembly pops the same list in the same order.
   Actual reachability supplies memory obligations and shape excludes opaque
   GAS misuse/forbidden opcodes/label collisions. Resource starvation is an
   explicit disjunct; a starved computed precompile is an oracle outcome. No sufficient-gas existential,
   arbitrary label maps, or positional entry parameter is in this API. *)
Theorem codegen_correct:
  !fuel rpolicy unit cp prog Inv vs es.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    initial_ctx_rel cp prog unit.cu_context vs es
    ==>
    ?r es'. run_call es = SOME (r, es') /\
            (frame_resource_starved es r es' \/
             venom_frame_rel es r es' (run_context fuel unit.cu_context vs))
Proof
  rpt strip_tac >>
  drule_all codegen_asm_run_call >> strip_tac >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `frame_resource_starved es r es'` >> gvs[] >>
  drule_all codegen_entry_asm_sim >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  simp[venom_frame_rel_def] >>
  Cases_on `run_context fuel unit.cu_context vs` >>
  gvs[run_context_never_ok]
  >- (res_tac >> gvs[venom_asm_terminal_rel_def]) >>
  rename1 `Abort a _` >> Cases_on `a` >>
  res_tac >> gvs[venom_asm_terminal_rel_def] >> metis_tac[]
QED

(* TASK056 RETIRED SOURCE ARCHIVE. Replaced by initial_ctx_rel and S7 above;
   no equivalence bridge. Original legacy admission/proof preserved verbatim.
(* ===== Preserved Legacy Contract (removal owner TASK056) ===== *)

(* Initial correspondence at the selected context-entry region.  [off] is
   an assembly-instruction index and the EVM PC is its byte offset. *)
(* TEMPORARY COMPATIBILITY: exact old boundary, removal owner TASK056.
   This saved-snapshot/positioned relation is NOT the new live-frame API. *)
Definition initial_ctx_rel_legacy_def:
  initial_ctx_rel_legacy cp prog off ctx vs es ⇔
    (case es.contexts of
       (ctxt, rb) :: _ =>
         rb.accounts = vs.vs_accounts ∧
         rb.tStorage = vs.vs_transient ∧
         ctxt.returnData = vs.vs_returndata ∧
         ctxt.logs = vs.vs_logs ∧
         ctxt.stack = [] ∧
         context_memory_rel cp vs.vs_memory (buffer_to_list ctxt.memory) ∧
         ctxt.pc = asm_pc_to_offset prog off
     | [] => F)
End

(* Conditional whole-context correctness for an explicitly positioned named
   entry function in a complete compilation unit. *)
(* EXISTING LEGACY ADMISSION: statement and proof retained exactly modulo
   the boundary rename. Old e2e proof consumers require it until TASK056;
   it is not a producer/alias of S7 and is NOT certified. *)
Theorem codegen_correct_legacy:
  ∀fuel rpolicy unit cp prog name i r fn off Inv vs.
    generate_context_plan unit.cu_context = SOME cp ∧
    codegen_assembly rpolicy unit = SOME prog ∧
    unit.cu_context.ctx_entry = SOME name ∧
    lookup_function name unit.cu_context.ctx_functions = SOME fn ∧
    i < LENGTH unit.cu_context.ctx_functions ∧
    EL i unit.cu_context.ctx_functions = fn ∧
    EL i cp.cp_regions = r ∧
    ops_contain_at off
      (execute_plan cp.cp_initial_fmp (context_plan_ops cp))
      (execute_plan cp.cp_initial_fmp r.sr_plan) ∧
    codegen_context_obligations Inv unit.cu_context cp ∧
    codegen_reachability_package Inv unit.cu_context vs ⇒
    ∃gas_needed.
      ∀es. initial_ctx_rel_legacy cp prog off unit.cu_context vs es ∧
           (case es.contexts of
              (ctxt, rb) :: _ =>
                ctxt.msgParams.gasLimit ≥ gas_needed ∧
                ctxt.msgParams.code = assemble prog ∧
                ctxt.msgParams.parsed = parse_code 0 FEMPTY (assemble prog)
            | [] => F) ⇒
        (case run_context fuel unit.cu_context vs of
           Halt vs' =>
             ∃es'. run es = SOME (INR NONE, es') ∧
                   final_state_rel vs' es'
         | Abort Revert_abort vs' =>
             ∃es'. run es = SOME (INR (SOME Reverted), es') ∧
                   final_state_rel vs' es'
         | Abort ExHalt_abort vs' =>
             ∃es' exc. run es = SOME (INR (SOME exc), es') ∧
                       exc ≠ Reverted ∧
                       final_state_rel vs' es'
         | OK _ => F
         | IntRet _ _ => F
         | Error _ => T)
Proof
  cheat
QED
*)
