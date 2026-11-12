(*
 * Codegen request prefix: the EVM frame's requests are a prefix of the
 * requests a Venom run records, including when the frame starves (runs out
 * of gas or overflows the stack).
 *
 * codegen_correct (codegenCorrectness) relates the requests only on Halt
 * and only for a frame that doesn't starve.  This companion holds for every
 * Halt or Abort run, with no starvation condition: the frame makes its
 * calls exactly as the generated assembly does up to the step where it
 * halts, aborts or starves, and makes none after it, while the assembly
 * may go on (and record more) after the frame starves.
 *
 * TOP-LEVEL:
 *   codegen_request_prefix - call_requests es is a prefix of Venom's
 * Helpers:
 *   asm_step_requests      - a step keeps or extends as_requests, and
 *                            keeps it on Halt, Revert and Fault
 *   asm_steps_requests     - a run's terminal requests extend its start's
 *   asm_frame_run_requests - against asm_frame_rel, call_requests es0 is a
 *                            prefix of the terminal requests
 *)
Theory codegenRequestPrefix
Ancestors
  codegenCorrectness codegenEntrySim codegenAsmProgOk codegenEntryRel
  codegenRel asmFrameRel asmFrameRun asmSem asmWf asmCallOracleProps
  extCallOracle callTrace
  list rich_list

(* ===== Assembly steps never drop a request ===== *)

Theorem asm_prim_requests[local]:
  MEM r [asm_binop f a; asm_unop g a; asm_ternop h a; asm_push_val w a;
         asm_pop a; asm_dup n a; asm_swap n a; asm_state_unop k a;
         asm_gas a] /\
  (r = AsmOK a1 \/ r = AsmHalt a1 \/ r = AsmRevert a1 \/ r = AsmFault a1) ==>
  a1.as_requests = a.as_requests
Proof
  simp[MEM] >> strip_tac >>
  gvs[asm_binop_def, asm_unop_def, asm_ternop_def, asm_push_val_def,
      asm_pop_def, asm_dup_def, asm_swap_def, asm_state_unop_def,
      asm_gas_def, asm_next_def, AllCaseEqs()]
QED

Theorem asm_mem_requests[local]:
  MEM r [asm_mload a; asm_mstore a; asm_mstore8 a; asm_sload a;
         asm_sstore a; asm_tload a; asm_tstore a; asm_jump pc a;
         asm_jumpi pc a; asm_return_op a; asm_revert_op a;
         asm_log n a; asm_sha3 a; asm_copy_to_mem bytes a;
         asm_returndatacopy a; asm_extcodecopy a; asm_mcopy a;
         asm_selfdestruct a] /\
  (r = AsmOK a1 \/ r = AsmHalt a1 \/ r = AsmRevert a1 \/ r = AsmFault a1) ==>
  a1.as_requests = a.as_requests
Proof
  simp[MEM] >> strip_tac >>
  gvs[asm_mload_def, asm_mstore_def, asm_mstore8_def, asm_sload_def,
      asm_sstore_def, asm_tload_def, asm_tstore_def, asm_jump_def,
      asm_jumpi_def, asm_return_op_def, asm_revert_op_def, asm_log_def,
      asm_sha3_def, asm_copy_to_mem_def, asm_returndatacopy_def,
      asm_extcodecopy_def, asm_mcopy_def, asm_selfdestruct_def,
      asm_expand_memory_def, asm_pop_def, asm_next_def, AllCaseEqs()]
QED

Theorem asm_consume_requests[local]:
  (asm_consume_call_outcome rq ro rs stk s = r ==>
   ?s1. r = AsmOK s1 /\ s1.as_requests = record_request rq s.as_requests) /\
  (asm_consume_create_outcome rq stk s = r ==>
   ?s1. r = AsmOK s1 /\ s1.as_requests = record_request rq s.as_requests)
Proof
  conj_tac >> strip_tac >> gvs[]
  >- simp[asm_consume_call_outcome_eq, asm_next_def] >>
  simp[asm_consume_create_outcome_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[asm_next_def]
QED

Theorem asm_ext_requests[local]:
  MEM r [asm_exec_call b a; asm_exec_staticcall a;
         asm_exec_delegatecall a; asm_exec_create a; asm_exec_create2 a] ==>
  (r = AsmOK a1 ==> a.as_requests <<= a1.as_requests) /\
  (r = AsmHalt a1 \/ r = AsmRevert a1 \/ r = AsmFault a1 ==>
   a1.as_requests = a.as_requests)
Proof
  simp[MEM] >> rw[] >>
  gvs[asm_exec_call_def, asm_exec_staticcall_def,
      asm_exec_delegatecall_def, asm_exec_create_def, asm_exec_create2_def,
      AllCaseEqs()] >>
  imp_res_tac asm_consume_requests >> gvs[record_request_def] >> rw[]
QED

(* One instance per list element of a lemma whose first premise is
   [MEM x [e1; ...; en]], with [x] a variable, ready for [imp_res_tac]. *)
fun mem_instances th =
  let
    val th = SPEC_ALL th
    val ant = fst (dest_imp (concl th))
    val memtm = if is_conj ant then fst (dest_conj ant) else ant
    val (x, l) = listSyntax.dest_mem memtm
  in
    map (fn e => GEN_ALL (SIMP_RULE (srw_ss()) [] (INST [x |-> e] th)))
        (fst (listSyntax.dest_list l))
  end

val prim_reqs = mem_instances asm_prim_requests @
                mem_instances asm_mem_requests @
                mem_instances asm_ext_requests

Theorem asm_class_requests[local]:
  MEM c [asm_step_arith name a; asm_step_compare name a;
    asm_step_bitwise name a; asm_step_memory name a;
    asm_step_control pc name a; asm_step_extcall name a;
    asm_step_copy name a; asm_step_context name a] ==>
  (c = SOME (AsmOK a1) ==> a.as_requests <<= a1.as_requests) /\
  (c = SOME (AsmHalt a1) \/ c = SOME (AsmRevert a1) \/
   c = SOME (AsmFault a1) ==>
   a1.as_requests = a.as_requests)
Proof
  simp[MEM] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (rpt strip_tac >> gvs[asm_step_arith_def, AllCaseEqs()] >>
      MAP_EVERY imp_res_tac prim_reqs >> gvs[])
  >- (rpt strip_tac >> gvs[asm_step_compare_def, AllCaseEqs()] >>
      MAP_EVERY imp_res_tac prim_reqs >> gvs[])
  >- (rpt strip_tac >> gvs[asm_step_bitwise_def, AllCaseEqs()] >>
      MAP_EVERY imp_res_tac prim_reqs >> gvs[])
  >- (rpt strip_tac >> gvs[asm_step_memory_def, AllCaseEqs()] >>
      MAP_EVERY imp_res_tac prim_reqs >> gvs[])
  >- (rpt strip_tac >> gvs[asm_step_control_def, asm_next_def, AllCaseEqs()] >>
      MAP_EVERY imp_res_tac prim_reqs >> gvs[])
  >- (rpt strip_tac >> gvs[asm_step_extcall_def, AllCaseEqs()] >>
      MAP_EVERY imp_res_tac prim_reqs >> gvs[])
  >- (rpt strip_tac >> gvs[asm_step_copy_def, AllCaseEqs()] >>
      MAP_EVERY imp_res_tac prim_reqs >> gvs[])
  >> (rpt strip_tac >> pop_assum mp_tac >>
      pure_rewrite_tac[asm_step_context_def] >>
      rpt IF_CASES_TAC >> simp[] >> strip_tac >>
      MAP_EVERY imp_res_tac prim_reqs >> gvs[])
QED

val class_reqs = mem_instances asm_class_requests

Theorem asm_step_requests:
  (asm_step lo o2pc inst a = AsmOK a1 ==> a.as_requests <<= a1.as_requests) /\
  (asm_step lo o2pc inst a = AsmHalt a1 \/
   asm_step lo o2pc inst a = AsmRevert a1 \/
   asm_step lo o2pc inst a = AsmFault a1 ==>
   a1.as_requests = a.as_requests)
Proof
  Cases_on `inst` >> simp[asm_step_def] >>
  TRY (simp[asm_next_def, AllCaseEqs()] >> rw[] >> simp[] >> NO_TAC) >>
  simp[asm_step_op_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  MAP_EVERY imp_res_tac (class_reqs @ prim_reqs) >> gvs[]
QED

Theorem asm_steps_requests:
  !n a a1.
    asm_steps lo o2pc prog n a = AsmOK a1 \/
    asm_steps lo o2pc prog n a = AsmHalt a1 \/
    asm_steps lo o2pc prog n a = AsmRevert a1 \/
    asm_steps lo o2pc prog n a = AsmFault a1 ==>
    a.as_requests <<= a1.as_requests
Proof
  Induct >> simp[asm_steps_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `asm_step lo o2pc (EL a.as_pc prog) a` >> simp[] >>
  metis_tac[asm_step_requests, isPREFIX_TRANS, isPREFIX_REFL]
QED

(* ===== Against the frame ===== *)

(* The run's terminal requests equal the frame's when the run halts,
   reverts or faults while the relation holds, and extend them when the
   frame starves (it makes no request from the starving step on; the
   assembly goes on alone). *)
Theorem asm_frame_run_requests:
  !n prog data es0 a es a1.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
    (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n a = AsmHalt a1 \/
     asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n a = AsmRevert a1 \/
     asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n a = AsmFault a1) ==>
    call_requests es0 <<= a1.as_requests
Proof
  Induct >- simp[asm_steps_def] >>
  rpt gen_tac >> rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 2 strip_tac >>
  disch_tac >>
  (reverse (Cases_on `a.as_pc < LENGTH prog`) >- gvs[asm_steps_def]) >>
  Cases_on `is_data_inst (EL a.as_pc prog)`
  >- (Cases_on `EL a.as_pc prog` >>
      gvs[is_data_inst_def, asm_step_def, asm_steps_def]) >>
  `a.as_requests ++ call_requests es = call_requests es0` by
    gvs[asm_frame_rel_def] >>
  `asm_frame_step_ok prog data es0 a es` by (irule asm_frame_step >> simp[]) >>
  pop_assum mp_tac >> simp[asm_frame_step_ok_def] >> strip_tac
  >- (gvs[] >> metis_tac[asm_steps_requests]) >>
  Cases_on `asm_step (SND (compute_label_offsets prog))
              (build_offset_to_pc prog) (EL a.as_pc prog) a` >>
  gvs[asm_steps_def]
  >>~- ([`asm_step _ _ _ _ = AsmOK _`], metis_tac[])
  >>~- ([`asm_step _ _ _ _ = AsmHalt _`], simp[]) >>
  imp_res_tac (GEN_ALL asm_step_requests) >> gvs[]
QED

(* ===== Venom against the frame ===== *)

(* Same hypotheses as codegen_correct; no starvation condition.  The
   requests are equal on a Halt or Abort the frame matches, and the frame's
   are a proper prefix only when the frame starves (Venom keeps running on
   failed outcomes past the frame's starving step). *)
Theorem codegen_request_prefix:
  !fuel rpolicy unit cp prog Inv vs es vs'.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    initial_ctx_rel cp prog unit.cu_context vs es /\
    (run_context fuel unit.cu_context vs = Halt vs' \/
     ?a. run_context fuel unit.cu_context vs = Abort a vs') ==>
    call_requests es <<= vs'.vs_requests
Proof
  rpt gen_tac >> strip_tac >>
  drule_all codegen_assembly_frame_prog_ok >> strip_tac >>
  `assemble prog <> []` by metis_tac[codegen_assembly_nonempty] >>
  (Q.SUBGOAL_THEN `vs.vs_call_ctx.cc_created_in_tx \/ account_already_created
     (lookup_account (FST (HD es.contexts)).msgParams.callee
       es.rollback.accounts)` assume_tac
   >- (gvs[initial_ctx_rel_def] >> metis_tac[])) >>
  drule_all asm_frame_rel_entry >> strip_tac >>
  drule_all codegen_entry_asm_sim >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  gvs[] >> res_tac >> gvs[venom_asm_terminal_rel_def] >>
  qspecl_then [`n`, `prog`, `vs.vs_data_section`, `es`, `entry_asm_state vs es`,
               `es`, `as'`] mp_tac asm_frame_run_requests >>
  simp[]
QED
