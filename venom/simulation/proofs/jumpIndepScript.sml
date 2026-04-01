(*
 * step_inst_base is independent of vs_prev_bb, vs_current_bb, vs_inst_idx
 * for non-pseudo non-terminator opcodes.
 *
 * PHI reads vs_prev_bb, so it's excluded (is_pseudo).
 * Terminators write vs_prev_bb/vs_current_bb/vs_inst_idx (via jump_to), so excluded.
 * All other opcodes never read or write these three fields.
 *
 * Built as a separate theory because the opcode case split is expensive.
 *
 * TOP-LEVEL:
 *   step_inst_base_jump_indep — main commutation theorem
 *)

Theory jumpIndep
Ancestors
  instIdxIndep venomExecSemantics venomState venomInst
Libs
  finite_mapTheory listTheory BasicProvers pairTheory

(* Abbreviation for the 3-field update *)
val jmp = ``\s:venom_state. s with <|vs_prev_bb := pb;
                                      vs_current_bb := cb;
                                      vs_inst_idx := idx|>``;

(* ================================================================
   Basic commutation helpers — all local
   ================================================================ *)

Theorem eval_op_jump[local]:
  !op s pb cb idx.
    eval_operand op (s with <|vs_prev_bb := pb;
                               vs_current_bb := cb;
                               vs_inst_idx := idx|>) =
    eval_operand op s
Proof Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_ops_jump[local]:
  !ops s pb cb idx.
    eval_operands ops (s with <|vs_prev_bb := pb;
                                 vs_current_bb := cb;
                                 vs_inst_idx := idx|>) =
    eval_operands ops s
Proof Induct >> simp[eval_operands_def, eval_op_jump]
QED

Theorem update_var_jump[local]:
  !x v s pb cb idx.
    update_var x v (s with <|vs_prev_bb := pb;
                              vs_current_bb := cb;
                              vs_inst_idx := idx|>) =
    (update_var x v s) with <|vs_prev_bb := pb;
                               vs_current_bb := cb;
                               vs_inst_idx := idx|>
Proof simp[update_var_def]
QED

Theorem write_mem_jump[local]:
  !off bytes s pb cb idx.
    write_memory_with_expansion off bytes
      (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                vs_inst_idx := idx|>) =
    (write_memory_with_expansion off bytes s) with
      <|vs_prev_bb := pb; vs_current_bb := cb; vs_inst_idx := idx|>
Proof simp[write_memory_with_expansion_def, LET_THM]
QED

Theorem read_mem_jump[local]:
  !off sz s pb cb idx.
    read_memory off sz (s with <|vs_prev_bb := pb;
                                  vs_current_bb := cb;
                                  vs_inst_idx := idx|>) =
    read_memory off sz s
Proof simp[read_memory_def]
QED

Theorem halt_state_jump[local]:
  !s pb cb idx.
    halt_state (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                          vs_inst_idx := idx|>) =
    (halt_state s) with <|vs_prev_bb := pb; vs_current_bb := cb;
                           vs_inst_idx := idx|>
Proof simp[halt_state_def]
QED

Theorem revert_state_jump[local]:
  !s pb cb idx.
    revert_state (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                            vs_inst_idx := idx|>) =
    (revert_state s) with <|vs_prev_bb := pb; vs_current_bb := cb;
                             vs_inst_idx := idx|>
Proof simp[revert_state_def]
QED

Theorem set_returndata_jump[local]:
  !rd s pb cb idx.
    set_returndata rd (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                                vs_inst_idx := idx|>) =
    (set_returndata rd s) with <|vs_prev_bb := pb; vs_current_bb := cb;
                                  vs_inst_idx := idx|>
Proof simp[set_returndata_def]
QED

Theorem mstore_jump[local]:
  !off v s pb cb idx.
    mstore off v (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                            vs_inst_idx := idx|>) =
    (mstore off v s) with <|vs_prev_bb := pb; vs_current_bb := cb;
                             vs_inst_idx := idx|>
Proof simp[mstore_def, LET_THM]
QED

Theorem mstore8_jump[local]:
  !off v s pb cb idx.
    mstore8 off v (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                             vs_inst_idx := idx|>) =
    (mstore8 off v s) with <|vs_prev_bb := pb; vs_current_bb := cb;
                              vs_inst_idx := idx|>
Proof simp[mstore8_def, LET_THM]
QED

Theorem sstore_jump[local]:
  !k v s pb cb idx.
    sstore k v (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                          vs_inst_idx := idx|>) =
    (sstore k v s) with <|vs_prev_bb := pb; vs_current_bb := cb;
                           vs_inst_idx := idx|>
Proof simp[sstore_def, contract_storage_def, LET_THM]
QED

Theorem tstore_jump[local]:
  !k v s pb cb idx.
    tstore k v (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                          vs_inst_idx := idx|>) =
    (tstore k v s) with <|vs_prev_bb := pb; vs_current_bb := cb;
                           vs_inst_idx := idx|>
Proof simp[tstore_def, contract_transient_def, LET_THM]
QED

Theorem mcopy_jump[local]:
  !dst src sz s pb cb idx.
    mcopy dst src sz (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                                vs_inst_idx := idx|>) =
    (mcopy dst src sz s) with <|vs_prev_bb := pb; vs_current_bb := cb;
                                 vs_inst_idx := idx|>
Proof simp[mcopy_def, LET_THM, write_memory_with_expansion_def]
QED

Theorem mload_jump[local]:
  !off s pb cb idx.
    mload off (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                         vs_inst_idx := idx|>) = mload off s
Proof simp[mload_def]
QED

Theorem sload_jump[local]:
  !k s pb cb idx.
    sload k (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                       vs_inst_idx := idx|>) = sload k s
Proof simp[sload_def, contract_storage_def]
QED

Theorem tload_jump[local]:
  !k s pb cb idx.
    tload k (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                       vs_inst_idx := idx|>) = tload k s
Proof simp[tload_def, contract_transient_def]
QED

(* ================================================================
   exec_pure/read/write helpers — all local
   ================================================================ *)

val jmp_rw = [eval_op_jump, eval_ops_jump, update_var_jump,
              write_mem_jump, read_mem_jump,
              halt_state_jump, revert_state_jump, set_returndata_jump,
              mstore_jump, mstore8_jump, sstore_jump, tstore_jump, mcopy_jump,
              mload_jump, sload_jump, tload_jump,
              instIdxIndepTheory.exec_result_map_def];

Theorem exec_pure1_jump[local]:
  !f inst s pb cb idx.
    exec_pure1 f inst (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                                 vs_inst_idx := idx|>) =
    exec_result_map
      (\s'. s' with <|vs_prev_bb := pb; vs_current_bb := cb;
                       vs_inst_idx := idx|>)
      (exec_pure1 f inst s)
Proof
  rpt gen_tac >>
  simp[exec_pure1_def, eval_op_jump, update_var_jump,
       instIdxIndepTheory.exec_result_map_def] >>
  EVERY_CASE_TAC >> simp[instIdxIndepTheory.exec_result_map_def]
QED

Theorem exec_pure2_jump[local]:
  !f inst s pb cb idx.
    exec_pure2 f inst (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                                 vs_inst_idx := idx|>) =
    exec_result_map
      (\s'. s' with <|vs_prev_bb := pb; vs_current_bb := cb;
                       vs_inst_idx := idx|>)
      (exec_pure2 f inst s)
Proof
  rpt gen_tac >>
  simp[exec_pure2_def, eval_op_jump, update_var_jump,
       instIdxIndepTheory.exec_result_map_def] >>
  EVERY_CASE_TAC >> simp[instIdxIndepTheory.exec_result_map_def]
QED

Theorem exec_pure3_jump[local]:
  !f inst s pb cb idx.
    exec_pure3 f inst (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                                 vs_inst_idx := idx|>) =
    exec_result_map
      (\s'. s' with <|vs_prev_bb := pb; vs_current_bb := cb;
                       vs_inst_idx := idx|>)
      (exec_pure3 f inst s)
Proof
  rpt gen_tac >>
  simp[exec_pure3_def, eval_op_jump, update_var_jump,
       instIdxIndepTheory.exec_result_map_def] >>
  EVERY_CASE_TAC >> simp[instIdxIndepTheory.exec_result_map_def]
QED

Theorem exec_read0_jump[local]:
  !g inst s pb cb idx.
    (!s pb cb idx. g (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                                vs_inst_idx := idx|>) = g s) ==>
    exec_read0 g inst (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                                 vs_inst_idx := idx|>) =
    exec_result_map
      (\s'. s' with <|vs_prev_bb := pb; vs_current_bb := cb;
                       vs_inst_idx := idx|>)
      (exec_read0 g inst s)
Proof
  rpt strip_tac >>
  simp[exec_read0_def, update_var_jump,
       instIdxIndepTheory.exec_result_map_def] >>
  EVERY_CASE_TAC >> simp[instIdxIndepTheory.exec_result_map_def]
QED

Theorem exec_read1_jump[local]:
  !g inst s pb cb idx.
    (!v s pb cb idx. g v (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                                    vs_inst_idx := idx|>) = g v s) ==>
    exec_read1 g inst (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                                 vs_inst_idx := idx|>) =
    exec_result_map
      (\s'. s' with <|vs_prev_bb := pb; vs_current_bb := cb;
                       vs_inst_idx := idx|>)
      (exec_read1 g inst s)
Proof
  rpt strip_tac >>
  simp[exec_read1_def, eval_op_jump, update_var_jump,
       instIdxIndepTheory.exec_result_map_def] >>
  EVERY_CASE_TAC >> simp[instIdxIndepTheory.exec_result_map_def]
QED

Theorem exec_write2_jump[local]:
  !f inst s pb cb idx.
    (!v1 v2 s pb cb idx.
       f v1 v2 (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                          vs_inst_idx := idx|>) =
       (f v1 v2 s) with <|vs_prev_bb := pb; vs_current_bb := cb;
                           vs_inst_idx := idx|>) ==>
    exec_write2 f inst (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                                  vs_inst_idx := idx|>) =
    exec_result_map
      (\s'. s' with <|vs_prev_bb := pb; vs_current_bb := cb;
                       vs_inst_idx := idx|>)
      (exec_write2 f inst s)
Proof
  rpt strip_tac >>
  simp[exec_write2_def, eval_op_jump,
       instIdxIndepTheory.exec_result_map_def] >>
  EVERY_CASE_TAC >> simp[instIdxIndepTheory.exec_result_map_def]
QED

(* ================================================================
   Allocation helper — local
   ================================================================ *)

Theorem exec_alloca_jump[local]:
  !inst s alloc_size pb cb idx.
    exec_alloca inst (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                                vs_inst_idx := idx|>) alloc_size =
    exec_result_map
      (\s'. s' with <|vs_prev_bb := pb; vs_current_bb := cb;
                       vs_inst_idx := idx|>)
      (exec_alloca inst s alloc_size)
Proof
  rpt gen_tac >> simp[exec_alloca_def, next_alloca_offset_def, LET_THM] >>
  EVERY_CASE_TAC >> simp[instIdxIndepTheory.exec_result_map_def] >>
  simp[update_var_def, venom_state_component_equality]
QED

(* ================================================================
   External call sub-helpers — local
   ================================================================ *)

Theorem venom_to_tx_params_jump[local]:
  !s pb cb idx.
    venom_to_tx_params (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                                  vs_inst_idx := idx|>) =
    venom_to_tx_params s
Proof simp[venom_to_tx_params_def]
QED

Theorem make_venom_call_state_jump[local]:
  !s target gas value calldata code is_static pb cb idx.
    make_venom_call_state (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                                     vs_inst_idx := idx|>)
      target gas value calldata code is_static =
    make_venom_call_state s target gas value calldata code is_static
Proof
  simp[make_venom_call_state_def, LET_THM, venom_to_tx_params_jump]
QED

Theorem make_venom_delegatecall_state_jump[local]:
  !s target gas calldata code is_static pb cb idx.
    make_venom_delegatecall_state
      (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                vs_inst_idx := idx|>)
      target gas calldata code is_static =
    make_venom_delegatecall_state s target gas calldata code is_static
Proof
  simp[make_venom_delegatecall_state_def, LET_THM, venom_to_tx_params_jump]
QED

Theorem make_venom_create_state_jump[local]:
  !s new_address gas value init_code pb cb idx.
    make_venom_create_state
      (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                vs_inst_idx := idx|>)
      new_address gas value init_code =
    make_venom_create_state s new_address gas value init_code
Proof
  simp[make_venom_create_state_def, LET_THM, venom_to_tx_params_jump]
QED

(* Utility: case-OPTION_MAP fusion *)
Theorem option_case_OPTION_MAP[local]:
  !f x n g.
    option_CASE (OPTION_MAP f x) n g = option_CASE x n (g o f)
Proof Cases_on `x` >> simp[]
QED

Theorem extract_venom_result_jump[local]:
  !s output_val retOff retSize run_result pb cb idx.
    extract_venom_result
      (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                vs_inst_idx := idx|>)
      output_val retOff retSize run_result =
    OPTION_MAP (\p. (FST p,
                     (SND p) with <|vs_prev_bb := pb; vs_current_bb := cb;
                                     vs_inst_idx := idx|>))
      (extract_venom_result s output_val retOff retSize run_result)
Proof
  rpt gen_tac >> simp[extract_venom_result_def, LET_THM] >>
  Cases_on `run_result` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `x1.contexts` >> simp[] >>
  Cases_on `h` >> Cases_on `t` >> simp[] >>
  Cases_on `x0` >>
  simp[write_memory_with_expansion_def, LET_THM,
       venom_state_component_equality] >>
  Cases_on `y` >>
  simp[write_memory_with_expansion_def, LET_THM,
       venom_state_component_equality]
QED

(* ================================================================
   exec_ext_call / exec_delegatecall / exec_create — local
   ================================================================ *)

val ext_call_rw =
  [LET_THM, read_mem_jump, extract_venom_result_jump,
   option_case_OPTION_MAP, update_var_jump];

Theorem exec_ext_call_jump[local]:
  !inst s gas addr value ao as_ ro rs is_static pb cb idx.
    exec_ext_call inst
      (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                vs_inst_idx := idx|>)
      gas addr value ao as_ ro rs is_static =
    exec_result_map
      (\s'. s' with <|vs_prev_bb := pb; vs_current_bb := cb;
                       vs_inst_idx := idx|>)
      (exec_ext_call inst s gas addr value ao as_ ro rs is_static)
Proof
  rpt gen_tac >>
  simp([exec_ext_call_def, make_venom_call_state_jump] @ ext_call_rw) >>
  EVERY_CASE_TAC >>
  simp[instIdxIndepTheory.exec_result_map_def, update_var_jump,
       venom_state_component_equality]
QED

Theorem exec_delegatecall_jump[local]:
  !inst s gas addr ao as_ ro rs pb cb idx.
    exec_delegatecall inst
      (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                vs_inst_idx := idx|>)
      gas addr ao as_ ro rs =
    exec_result_map
      (\s'. s' with <|vs_prev_bb := pb; vs_current_bb := cb;
                       vs_inst_idx := idx|>)
      (exec_delegatecall inst s gas addr ao as_ ro rs)
Proof
  rpt gen_tac >>
  simp([exec_delegatecall_def, make_venom_delegatecall_state_jump]
       @ ext_call_rw) >>
  EVERY_CASE_TAC >>
  simp[instIdxIndepTheory.exec_result_map_def, update_var_jump,
       venom_state_component_equality]
QED

Theorem exec_create_jump[local]:
  !inst s value offset sz salt_opt pb cb idx.
    exec_create inst
      (s with <|vs_prev_bb := pb; vs_current_bb := cb;
                vs_inst_idx := idx|>)
      value offset sz salt_opt =
    exec_result_map
      (\s'. s' with <|vs_prev_bb := pb; vs_current_bb := cb;
                       vs_inst_idx := idx|>)
      (exec_create inst s value offset sz salt_opt)
Proof
  rpt gen_tac >>
  simp([exec_create_def, make_venom_create_state_jump] @ ext_call_rw) >>
  Cases_on `salt_opt` >> simp[] >>
  EVERY_CASE_TAC >>
  simp[instIdxIndepTheory.exec_result_map_def, update_var_jump,
       venom_state_component_equality]
QED

(* ================================================================
   THE MAIN THEOREM — exported

   For non-pseudo, non-terminator opcodes, step_inst_base commutes
   with the 3-field update (vs_prev_bb, vs_current_bb, vs_inst_idx).
   ================================================================ *)

Theorem step_inst_base_jump_indep:
  !inst s pb cb idx.
    ~is_pseudo inst.inst_opcode /\
    ~is_terminator inst.inst_opcode ==>
    step_inst_base inst (s with <|vs_prev_bb := pb;
                                   vs_current_bb := cb;
                                   vs_inst_idx := idx|>) =
    exec_result_map
      (\s'. s' with <|vs_prev_bb := pb; vs_current_bb := cb;
                       vs_inst_idx := idx|>)
      (step_inst_base inst s)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[is_pseudo_def, is_terminator_def] >>
  simp[step_inst_base_def, exec_pure1_jump, exec_pure2_jump,
       exec_pure3_jump, exec_alloca_jump] >>
  TRY (irule exec_read0_jump >> simp jmp_rw >> NO_TAC) >>
  TRY (irule exec_read1_jump >> simp jmp_rw >> NO_TAC) >>
  TRY (irule exec_write2_jump >> simp jmp_rw >> NO_TAC) >>
  simp[eval_op_jump, eval_ops_jump,
       exec_ext_call_jump, exec_delegatecall_jump, exec_create_jump] >>
  EVERY_CASE_TAC >>
  simp(jmp_rw @ [venom_state_component_equality])
QED

