(*
 * Steps without memory effects through the frame view.
 *
 * TOP-LEVEL:
 *   nonmemory_step_frame_view — a step of any opcode other than ASSIGN,
 *                               memory accesses, calls, INVOKE and PARAM
 *                               commutes with the frame view
 *)

Theory frameViewScalar
Ancestors
  frameViewFacts frameRel venomExecSemantics venomState venomInst
  unitShapeDefs stackPlanGen contextCodegenRel codegenRel list

Theorem exec_pure1_frame_view:
  (!x. MEM (Var x) inst.inst_operands ==> ~retpc_var fn x) /\
  (!x. MEM x inst.inst_outputs ==> ~retpc_var fn x) /\
  exec_pure1 f inst s = OK s' ==>
  exec_pure1 f inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory
Proof
  simp[exec_pure1_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `eval_operand op s = SOME v` >>
  `eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (irule eval_operand_frame_view >> metis_tac[]) >>
  simp[frame_view_update_var, update_var_def, frame_view_def]
QED

Theorem exec_pure2_frame_view:
  (!x. MEM (Var x) inst.inst_operands ==> ~retpc_var fn x) /\
  (!x. MEM x inst.inst_outputs ==> ~retpc_var fn x) /\
  exec_pure2 f inst s = OK s' ==>
  exec_pure2 f inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory
Proof
  simp[exec_pure2_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `eval_operand op1 s = SOME v1` >>
  rename1 `eval_operand op2 s = SOME v2` >>
  `eval_operand op1 (frame_view fn ra s with vs_memory := m) = eval_operand op1 s`
    by (irule eval_operand_frame_view >> metis_tac[]) >>
  `eval_operand op2 (frame_view fn ra s with vs_memory := m) = eval_operand op2 s`
    by (irule eval_operand_frame_view >> metis_tac[]) >>
  simp[frame_view_update_var, update_var_def, frame_view_def]
QED

Theorem exec_pure3_frame_view:
  (!x. MEM (Var x) inst.inst_operands ==> ~retpc_var fn x) /\
  (!x. MEM x inst.inst_outputs ==> ~retpc_var fn x) /\
  exec_pure3 f inst s = OK s' ==>
  exec_pure3 f inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
     eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> metis_tac[]) >>
  qpat_x_assum `exec_pure3 f inst s = OK s'` mp_tac >>
  simp[exec_pure3_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[frame_view_update_var, update_var_def, frame_view_def]
QED

Theorem exec_read0_frame_view:
  (!x. MEM x inst.inst_outputs ==> ~retpc_var fn x) /\
  f (frame_view fn ra s with vs_memory := m) = f s /\
  exec_read0 f inst s = OK s' ==>
  exec_read0 f inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory
Proof
  simp[exec_read0_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[frame_view_update_var, update_var_def, frame_view_def]
QED

Theorem exec_read1_frame_view:
  (!x. MEM (Var x) inst.inst_operands ==> ~retpc_var fn x) /\
  (!x. MEM x inst.inst_outputs ==> ~retpc_var fn x) /\
  (!v. f v (frame_view fn ra s with vs_memory := m) = f v s) /\
  exec_read1 f inst s = OK s' ==>
  exec_read1 f inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
     eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> metis_tac[]) >>
  qpat_x_assum `exec_read1 f inst s = OK s'` mp_tac >>
  simp[exec_read1_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[frame_view_update_var, update_var_def, frame_view_def]
QED

Theorem exec_write2_frame_view:
  (!x. MEM (Var x) inst.inst_operands ==> ~retpc_var fn x) /\
  (!v w. f v w (frame_view fn ra s with vs_memory := m) =
          (frame_view fn ra (f v w s) with vs_memory := m)) /\
  (!v w. (f v w s).vs_memory = s.vs_memory) /\
  exec_write2 f inst s = OK s' ==>
  exec_write2 f inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
     eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> metis_tac[]) >>
  qpat_x_assum `exec_write2 f inst s = OK s'` mp_tac >>
  simp[exec_write2_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED


val opcode_equations = CONJUNCTS step_inst_base_opcode_eqs;
fun opcode_equation opc =
  valOf (List.find
    (fn th => aconv (rhs (fst (dest_imp (snd (strip_forall (concl th)))))) opc)
    opcode_equations);

Theorem scalar_base_frame_view:
  ssa_form fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode
    [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR;
     SIGNEXTEND; BYTE; OFFSET] /\ step_inst_base inst s = OK s' ==>
  step_inst_base inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `!x. MEM (Var x) inst.inst_operands ==> ~retpc_var fn x` by
    (gen_tac >> disch_tac >> irule ordinary_operand_not_retpc >>
     simp[] >> qexists_tac `inst` >> gvs[]) >>
  `!x. MEM x inst.inst_outputs ==> ~retpc_var fn x` by
    (gen_tac >> disch_tac >> irule noncopy_output_not_retpc >>
     simp[] >> qexists_tac `inst` >> gvs[]) >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_assum `inst.inst_opcode = _`
    (fn th => fs[opcode_equation (rhs (concl th))]) >>
  FIRST [irule exec_pure1_frame_view, irule exec_pure2_frame_view,
         irule exec_pure3_frame_view] >> simp[]
QED

Theorem environment_base_frame_view:
  ssa_form fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode
    [SLOAD; TLOAD; CALLER; ADDRESS; CALLVALUE; GAS; ORIGIN; GASPRICE;
     CHAINID; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
     BLOBBASEFEE; BLOCKHASH; BLOBHASH; BALANCE; SELFBALANCE; CALLDATASIZE;
     CALLDATALOAD; RETURNDATASIZE; CODESIZE; EXTCODESIZE; EXTCODEHASH] /\
  step_inst_base inst s = OK s' ==>
  step_inst_base inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `!x. MEM (Var x) inst.inst_operands ==> ~retpc_var fn x` by
    (gen_tac >> disch_tac >> irule ordinary_operand_not_retpc >>
     simp[] >> qexists_tac `inst` >> gvs[]) >>
  `!x. MEM x inst.inst_outputs ==> ~retpc_var fn x` by
    (gen_tac >> disch_tac >> irule noncopy_output_not_retpc >>
     simp[] >> qexists_tac `inst` >> gvs[]) >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_assum `inst.inst_opcode = _`
    (fn th => fs[opcode_equation (rhs (concl th))]) >>
  FIRST [irule exec_read0_frame_view, irule exec_read1_frame_view] >>
  simp[frame_view_def, sload_def, tload_def, contract_storage_def,
       contract_transient_def]
QED

Theorem storage_base_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [SSTORE; TSTORE] /\ step_inst_base inst s = OK s' ==>
  step_inst_base inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `!x. MEM (Var x) inst.inst_operands ==> ~retpc_var fn x` by
    (gen_tac >> disch_tac >> irule ordinary_operand_not_retpc >>
     simp[] >> qexists_tac `inst` >> gvs[]) >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_assum `inst.inst_opcode = _`
    (fn th => fs[opcode_equation (rhs (concl th))]) >>
  irule exec_write2_frame_view >>
  simp[frame_view_def, sstore_def, tstore_def]
QED

Theorem control_base_frame_view:
  ssa_form fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode
    [NOP; JMP; JNZ; DJMP; ASSERT; ASSERT_UNREACHABLE; INITIAL_FMP; BUMP] /\
  step_inst_base inst s = OK s' ==>
  step_inst_base inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `!x. MEM (Var x) inst.inst_operands ==> ~retpc_var fn x` by
    (gen_tac >> disch_tac >> irule ordinary_operand_not_retpc >>
     simp[] >> qexists_tac `inst` >> gvs[]) >>
  `!x. MEM x inst.inst_outputs ==> ~retpc_var fn x` by
    (gen_tac >> disch_tac >> irule noncopy_output_not_retpc >>
     simp[] >> qexists_tac `inst` >> gvs[]) >>
  `!op. MEM op inst.inst_operands ==>
     eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> metis_tac[]) >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_assum `inst.inst_opcode = _`
    (fn th => fs[opcode_equation (rhs (concl th))]) >>
  gvs[AllCaseEqs()] >>
  simp[frame_view_update_var, update_var_def, jump_to_def, frame_view_def]
QED

Theorem terminal_base_not_ok:
  MEM inst.inst_opcode
    [RET; RETFMP; DRET; STOP; RETURN; REVERT; SINK; SELFDESTRUCT; INVALID; PHI] ==>
  step_inst_base inst s <> OK s'
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_assum `inst.inst_opcode = _`
    (fn th => simp[opcode_equation (rhs (concl th))]) >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  pairarg_tac >> gvs[]
QED

Theorem nonmemory_base_frame_view:
  codegen_ready_fn fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> INVOKE /\ ~is_param_opcode inst.inst_opcode /\
  ~MEM inst.inst_opcode
    [ASSIGN; MLOAD; ILOAD; SHA3; LOG; MSTORE; MSTORE8; ISTORE; MCOPY;
     CALLDATACOPY; RETURNDATACOPY; CODECOPY; EXTCODECOPY;
     CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  step_inst_base inst s = OK s' ==>
  step_inst_base inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `~is_pre_codegen_opcode inst.inst_opcode` by
    (irule codegen_ready_inst_not_pre >> metis_tac[]) >>
  `~MEM inst.inst_opcode
    [RET; RETFMP; DRET; STOP; RETURN; REVERT; SINK; SELFDESTRUCT; INVALID; PHI]`
    by metis_tac[terminal_base_not_ok] >>
  `MEM inst.inst_opcode
    [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR;
     SIGNEXTEND; BYTE; OFFSET] \/
   MEM inst.inst_opcode
    [SLOAD; TLOAD; CALLER; ADDRESS; CALLVALUE; GAS; ORIGIN; GASPRICE;
     CHAINID; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
     BLOBBASEFEE; BLOCKHASH; BLOBHASH; BALANCE; SELFBALANCE; CALLDATASIZE;
     CALLDATALOAD; RETURNDATASIZE; CODESIZE; EXTCODESIZE; EXTCODEHASH] \/
   MEM inst.inst_opcode [SSTORE; TSTORE] \/
   MEM inst.inst_opcode
    [NOP; JMP; JNZ; DJMP; ASSERT; ASSERT_UNREACHABLE; INITIAL_FMP; BUMP]`
    by (Cases_on `inst.inst_opcode` >>
        gvs[is_pre_codegen_opcode_def, is_param_opcode_def,
            is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
            is_raw_fmp_opcode_def]) >>
  FIRST [drule_all scalar_base_frame_view, drule_all environment_base_frame_view,
         drule_all storage_base_frame_view, drule_all control_base_frame_view] >>
  metis_tac[]
QED

Theorem nonmemory_step_frame_view:
  step_inst fuel ctx inst s = OK s' /\
  inst.inst_opcode <> INVOKE /\ ~is_param_opcode inst.inst_opcode /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  ~MEM inst.inst_opcode
    [ASSIGN; MLOAD; ILOAD; SHA3; LOG; MSTORE; MSTORE8; ISTORE; MCOPY;
     CALLDATACOPY; RETURNDATACOPY; CODECOPY; EXTCODECOPY;
     CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  ?m'. step_inst fuel ctx inst (frame_view fn ra s with vs_memory := m) =
         OK (frame_view fn ra s' with vs_memory := m') /\
       (!i. read_byte i m = read_byte i s.vs_memory ==>
            read_byte i m' = read_byte i s'.vs_memory) /\
       (!i. EVERY (\r. ~byte_in_memory_range r i)
              (source_memory_write_ranges inst s) ==>
            read_byte i m' = read_byte i m)
Proof
  strip_tac >>
  `step_inst_base inst s = OK s'` by
    (qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
     simp[Once step_inst_def]) >>
  drule_all nonmemory_base_frame_view >>
  disch_then (qspecl_then [`ra`, `m`] strip_assume_tac) >>
  qexists_tac `m` >> simp[Once step_inst_def]
QED
