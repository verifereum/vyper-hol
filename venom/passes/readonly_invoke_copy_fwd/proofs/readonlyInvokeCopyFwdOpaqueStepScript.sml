(* Exact-memory execution through the opaque return-PC view. *)
Theory readonlyInvokeCopyFwdOpaqueStep
Ancestors
  readonlyInvokeCopyFwdOpaque frameViewFacts frameViewScalar frameViewRead
  frameViewWrite frameViewCall unitShapeDefs venomExecSemantics venomState
  frameRel venomMemProps venomCallOracleDefs list finite_map

Theorem ricf_view_pure1_ok[local]:
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (ricf_retpc_view fn s) = eval_operand op s) /\
  (!out. MEM out inst.inst_outputs ==> ~retpc_var fn out) ==>
  (exec_pure1 f inst (ricf_retpc_view fn s) = OK v <=>
   ?u. exec_pure1 f inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >> EQ_TAC >>
  simp[exec_pure1_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[MEM, ricf_retpc_view_update_var] >>
  metis_tac[ricf_retpc_view_update_var]
QED

Theorem ricf_view_pure2_ok[local]:
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (ricf_retpc_view fn s) = eval_operand op s) /\
  (!out. MEM out inst.inst_outputs ==> ~retpc_var fn out) ==>
  (exec_pure2 f inst (ricf_retpc_view fn s) = OK v <=>
   ?u. exec_pure2 f inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >> EQ_TAC >>
  simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[MEM, ricf_retpc_view_update_var] >>
  metis_tac[ricf_retpc_view_update_var]
QED

Theorem ricf_view_pure3_ok[local]:
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (ricf_retpc_view fn s) = eval_operand op s) /\
  (!out. MEM out inst.inst_outputs ==> ~retpc_var fn out) ==>
  (exec_pure3 f inst (ricf_retpc_view fn s) = OK v <=>
   ?u. exec_pure3 f inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >> EQ_TAC >>
  simp[exec_pure3_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[MEM, ricf_retpc_view_update_var] >>
  metis_tac[ricf_retpc_view_update_var]
QED

Theorem ricf_view_read0_ok[local]:
  f (ricf_retpc_view fn s) = f s /\
  (!out. MEM out inst.inst_outputs ==> ~retpc_var fn out) ==>
  (exec_read0 f inst (ricf_retpc_view fn s) = OK v <=>
   ?u. exec_read0 f inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >> EQ_TAC >>
  simp[exec_read0_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[MEM, ricf_retpc_view_update_var] >>
  metis_tac[ricf_retpc_view_update_var]
QED

Theorem ricf_view_read1_ok[local]:
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (ricf_retpc_view fn s) = eval_operand op s) /\
  (!out. MEM out inst.inst_outputs ==> ~retpc_var fn out) /\
  (!x. f x (ricf_retpc_view fn s) = f x s) ==>
  (exec_read1 f inst (ricf_retpc_view fn s) = OK v <=>
   ?u. exec_read1 f inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >> EQ_TAC >>
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[MEM, ricf_retpc_view_update_var] >>
  metis_tac[ricf_retpc_view_update_var]
QED

val opcode_equations = CONJUNCTS step_inst_base_opcode_eqs;
fun opcode_equation opc =
  valOf (List.find
    (fn th => aconv (rhs (fst (dest_imp (snd (strip_forall (concl th)))))) opc)
    opcode_equations);

Theorem ricf_retpc_view_scalar_ok[local]:
  ssa_form fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode
    [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR;
     SIGNEXTEND; BYTE; OFFSET] ==>
  (step_inst_base inst (ricf_retpc_view fn s) = OK v <=>
   ?u. step_inst_base inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (ricf_retpc_view fn s) = eval_operand op s` by
    (rpt strip_tac >> irule ricf_retpc_view_operand >>
     gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  `!out. MEM out inst.inst_outputs ==> ~retpc_var fn out` by
    (rpt gen_tac >> strip_tac >> irule noncopy_output_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_assum `inst.inst_opcode = _`
    (fn th => simp[opcode_equation (rhs (concl th))]) >>
  FIRST [irule ricf_view_pure1_ok, irule ricf_view_pure2_ok,
         irule ricf_view_pure3_ok] >> simp[]
QED

Theorem ricf_retpc_view_alloca_ok[local]:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
  (step_inst_base inst (ricf_retpc_view fn s) = OK v <=>
   ?u. step_inst_base inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >>
  `!out. MEM out inst.inst_outputs ==> ~retpc_var fn out` by
    (rpt gen_tac >> strip_tac >> irule noncopy_output_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  Cases_on `inst.inst_operands` >> simp[opcode_equation ``ALLOCA``] >>
  rename1 `inst.inst_operands = op::ops` >>
  Cases_on `op` >> simp[opcode_equation ``ALLOCA``] >>
  Cases_on `ops` >> simp[opcode_equation ``ALLOCA``] >>
  Cases_on `inst.inst_outputs` >> simp[exec_alloca_def] >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> simp[exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >>
  gvs[MEM, ricf_retpc_view_def, frame_view_def, exec_alloca_def,
    update_var_def, FMAP_MAP2_FUPDATE]
  >- metis_tac[] >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME old` >>
  Cases_on `old` >>
  gvs[MEM, ricf_retpc_view_def, frame_view_def, exec_alloca_def,
    update_var_def, FMAP_MAP2_FUPDATE] >> metis_tac[]
QED

Theorem ricf_retpc_view_reads_ok[local]:
  ssa_form fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode
    [MLOAD; ILOAD; SLOAD; TLOAD; CALLER; ADDRESS; CALLVALUE; ORIGIN;
     GASPRICE; CHAINID; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT;
     BASEFEE; BLOBBASEFEE; BLOCKHASH; BLOBHASH; BALANCE; SELFBALANCE;
     CALLDATASIZE; CALLDATALOAD; RETURNDATASIZE; CODESIZE; EXTCODESIZE;
     EXTCODEHASH; MEMTOP; DLOAD] ==>
  (step_inst_base inst (ricf_retpc_view fn s) = OK v <=>
   ?u. step_inst_base inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (ricf_retpc_view fn s) = eval_operand op s` by
    (rpt strip_tac >> irule ricf_retpc_view_operand >>
     gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  `!out. MEM out inst.inst_outputs ==> ~retpc_var fn out` by
    (rpt gen_tac >> strip_tac >> irule noncopy_output_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_assum `inst.inst_opcode = _`
    (fn th => simp[opcode_equation (rhs (concl th))]) >>
  FIRST [irule ricf_view_read0_ok, irule ricf_view_read1_ok] >>
  simp[ricf_retpc_view_def, frame_view_def, sload_def, tload_def,
    contract_storage_def, contract_transient_def, mload_def]
QED

Theorem ricf_retpc_view_local_params_ok[local]:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM; GETFMP; INITIAL_FMP] ==>
  (step_inst_base inst (ricf_retpc_view fn s) = OK v <=>
   ?u. step_inst_base inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >>
  `!out. MEM out inst.inst_outputs /\ inst.inst_opcode <> RETPC_PARAM ==>
    ~retpc_var fn out` by
    (rpt gen_tac >> strip_tac >> irule noncopy_output_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  `!out. MEM out inst.inst_outputs /\ inst.inst_opcode = RETPC_PARAM ==>
    retpc_var fn out` by
    (rpt strip_tac >> simp[retpc_var_def] >>
     irule copy_phi_var_seed >> metis_tac[]) >>
  `(ricf_retpc_view fn s).vs_params = s.vs_params /\
   (ricf_retpc_view fn s).vs_fmp = s.vs_fmp /\
   (ricf_retpc_view fn s).vs_initial_fmp = s.vs_initial_fmp /\
   (ricf_retpc_view fn s).vs_return_pc_token = 0w` by
    simp[ricf_retpc_view_def, frame_view_def] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  EQ_TAC >>
  qpat_assum `inst.inst_opcode = _`
    (fn th => simp[opcode_equation (rhs (concl th)), AllCaseEqs()]) >>
  rpt strip_tac >> gvs[MEM, ricf_retpc_view_update_var] >>
  metis_tac[ricf_retpc_view_update_var]
QED

Theorem ricf_view_assign_eval_ok[local]:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [op] /\ MEM out inst.inst_outputs ==>
  (eval_operand op (ricf_retpc_view fn s) = SOME w <=>
   ?x. eval_operand op s = SOME x /\
       w = if retpc_var fn out then 0w else x)
Proof
  strip_tac >> Cases_on `op`
  >- (`~retpc_var fn out` by
        (strip_tac >> drule_all retpc_var_output_cases >> simp[]) >>
      simp[eval_operand_def, ricf_retpc_view_def, frame_view_def] >> metis_tac[])
  >- (rename1 `inst.inst_operands = [Var name]` >>
      `retpc_var fn out <=> retpc_var fn name` by
        metis_tac[assign_output_retpc] >>
      simp[eval_operand_def, lookup_var_def, ricf_retpc_view_vars] >>
      Cases_on `FLOOKUP s.vs_vars name` >> simp[] >> metis_tac[])
  >> (`~retpc_var fn out` by
        (strip_tac >> drule_all retpc_var_output_cases >> simp[]) >>
      simp[eval_operand_def, ricf_retpc_view_def, frame_view_def] >> metis_tac[])
QED

Theorem ricf_retpc_view_assign_ok[local]:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = ASSIGN ==>
  (step_inst_base inst (ricf_retpc_view fn s) = OK v <=>
   ?u. step_inst_base inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >> simp[opcode_equation ``ASSIGN``] >>
  rename1 `inst.inst_operands = op::ops` >>
  Cases_on `ops` >> simp[opcode_equation ``ASSIGN``] >>
  Cases_on `inst.inst_outputs` >> simp[opcode_equation ``ASSIGN``] >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> simp[opcode_equation ``ASSIGN``] >>
  `!w. eval_operand op (ricf_retpc_view fn s) = SOME w <=>
    ?x. eval_operand op s = SOME x /\
      w = if retpc_var fn out then 0w else x` by
    (gen_tac >> irule ricf_view_assign_eval_ok >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  EQ_TAC >> simp[AllCaseEqs()] >> rpt strip_tac >>
  gvs[ricf_retpc_view_update_var] >> metis_tac[ricf_retpc_view_update_var]
QED

Theorem ricf_retpc_view_control_ok[local]:
  ssa_form fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode
    [NOP; JMP; JNZ; DJMP; ASSERT; ASSERT_UNREACHABLE; SETFMP; DALLOCA; BUMP;
     GAS] ==>
  (step_inst_base inst (ricf_retpc_view fn s) = OK v <=>
   ?u. step_inst_base inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (ricf_retpc_view fn s) = eval_operand op s` by
    (rpt strip_tac >> irule ricf_retpc_view_operand >>
     gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  `!out. MEM out inst.inst_outputs ==> ~retpc_var fn out` by
    (rpt gen_tac >> strip_tac >> irule noncopy_output_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  EQ_TAC >>
  qpat_assum `inst.inst_opcode = _`
    (fn th => simp[opcode_equation (rhs (concl th)), exec_gas_def,
      AllCaseEqs(), ricf_retpc_view_update_var]) >>
  rpt strip_tac >> gvs[MEM] >>
  gvs[ricf_retpc_view_def, frame_view_def, jump_to_def,
    update_var_def, FMAP_MAP2_FUPDATE] >>
  qpat_x_assum `SOME _ = eval_operand _ s`
    (fn th => simp[GSYM th, FMAP_MAP2_FUPDATE]) >>
  metis_tac[MEM]
QED

Theorem ricf_retpc_view_terminal_not_ok[local]:
  MEM inst.inst_opcode
    [RET; RETFMP; DRET; STOP; RETURN; REVERT; SINK; SELFDESTRUCT; INVALID; PHI]
  ==>
  (step_inst_base inst (ricf_retpc_view fn s) = OK v <=>
   ?u. step_inst_base inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  metis_tac[terminal_base_not_ok]
QED

Theorem ricf_retpc_view_log_ok[local]:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = LOG ==>
  (step_inst_base inst (ricf_retpc_view fn s) = OK v <=>
   ?u. step_inst_base inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >>
  `(ricf_retpc_view fn s).vs_call_ctx = s.vs_call_ctx /\
   (ricf_retpc_view fn s).vs_memory = s.vs_memory /\
   (ricf_retpc_view fn s).vs_logs = s.vs_logs` by
    simp[ricf_retpc_view_def, frame_view_def] >>
  `!logs. ricf_retpc_view fn (s with vs_logs := logs) =
    (ricf_retpc_view fn s with vs_logs := logs)` by
    simp[ricf_retpc_view_def, frame_view_def] >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (ricf_retpc_view fn s) = eval_operand op s` by
    (rpt strip_tac >> irule ricf_retpc_view_operand >>
     gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  `!ops. EVERY (\op. MEM op inst.inst_operands) ops ==>
    eval_operands ops (ricf_retpc_view fn s) = eval_operands ops s` by
    (rpt strip_tac >> irule ricf_retpc_view_operands >>
     fs[EVERY_MEM] >> rpt gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  `eval_operands inst.inst_operands (ricf_retpc_view fn s) =
    eval_operands inst.inst_operands s` by
    (first_x_assum irule >> simp[EVERY_MEM]) >>
  Cases_on `inst.inst_operands` >>
  simp[opcode_equation ``LOG``, AllCaseEqs()] >>
  Cases_on `h` >> simp[opcode_equation ``LOG``, AllCaseEqs()] >>
  rename1 `inst.inst_operands = Lit tc::rest` >>
  Cases_on `LENGTH rest = w2n tc + 2` >> simp[] >>
  `MEM (HD (REVERSE rest)) rest` by
    (`MEM (EL 0 (REVERSE rest)) (REVERSE rest)` by
      (irule EL_MEM >> simp[]) >> gvs[MEM_REVERSE]) >>
  `MEM (EL 1 (REVERSE rest)) rest` by
    (once_rewrite_tac[GSYM MEM_REVERSE] >> irule EL_MEM >> simp[]) >>
  `EVERY (\op. op = Lit tc \/ MEM op rest) (DROP 2 (REVERSE rest))` by
    (simp[EVERY_MEM] >> rpt strip_tac >> disj2_tac >>
     drule rich_listTheory.MEM_DROP_IMP >> simp[MEM_REVERSE]) >>
  EQ_TAC >> simp[opcode_equation ``LOG``, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ricf_retpc_view_memory_ok[local]:
  ssa_form fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode
    [MSTORE; MSTORE8; ISTORE; MCOPY; SSTORE; TSTORE; SHA3;
     CALLDATACOPY; RETURNDATACOPY; DLOADBYTES; CODECOPY; EXTCODECOPY] ==>
  (step_inst_base inst (ricf_retpc_view fn s) = OK v <=>
   ?u. step_inst_base inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >>
  `(ricf_retpc_view fn s).vs_call_ctx = s.vs_call_ctx /\
   (ricf_retpc_view fn s).vs_memory = s.vs_memory /\
   (ricf_retpc_view fn s).vs_returndata = s.vs_returndata /\
   (ricf_retpc_view fn s).vs_data_section = s.vs_data_section /\
   (ricf_retpc_view fn s).vs_code = s.vs_code /\
   (ricf_retpc_view fn s).vs_accounts = s.vs_accounts` by
    simp[ricf_retpc_view_def, frame_view_def] >>
  `(!off xs. write_memory_with_expansion off xs (ricf_retpc_view fn s) =
      ricf_retpc_view fn (write_memory_with_expansion off xs s)) /\
   (!off w. mstore off w (ricf_retpc_view fn s) =
      ricf_retpc_view fn (mstore off w s)) /\
   (!off w. mstore8 off w (ricf_retpc_view fn s) =
      ricf_retpc_view fn (mstore8 off w s)) /\
   (!off w. istore off w (ricf_retpc_view fn s) =
      ricf_retpc_view fn (istore off w s)) /\
   (!dst src sz. mcopy dst src sz (ricf_retpc_view fn s) =
      ricf_retpc_view fn (mcopy dst src sz s)) /\
   (!key w. sstore key w (ricf_retpc_view fn s) =
      ricf_retpc_view fn (sstore key w s)) /\
   (!key w. tstore key w (ricf_retpc_view fn s) =
      ricf_retpc_view fn (tstore key w s))` by
    (rpt conj_tac >> simp[ricf_retpc_view_def, frame_view_def,
      mstore_eq_write_mem, mstore8_def, write_memory_with_expansion_def,
      istore_def, mcopy_def, sstore_def, tstore_def]) >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (ricf_retpc_view fn s) = eval_operand op s` by
    (rpt strip_tac >> irule ricf_retpc_view_operand >>
     gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  `eval_operands inst.inst_operands (ricf_retpc_view fn s) =
     eval_operands inst.inst_operands s` by
    (irule ricf_retpc_view_operands >>
     rpt gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  `!out. MEM out inst.inst_outputs ==> ~retpc_var fn out` by
    (rpt gen_tac >> strip_tac >> irule noncopy_output_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  EQ_TAC >>
  qpat_assum `inst.inst_opcode = _`
    (fn th => simp[opcode_equation (rhs (concl th)), exec_write2_def,
      AllCaseEqs(), ricf_retpc_view_update_var]) >>
  rpt strip_tac >> gvs[MEM, ricf_retpc_view_update_var] >>
  metis_tac[ricf_retpc_view_update_var]
QED

Theorem ricf_view_consume_call[local]:
  consume_call_outcome rq ro rs s = (w,r) ==>
  consume_call_outcome rq ro rs (ricf_retpc_view fn s) =
    (w,ricf_retpc_view fn r)
Proof
  simp[consume_call_outcome_eq, ricf_retpc_view_def, frame_view_def,
    write_memory_with_expansion_def] >> strip_tac >> gvs[]
QED

Theorem ricf_view_consume_create[local]:
  consume_create_outcome rq s = (w,r) ==>
  consume_create_outcome rq (ricf_retpc_view fn s) =
    (w,ricf_retpc_view fn r)
Proof
  simp[consume_create_outcome_eq, ricf_retpc_view_def, frame_view_def] >>
  strip_tac >> gvs[]
QED

Theorem ricf_view_ext_call_ok[local]:
  (!out. MEM out inst.inst_outputs ==> ~retpc_var fn out) ==>
  (exec_ext_call inst (ricf_retpc_view fn s)
     gas addr value ao az ro rz staticflag = OK v <=>
   ?u. exec_ext_call inst s gas addr value ao az ro rz staticflag = OK u /\
       v = ricf_retpc_view fn u)
Proof
  strip_tac >>
  `venom_call_request (ricf_retpc_view fn s) addr value ao az staticflag =
    venom_call_request s addr value ao az staticflag` by
    simp[venom_call_request_def, read_memory_def,
      ricf_retpc_view_def, frame_view_def] >>
  Cases_on `consume_call_outcome
    (venom_call_request s addr value ao az staticflag) (w2n ro) (w2n rz) s` >>
  drule ricf_view_consume_call >>
  disch_then (qspec_then `fn` assume_tac) >>
  EQ_TAC >> simp[exec_ext_call_def, AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
  rpt strip_tac >> gvs[MEM, ricf_retpc_view_update_var, Excl "consume_call_outcome_eq"] >>
  metis_tac[ricf_retpc_view_update_var]
QED

Theorem ricf_view_create_ok[local]:
  (!out. MEM out inst.inst_outputs ==> ~retpc_var fn out) ==>
  (exec_create inst (ricf_retpc_view fn s) value off sz salt = OK v <=>
   ?u. exec_create inst s value off sz salt = OK u /\
       v = ricf_retpc_view fn u)
Proof
  strip_tac >>
  `venom_create_request (ricf_retpc_view fn s) value off sz salt =
    venom_create_request s value off sz salt` by
    simp[venom_create_request_def, read_memory_def,
      ricf_retpc_view_def, frame_view_def] >>
  Cases_on `consume_create_outcome (venom_create_request s value off sz salt) s` >>
  drule ricf_view_consume_create >>
  disch_then (qspec_then `fn` assume_tac) >>
  EQ_TAC >> simp[exec_create_def, AllCaseEqs(), Excl "consume_create_outcome_eq"] >>
  rpt strip_tac >> gvs[MEM, ricf_retpc_view_update_var, Excl "consume_create_outcome_eq"] >>
  metis_tac[ricf_retpc_view_update_var]
QED

Theorem ricf_view_delegatecall_ok[local]:
  (!out. MEM out inst.inst_outputs ==> ~retpc_var fn out) ==>
  (exec_delegatecall inst (ricf_retpc_view fn s) gas addr ao az ro rz = OK v <=>
   ?u. exec_delegatecall inst s gas addr ao az ro rz = OK u /\
       v = ricf_retpc_view fn u)
Proof
  strip_tac >>
  `venom_call_request (ricf_retpc_view fn s) addr 0w ao az F =
    venom_call_request s addr 0w ao az F` by
    simp[venom_call_request_def, read_memory_def,
      ricf_retpc_view_def, frame_view_def] >>
  Cases_on `consume_call_outcome
    (venom_call_request s addr 0w ao az F with cr_kind := DelegateMessageCall)
    (w2n ro) (w2n rz) s` >>
  drule ricf_view_consume_call >>
  disch_then (qspec_then `fn` assume_tac) >>
  EQ_TAC >> simp[exec_delegatecall_def, AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
  rpt strip_tac >> gvs[MEM, ricf_retpc_view_update_var, Excl "consume_call_outcome_eq"] >>
  metis_tac[ricf_retpc_view_update_var]
QED

Theorem ricf_retpc_view_external_ok[local]:
  ssa_form fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  (step_inst_base inst (ricf_retpc_view fn s) = OK v <=>
   ?u. step_inst_base inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (ricf_retpc_view fn s) = eval_operand op s` by
    (rpt strip_tac >> irule ricf_retpc_view_operand >>
     gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  `eval_operands inst.inst_operands (ricf_retpc_view fn s) =
     eval_operands inst.inst_operands s` by
    (irule ricf_retpc_view_operands >>
     rpt gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  `!out. MEM out inst.inst_outputs ==> ~retpc_var fn out` by
    (rpt gen_tac >> strip_tac >> irule noncopy_output_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  `(ricf_retpc_view fn s).vs_call_ctx = s.vs_call_ctx` by
    simp[ricf_retpc_view_def, frame_view_def] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  EQ_TAC >>
  qpat_assum `inst.inst_opcode = _`
    (fn th => simp[opcode_equation (rhs (concl th)), AllCaseEqs()]) >>
  rpt strip_tac >> gvs[MEM, ricf_view_ext_call_ok,
    ricf_view_delegatecall_ok, ricf_view_create_ok] >> metis_tac[]
QED

val view_ok_families =
  [(["ADD", "SUB", "MUL", "Div", "Mod", "SDIV", "SMOD", "Exp",
     "ADDMOD", "MULMOD", "EQ", "LT", "GT", "SLT", "SGT", "ISZERO",
     "AND", "OR", "XOR", "NOT", "SHL", "SHR", "SAR", "SIGNEXTEND",
     "BYTE", "OFFSET"], ricf_retpc_view_scalar_ok),
   (["MLOAD", "ILOAD", "SLOAD", "TLOAD", "CALLER", "ADDRESS",
     "CALLVALUE", "ORIGIN", "GASPRICE", "CHAINID", "COINBASE",
     "TIMESTAMP", "NUMBER", "PREVRANDAO", "GASLIMIT", "BASEFEE",
     "BLOBBASEFEE", "BLOCKHASH", "BLOBHASH", "BALANCE", "SELFBALANCE",
     "CALLDATASIZE", "CALLDATALOAD", "RETURNDATASIZE", "CODESIZE",
     "EXTCODESIZE", "EXTCODEHASH", "MEMTOP", "DLOAD"],
    ricf_retpc_view_reads_ok),
   (["ALLOCA"], ricf_retpc_view_alloca_ok),
   (["PARAM", "FMP_PARAM", "RETPC_PARAM", "GETFMP", "INITIAL_FMP"],
    ricf_retpc_view_local_params_ok),
   (["ASSIGN"], ricf_retpc_view_assign_ok),
   (["NOP", "JMP", "JNZ", "DJMP", "ASSERT", "ASSERT_UNREACHABLE",
     "SETFMP", "DALLOCA", "BUMP", "GAS"], ricf_retpc_view_control_ok),
   (["RET", "RETFMP", "DRET", "STOP", "RETURN", "REVERT", "SINK",
     "SELFDESTRUCT", "INVALID", "PHI"], ricf_retpc_view_terminal_not_ok),
   (["MSTORE", "MSTORE8", "ISTORE", "MCOPY", "SSTORE", "TSTORE",
     "SHA3", "CALLDATACOPY", "RETURNDATACOPY", "DLOADBYTES",
     "CODECOPY", "EXTCODECOPY"], ricf_retpc_view_memory_ok),
   (["LOG"], ricf_retpc_view_log_ok),
   (["CALL", "STATICCALL", "DELEGATECALL", "CREATE", "CREATE2"],
    ricf_retpc_view_external_ok)];

Theorem ricf_retpc_view_step_ok:
  ssa_form fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> INVOKE ==>
  (step_inst fuel C inst (ricf_retpc_view fn s) = OK v <=>
   ?u. step_inst fuel C inst s = OK u /\ v = ricf_retpc_view fn u)
Proof
  strip_tac >> simp[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_assum `inst.inst_opcode = _` (fn th =>
    irule (#2 (valOf (List.find
      (fn (ops,_) => List.exists
        (fn opc => opc = fst (dest_const (rhs (concl th)))) ops)
      view_ok_families)))) >> simp[]
QED
