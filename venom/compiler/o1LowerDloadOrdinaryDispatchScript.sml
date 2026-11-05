Theory o1LowerDloadOrdinaryDispatch
Ancestors
  o1LowerDloadPtrDiscipline o1LowerDloadJointArithmetic o1LowerDloadJointScalar
  o1LowerDloadJointTernary o1LowerDloadJointCompare o1LowerDloadJointShift
  o1LowerDloadJointResidualScalar o1LowerDloadJointRead0 o1LowerDloadJointRead1
  o1LowerDloadJointParam o1LowerDloadJointRetpc o1LowerDloadJointAssign
  o1LowerDloadJointBump o1LowerDloadJointIdentity o1LowerDloadJointMemoryRead
  o1LowerDloadJointMemoryWrite o1LowerDloadJointCleanWrite
  o1LowerDloadJointRangeCopy o1LowerDloadJointRangeRead
  o1LowerDloadJointStorageRead o1LowerDloadJointStorageWrite
  o1LowerDloadJointInternalEffects o1LowerDloadJointExternal
  o1LowerDloadReadiness venomInstProps o1LowerDloadJointRelation
  o1LowerDloadOccurrence o1PassContract contextCodegenRel venomInst
  venomWf ptrDiscipline venomExecSemantics list

Theorem ld_joint_ordinary_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t n a U B HP H sites X ts /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_src_inv D C vs /\
  callee_first names C.ctx_functions /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  (?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst) /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DLOAD; DLOADBYTES; ALLOCA] /\
  ~in_revert_forward fn s /\ step_inst fuel C inst s = OK s1 ==>
  ?inst2 t1 u fn'.
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule ld_joint_source >> strip_tac >>
     drule occ_frame_reachable_annotation >> simp[]) >>
  `wf_function fn` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> first_x_assum drule >>
     simp[o1_fn_shape_def]) >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `?inst2. active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ld_nonterminator_successor >>
     drule_all step_preserves_control_flow >> simp[] >> metis_tac[]) >>
  `~MEM inst.inst_opcode [MEMTOP; DRET; GETFMP; SETFMP; RETFMP; FMP_PARAM]` by
    (`?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
       metis_tac[ptr_discipline_fn_ptr_ok] >>
     fs[EVERY_MEM] >> first_x_assum drule >>
     simp[fn_ptr_ok_def] >> strip_tac >> first_x_assum drule >> simp[MEM]) >>
  `inst.inst_opcode <> DALLOCA` by
    (fs[o1_src_inv_def, ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
  qexists_tac `inst2` >> simp[] >>
  Cases_on `MEM inst.inst_opcode [ADD; SUB]`
  >- (irule ld_joint_arithmetic_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; SLT; SGT; AND; OR; XOR]`
  >- (irule ld_joint_binary_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [ADDMOD; MULMOD]`
  >- (irule ld_joint_ternary_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [ISZERO; NOT]`
  >- (irule ld_joint_unary_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [LT; GT; EQ]`
  >- (irule ld_joint_compare_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [SHL; SHR; SAR]`
  >- (irule ld_joint_shift_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [SIGNEXTEND; BYTE; OFFSET; INITIAL_FMP]`
  >- (irule ld_joint_residual_scalar_next >> simp[]) >>
  Cases_on `inst.inst_opcode = GAS`
  >- (irule ld_joint_gas_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE;
    CHAINID; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
    BLOBBASEFEE; CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE]`
  >- (irule ld_joint_read0_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [BLOCKHASH; BLOBHASH; BALANCE; EXTCODESIZE; EXTCODEHASH; CALLDATALOAD]`
  >- (irule ld_joint_read1_next >> simp[]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (irule ld_joint_param_next >> simp[]) >>
  Cases_on `inst.inst_opcode = RETPC_PARAM`
  >- (irule ld_joint_retpc_next >> simp[]) >>
  Cases_on `inst.inst_opcode = ASSIGN`
  >- (irule ld_joint_assign_next >> simp[]) >>
  Cases_on `inst.inst_opcode = BUMP`
  >- (irule ld_joint_bump_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE]`
  >- (irule ld_joint_identity_next >> simp[]) >>
  Cases_on `inst.inst_opcode = MLOAD`
  >- (irule ld_joint_mload_next >> simp[]) >>
  Cases_on `inst.inst_opcode = MSTORE`
  >- (irule ld_joint_mstore_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [MSTORE8; CALLDATACOPY; CODECOPY; RETURNDATACOPY; EXTCODECOPY]`
  >- (irule ld_joint_clean_write_next >> simp[]) >>
  Cases_on `inst.inst_opcode = MCOPY`
  >- (irule ld_joint_mcopy_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [ILOAD; SHA3]`
  >- (irule ld_joint_range_read_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [SLOAD; TLOAD]`
  >- (irule ld_joint_storage_load_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [SSTORE; TSTORE]`
  >- (irule ld_joint_storage_store_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [ISTORE; LOG]`
  >- (irule ld_joint_internal_effect_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [CALL; STATICCALL]`
  >- (irule ld_joint_call_next >> simp[]) >>
  Cases_on `inst.inst_opcode = DELEGATECALL`
  >- (irule ld_joint_delegatecall_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [CREATE; CREATE2]`
  >- (irule ld_joint_create_next >> simp[]) >>
  `inst.inst_opcode = PHI` by
    (Cases_on `inst.inst_opcode` >> gvs[MEM, is_terminator_def]) >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED
