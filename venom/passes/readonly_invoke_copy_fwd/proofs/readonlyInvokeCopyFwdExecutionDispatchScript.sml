Theory readonlyInvokeCopyFwdExecutionDispatch
Ancestors
  readonlyInvokeCopyFwdExecutionCallSteps readonlyInvokeCopyFwdExecutionTerminal
  readonlyInvokeCopyFwdExecutionBuiltins
  readonlyInvokeCopyFwdExecutionSteps readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionBoundary readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdHistory
  invokeCopyFwdCommonDefs readonlyMemoryArgsDefs
  o1LowerDloadOccurrence o1LowerDloadPtrDiscipline o1LowerDloadGhost
  ptrDiscipline ptrDisciplineControl reachableFnSim o1PassContract unitShapeDefs
  contextCodegenRel allocaFrontierBound passSimulationDefs
  venomExecSemantics venomExecProofs venomWf venomInst venomState
  finite_map list

Theorem ricf_execution_terminal:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY ricf_full_alloca_copies C.ctx_functions /\ EVERY ricf_src_alloca C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~vs.vs_halted /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ mem_inv raw_mem_ok C vs /\ taint_within D C vs /\
  (!f. MEM f C.ctx_functions ==>
    ricf_logged_function_trace
      (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) f)
      f (log_of f) (mid_of f) /\ ricf_function_edit f (mid_of f) /\
    ?f'. lookup_function f.fn_name Ct.ctx_functions = SOME f' /\
      fn_entry_label f' = fn_entry_label f) /\
  (!a1 U1 B1 E1 history1 certificates1 sites1 maps1 targets1.
    fn_sim_below D vs C Ct
      (ricf_execution_boundary vs C mid_of log_of D a1 U1 B1 E1 history1 certificates1
        sites1 maps1 targets1)
      (ricf_execution_return vs C Ct mid_of log_of D a1 U1 B1 E1 history1 certificates1
        sites1 maps1 targets1) (SUC k)) /\
  ricf_block_edit bb tb /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (mid_of fn).fn_blocks = SOME tb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction tb t.vs_inst_idx = SOME ti /\
  terminates (step_inst k C inst s) /\
  (!u. step_inst k C inst s = OK u ==> is_terminator inst.inst_opcode) ==>
  ?m. block_step_rel D vs C
    (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    stk PG fn (step_inst k C inst s) (step_inst m Ct ti t)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all ricf_execution_invoke_terminal_result >> simp[]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_point_def, ricf_execution_invariant_def,
       ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions` by metis_tac[frame_reachable_prov_support] >>
  `ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
   ricf_function_edit fn (mid_of fn)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    metis_tac[ricf_execution_point_control] >>
  `ricf_inst_edit inst ti` by
    (drule_all ricf_block_edit_fetch >> strip_tac >> gvs[]) >>
  drule_all ricf_execution_noninvoke_terminal >> simp[]
QED

Theorem ricf_execution_builtin_next:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY ricf_full_alloca_copies C.ctx_functions /\ EVERY ricf_src_alloca C.ctx_functions /\
  EVERY ricf_param_order_ok C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ mem_inv raw_mem_ok C vs /\
  ricf_block_edit bb tb /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ get_instruction tb t.vs_inst_idx = SOME ti /\
  ~in_revert_forward fn s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> MCOPY /\
  ~MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  step_inst k C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst k Ct ti t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG (step_prov PG G inst u) (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `active_inst fn inst s` by
    (simp[active_inst_def] >> qexists_tac `bb` >>
     fs[get_instruction_def] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_point_def, ricf_execution_invariant_def,
       ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions` by metis_tac[frame_reachable_prov_support] >>
  `o1_fn_shape C fn /\ wf_ssa fn /\
   ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
   EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
   ricf_full_alloca_copies fn /\ ricf_src_alloca fn` by
    (fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def,
       o1_fn_shape_def, fn_shape_ok_def, wf_ssa_def, EVERY_MEM] >>
     metis_tac[]) >>
  `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
  `~MEM inst.inst_opcode [MEMTOP;GETFMP;SETFMP;FMP_PARAM;DJMP;OFFSET]` by
    (fs[MEM, EVERY_MEM, fn_ptr_ok_def, o1_fn_shape_def, fn_shape_ok_def,
       inst_shape_ok_def] >> metis_tac[]) >>
  `inst.inst_opcode <> DALLOCA` by
    (fs[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
  `inst.inst_opcode <> PHI` by
    (strip_tac >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  `MEM inst.inst_opcode [ISZERO;NOT;MUL;Div;Mod;SDIV;SMOD;Exp;
    SLT;SGT;AND;OR;XOR;ADDMOD;MULMOD;ADD;SUB;LT;GT;EQ;SHL;SHR;SAR;SIGNEXTEND;BYTE;GAS;
    CALLER;ADDRESS;CALLVALUE;ORIGIN;GASPRICE;CHAINID;COINBASE;TIMESTAMP;NUMBER;
    PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;CALLDATASIZE;RETURNDATASIZE;CODESIZE;
    SELFBALANCE;BLOCKHASH;BLOBHASH;BALANCE;EXTCODESIZE;EXTCODEHASH;CALLDATALOAD;DLOAD;
    SLOAD;TLOAD;MLOAD;ILOAD;MSTORE;ISTORE;MSTORE8;SSTORE;TSTORE;ASSERT;ASSERT_UNREACHABLE;
    CALLDATACOPY;DLOADBYTES;CODECOPY;RETURNDATACOPY;EXTCODECOPY;SHA3;LOG;BUMP;
    ALLOCA;PARAM;RETPC_PARAM;ASSIGN;NOP;INITIAL_FMP]` by
    (Cases_on `inst.inst_opcode` >> gvs[MEM, is_terminator_def]) >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    metis_tac[ricf_execution_point_control] >>
  `ricf_inst_edit inst ti` by
    (drule_all ricf_block_edit_fetch >> strip_tac >> gvs[]) >>
  `ti = inst` by (fs[ricf_inst_edit_def] >> gvs[]) >> gvs[] >>
  mp_tac (Q.INST [`fuel` |-> `k`] (SPEC_ALL ricf_execution_point_builtin)) >>
  (impl_tac >- simp[]) >> simp[]
QED
