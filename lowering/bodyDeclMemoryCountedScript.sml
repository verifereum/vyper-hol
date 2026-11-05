(* Counted straight-line paths for declaration memory operations. *)
Theory bodyDeclMemoryCounted
Ancestors
  bodyDeclMemoryCore fragGasSeqMem
  loweringPosts exprSimProps stmtSimProps exprSimHypsDefs
  bodyNameMemoryFacts bodyCopyMemory bodyMemoryDefs stmtSimDeclMem
  localPtrsProps stmtSimDeclStore stmtSimDecl valueCopy valueCopyBytes
  exprOperandVar freshWrites valueTypingMemoryProps vyperTyping
  exprSimDefs stmtSimDefs venomState valueEncoding valueEncodingProofs
  intCallResult compileEnv exprLoweringProps loweringSlice exprLowering
  exprSimBufferStore words venomExecSemantics stmtLowering context
  fragExec fragExecMem allocaHistoryFragment list rich_list emitHelper
  emitHelperProps venomInst exprSimLiteralBuffer exprSimAlloc exprSimBuffer
  finite_map bodySimDeclCases allocLimits bodySim exprSimHyps
  vyperTypeSystem vyperTypeInvariants memoryLocalRhsProps
  supportedStmtTraverse supportedExprTraverse vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperInterpreter vyperState

Theorem body_decl_zero_gas_path:
  fn_has_code sa sb func /\ same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, same_blocks_def] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  drule_all run_inst_seq_gas_path_mem >> simp[]
QED

Theorem annassign_setup_body_gas_path_mem:
  declare_local ce id ty sa = (c,st) /\ ce.ce_alloca_locals /\
  lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP ce.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz) /\
  p = STRING #"%" (toString sa.cs_next_var) /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p] st = ((),sA) /\
  type_memory_bytes ce ty < dimword (:256) /\
  fn_has_code sa sA func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
  alloca_history func s /\ return_buf_frame d ce sa s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sA.cs_current_bb /\
    t.vs_inst_idx = LENGTH sA.cs_current_insts /\
    stmt_state_rel ctx func c cx es t /\ alloca_history func t /\
    return_buf_frame d c sA t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    local_ptrs_reserved c sA /\ not_fresh_at sA p /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes ce ty)) /\
    not_local_ptr c es.scopes p /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    ?w. lookup_var p t = SOME w /\
      FLOOKUP t.vs_allocas st.cs_next_id = SOME (w2n w,type_memory_bytes ce ty) /\
      w2n w + type_memory_bytes ce ty <= t.vs_alloca_next
Proof
  strip_tac >> drule_all annassign_setup_shape >> strip_tac >>
  `stmt_state_rel ctx func c cx es s` by metis_tac[stmt_state_rel_declare_local_entry] >>
  qabbrev_tac `A = mk_inst st.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes ce ty))] [p]` >>
  `A.inst_opcode = ALLOCA /\ A.inst_operands = [Lit (n2w (type_memory_bytes ce ty))] /\
   A.inst_outputs = [p] /\ A.inst_id = st.cs_next_id` by simp[Abbr `A`, mk_inst_def] >>
  drule_all body_decl_alloca_run >> strip_tac >>
  `sa.cs_next_var <= sA.cs_next_var` by (drule emit_inst_extends >> gvs[]) >>
  `return_buf_frame d c sA t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s`, `sa`] >> simp[]) >>
  `emitted_insts sa sA = [A] /\ same_blocks sa sA /\
   sA.cs_current_insts = sa.cs_current_insts ++ [A]` by
    (drule emit_inst_extends >> strip_tac >>
     gvs[emitted_insts_def, same_blocks_def, Abbr `A`, DROP_LENGTH_APPEND]) >>
  `run_inst_seq (emitted_insts sa sA) s = OK t` by
    (gvs[mk_inst_def] >> simp[run_inst_seq_def, step_inst_base_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sA) s` by
    (simp[run_inst_seq_mem_ok_last] >>
     irule instMemFrontierTheory.below_frontier_no_ranges >> simp[Abbr `A`, mk_inst_def]) >>
  `gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH sA.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists_tac `sa` >> simp[is_terminator_def]) >>
  `alloca_history func (t with vs_inst_idx := LENGTH sA.cs_current_insts)` by
    (irule body_store_memory_history >> simp[same_blocks_def, is_terminator_def] >>
     qexistsl_tac [`s`, `sa`] >> simp[is_terminator_def] >> fs[stmt_state_rel_def, same_blocks_def]) >>
  `t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `exec_alloca A s _ = OK t` mp_tac >>
     simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
     gvs[update_var_def]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sA.cs_current_insts` >>
  gvs[stmt_state_rel_inst_idx, same_blocks_def] >>
  conj_tac
  >- (Cases_on `d` >- fs[return_buf_frame_def] >>
      rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
      fs[return_buf_frame_def, lookup_var_def]) >>
  fs[lookup_var_def] >> rpt strip_tac >>
  first_x_assum irule >> strip_tac >> gvs[]
QED
