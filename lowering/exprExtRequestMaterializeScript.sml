(* Compiler-only allocation and copy segments for default materialization. *)
Theory exprExtRequestMaterialize
Ancestors
  exprExtRequestUnwrapAdapter exprExtRequestDefaultProbe
  exprExtRequestHistoryCompose exprExtRequestHistory exprExtRequestReadProbe
  exprSimAlloc exprLoweringProps exprSimProps fragGasSeq fragGasMode
  fragGasFresh freshWrites context compileEnv emitHelper emitHelperProps
  venomInst venomInstProofs venomExecSemantics venomState list rich_list
  arithmetic fragExec

Theorem extrequest_straight_run_path:
  fn_has_code sa sb func /\ same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb)
          (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  simp[gas_marked_path_def] >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[] >> disch_then irule >> fs[EVERY_MEM]
QED

Theorem extrequest_allocation_history:
  compile_alloc_buffer sz sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sz < dimword (:256) ==>
  ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx ee t /\
    extrequest_history_frame cenv cx ee sa s ee sb t /\
    eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ t.vs_memory = s.vs_memory /\
    (!aid b len. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv ee.scopes t name b len ==>
      regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p)
Proof
  strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `ci_mono sa sb` by
    (qspecl_then [`sz`, `sa`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >>
     gvs[ci_mono_def]) >>
  qexistsl_tac [`t`, `w`] >> simp[] >>
  simp[extrequest_history_frame_def, extrequest_read_frame_def] >>
  gvs[ci_mono_def] >> metis_tac[]
QED
