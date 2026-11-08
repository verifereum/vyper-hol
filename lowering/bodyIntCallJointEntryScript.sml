(* Count and initialize the actual semantic/resource prologue landing. *)
Theory bodyIntCallJointEntry
Ancestors
  bodyIntCallRootFrame fragGasSeq intCallCallee emitHelperProps
  fragExec exprLoweringProps entrySinkExtraction list rich_list

Theorem internal_prologue_counted_landing:
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,rpc),st1) /\
  fn_has_code st0 st1 func /\ ~s.vs_halted /\
  s.vs_current_bb = st0.cs_current_bb /\
  s.vs_inst_idx = LENGTH st0.cs_current_insts /\
  run_inst_seq (emitted_insts st0 st1) s = OK u ==>
  gas_path ctx func s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st0 st1)))
    (OK (u with vs_inst_idx := LENGTH st1.cs_current_insts)) /\
  ~u.vs_halted /\ u.vs_current_bb = st1.cs_current_bb
Proof
  strip_tac >> drule compile_internal_prologue_shape >> strip_tac >>
  `emitted_insts st0 st1 = new` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX st1.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts st0 st1) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st1.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`,`func`,`bb`] mp_tac) >> simp[] >> strip_tac >>
  metis_tac[run_inst_seq_preserves_entry_control]
QED
