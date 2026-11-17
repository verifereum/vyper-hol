Theory dftPacketReturnRootSuccessor
Ancestors
  dftPacketTraceCallProvenance dftPacketReturnRootOccurrence
  gasFocusNativeRootReturn dftGasFromListTraceNames dftGasFromListTraceDefs
  dftGasFromListReadings dftCorrectness venomExecSemantics venomInst list rich_list arithmetic

Theorem dft_packet_return_root_successor:
  let T = trace_blocks [] 0 N C root_fn root_entry;
      L = trace_blocks ((e,c.inst_id)::a) e (N-e) C child ent
  in
    EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
      f.fn_blocks) C.ctx_functions /\
    EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) root_fn.fn_blocks /\
    call_h < j /\ j < LENGTH T /\
    EL call_h T = ((a,e,c.inst_id),parent,c,b0) /\
    EL j T = (((e,c.inst_id)::a,d,retinst.inst_id),child,retinst,s) /\
    c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME child /\
    eval_operands ops b0 = SOME args /\ setup_callee child args b0 = SOME ent /\
    run_blocks (N-e) C child ent = IntRet ir out /\
    MEM retinst.inst_opcode [RET;RETFMP;DRET] /\
    step_inst (N-d) C retinst s = IntRet ir out /\
    lookup_block b0.vs_current_bb parent.fn_blocks = SOME bb /\
    get_instruction bb b0.vs_inst_idx = SOME c /\
    bind_outputs c.inst_outputs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state b0 out)) = SOME post /\
    get_instruction bb (SUC b0.vs_inst_idx) = SOME next ==>
    j = call_h + LENGTH L /\ SUC j < LENGTH T /\
    EL (SUC j) T = ((a,e,next.inst_id),parent,next,
      post with vs_inst_idx := SUC b0.vs_inst_idx) /\
    trace_gas (TAKE (SUC j) T) = trace_gas (TAKE j T)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `SUC j < LENGTH root_trace` >>
  `ALL_DISTINCT (MAP FST root_trace)` by
    (unabbrev_all_tac >> irule (cj 3 trace_names_distinct) >> simp[]) >>
  `call_h < LENGTH root_trace` by decide_tac >>
  `MEM (((e,c.inst_id)::a,d,retinst.inst_id),child,retinst,s) root_trace` by
    metis_tac[MEM_EL] >>
  unabbrev_all_tac >>
  drule native_trace_blocks_call_provenance >>
  simp[frame_below_def] >> strip_tac >>
  `((a,e,c.inst_id),parent',c',b0') = ((a,e,c.inst_id),parent,c,b0)` by
    (drule all_distinct_map_mem_inj >> disch_then irule >>
     simp[] >> metis_tac[MEM_EL]) >>
  gnvs[] >>
  qpat_x_assum `MEM _ (trace_step _ _ _ _ _ _ _)` mp_tac >>
  simp[cj 1 trace_defs] >> strip_tac >>
  `retinst.inst_opcode <> INVOKE` by gvs[] >>
  `e + (N-e) - d = N-d` by decide_tac >>
  drule return_trace_blocks_endpoint >> simp[] >> strip_tac >>
  `call_h < LENGTH (trace_blocks [] 0 N C root_fn root_entry)` by decide_tac >>
  drule_all (SRULE [LET_THM] focus_native_root_return_accounting) >> strip_tac >>
  qmatch_goalsub_abbrev_tac `SUC j < LENGTH root_trace` >>
  qmatch_goalsub_abbrev_tac `j = call_h + LENGTH child_trace` >>
  `child_trace <> []` by (strip_tac >> gvs[]) >>
  `LAST (TAKE (call_h + SUC (LENGTH child_trace)) root_trace) =
    (((e,c.inst_id)::a,d,retinst.inst_id),child,retinst,s)` by
    simp[LAST_APPEND_NOT_NIL] >>
  `EL (call_h + LENGTH child_trace) root_trace =
    (((e,c.inst_id)::a,d,retinst.inst_id),child,retinst,s)` by
    (qpat_x_assum `LAST (TAKE _ _) = _` mp_tac >>
     simp[LAST_TAKE_EL, ADD_CLAUSES]) >>
  `j = call_h + LENGTH child_trace` by
    (`j < LENGTH (MAP FST root_trace) /\
      call_h + LENGTH child_trace < LENGTH (MAP FST root_trace)` by simp[] >>
     `EL j (MAP FST root_trace) =
      EL (call_h + LENGTH child_trace) (MAP FST root_trace)` by simp[EL_MAP] >>
     metis_tac[ALL_DISTINCT_EL_IMP]) >>
  `SUC j = call_h + SUC (LENGTH child_trace)` by decide_tac >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  `retinst.inst_opcode <> GAS` by gvs[] >>
  `TAKE (SUC j) root_trace = TAKE j root_trace ++ [EL j root_trace]` by
    simp[TAKE_SUC_BY_TAKE, SNOC_APPEND] >>
  qpat_x_assum `TAKE (SUC j) _ = _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[trace_gas_def, MAP_APPEND, FLAT_APPEND, MAP, FLAT] >>
  simp[visit_gas_def]
QED
