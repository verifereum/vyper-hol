Theory gasFocusNativeRootReturn
Ancestors
  dftPacketNativeContinuation dftPacketReturnNative dftGasFromListReadings
  dftGasFromListTraceDefs venomExecSemantics venomInst list rich_list arithmetic

Theorem focus_native_root_return_accounting:
  let T = trace_blocks [] 0 root_fuel C root_fn root_entry;
      child_trace = trace_blocks ((e,c.inst_id)::a) e (root_fuel-e) C child ent;
      v = ((a,e,c.inst_id),parent,c,b0);
      resumed = j + SUC (LENGTH child_trace)
  in
    j < LENGTH T /\ EL j T = v /\
    lookup_block b0.vs_current_bb parent.fn_blocks = SOME bb /\
    get_instruction bb b0.vs_inst_idx = SOME c /\
    c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME child /\
    eval_operands ops b0 = SOME args /\ setup_callee child args b0 = SOME ent /\
    run_blocks (root_fuel-e) C child ent = IntRet ir child_out /\
    bind_outputs c.inst_outputs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME post /\
    get_instruction bb (SUC b0.vs_inst_idx) = SOME next ==>
    resumed < LENGTH T /\
    EL resumed T = ((a,e,next.inst_id),parent,next,
      post with vs_inst_idx := SUC b0.vs_inst_idx) /\
    TAKE resumed T = TAKE j T ++ [v] ++ child_trace /\
    trace_gas (TAKE resumed T) = trace_gas (TAKE j T) ++ trace_gas child_trace
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all native_trace_blocks_continuation >> strip_tac >>
  gvs[] >>
  drule_all dft_packet_native_return_concat >> strip_tac >>
  drule_all dft_packet_native_return_next >>
  disch_then (qspecl_then [`parent`, `e`, `a`] strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `j + SUC (LENGTH child_trace)` >>
  qmatch_goalsub_abbrev_tac `j + SUC (LENGTH child_trace) < LENGTH root_trace` >>
  qmatch_asmsub_abbrev_tac `DROP j root_trace = block_trace ++ rest` >>
  `root_trace = TAKE j root_trace ++ block_trace ++ rest` by
    (qspecl_then [`j`, `root_trace`] mp_tac listTheory.TAKE_DROP >>
     pure_asm_rewrite_tac[APPEND_ASSOC] >> metis_tac[]) >>
  `LENGTH (TAKE j root_trace) = j` by simp[LENGTH_TAKE] >>
  `j + SUC (LENGTH child_trace) < LENGTH root_trace` by
    (`LENGTH (DROP j root_trace) = LENGTH block_trace + LENGTH rest` by
       (pure_asm_rewrite_tac[LENGTH_APPEND] >> REFL_TAC) >> fs[] >> decide_tac) >>
  conj_tac >- simp[] >>
  conj_tac >- (qpat_x_assum `root_trace = _` SUBST1_TAC >> simp[EL_APPEND]) >>
  `TAKE (j + SUC (LENGTH child_trace)) root_trace =
    TAKE j root_trace ++ [((a,e,c.inst_id),parent,c,b0)] ++ child_trace` by
    (qpat_x_assum `root_trace = _` (fn th => once_rewrite_tac[th]) >>
     simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG, TAKE_TAKE_MIN, SUB_PLUS, MIN_DEF,
          Abbr `block_trace`, Abbr `child_trace`]) >>
  simp[visit_gas_def]
QED
