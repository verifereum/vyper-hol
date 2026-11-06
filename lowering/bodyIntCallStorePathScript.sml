Theory bodyIntCallStorePath
Ancestors
  bodyIntCallStoreRun fragGasSeq exprSimVVFrame intCallResult
  fragExec emitHelperProps exprLoweringProps list rich_list

Theorem store_run_counted_post:
  store_multi_results buf ops 0 si = ((),sb) /\
  fn_has_code si sb func /\ ~s.vs_halted /\
  s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts /\
  run_inst_seq (emitted_insts si sb) s = OK u /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  vv_post ctx func ce cx e es0 sa sb s0 es' raw vv u ==>
  ?out. gas_path ctx func s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts si sb))) (OK out) /\
    vv_post ctx func ce cx e es0 sa sb s0 es' raw vv out /\
    ~out.vs_halted /\ out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule store_multi_results_shape >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def, same_blocks_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts si sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX sb.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`,`func`,`bb`] mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts si sb)` >>
  simp[] >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (conj_tac
     >- (qpat_assum `u with <|vs_vars := _; vs_memory := _|> = s`
           (mp_tac o Q.AP_TERM `\z:venom_state. z.vs_halted`) >> simp[]) >>
     qpat_assum `u with <|vs_vars := _; vs_memory := _|> = s`
       (mp_tac o Q.AP_TERM `\z:venom_state. z.vs_current_bb`) >> simp[]) >>
  gvs[same_blocks_def]
QED
