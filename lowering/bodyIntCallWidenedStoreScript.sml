Theory bodyIntCallWidenedStore
Ancestors
  bodyIntCallStoreRun bodyIntCallStorePost bodyIntCallReturnLayout
  intCallResult compileEnv exprLoweringProps venomState venomMemDefs
  finite_map list rich_list valueTypingMemoryProps exprSimProps fragGasSeq
  fragGasPath fragExec

(* Keep the allocation witness rather than consuming it in vv_at. *)
Theorem stack_buffer_run_owned:
  store_multi_results buf.buf_operand results 0 si = ((),sb) /\
  local_ptrs_reserved ce si /\
  buf.buf_operand = Var p /\ not_fresh_at si p /\
  (!x. MEM (Var x) results ==> not_fresh_at si x) /\
  evaluate_type (get_tenv cx) cty = SOME tv /\ value_has_type tv v /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name)) cty /\
  intret_vals_match tv v ws /\ ws <> [] /\
  stmt_state_rel ctx func ce cx es' s /\ wb_frame ce es0 es' sa s0 s /\
  sa.cs_next_var <= si.cs_next_var /\
  eval_operand buf.buf_operand s = SOME w /\
  MAP (\op. eval_operand op s) results = MAP SOME ws /\
  w2n w + 32 * LENGTH results < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n w,32 * LENGTH results) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  val_footprint tv v <= 32 * LENGTH results /\
  (!n lb lsz. local_region ce es'.scopes s n lb lsz ==>
    w2n w + 32 * LENGTH results <= lb \/ lb + lsz <= w2n w) /\
  (!n lb lsz. local_region ce es0.scopes s0 n lb lsz ==>
    local_region ce es'.scopes s n lb lsz) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint (w2n w) (32 * LENGTH results) off
      (type_memory_size itv)) ==>
  ?u. run_inst_seq (emitted_insts si sb) s = OK u /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    stmt_state_rel ctx func ce cx es' u /\ wb_frame ce es0 es' sa s0 u /\
    eval_operand buf.buf_operand u = SOME w /\
    val_in_memory tv v (w2n w) u.vs_memory /\
    FLOOKUP u.vs_allocas aid = SOME (w2n w,32 * LENGTH results) /\
    (!n lb lsz. local_region ce es'.scopes u n lb lsz ==>
      w2n w + 32 * LENGTH results <= lb \/ lb + lsz <= w2n w)
Proof
  strip_tac >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at si x` by simp[] >>
  drule store_multi_results_run >>
  disch_then (qspecl_then [`s`,`w2n w`,`ws`] mp_tac) >>
  simp[] >> strip_tac >> rename1 `run_inst_seq _ s = OK u` >>
  `u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `u with <|vs_memory := _; vs_vars := _|> = s`
      (mp_tac o Q.AP_TERM `\z:venom_state. z.vs_allocas`) >> simp[]) >>
  `eval_operand buf.buf_operand u = SOME w` by gvs[eval_operand_def] >>
  `stmt_state_rel ctx func ce cx es' u` by
    (irule owned_memory_tail_state_rel >>
     qexistsl_tac [`w2n w`,`s`,`si`,`32 * LENGTH results`] >>
     simp[] >> rpt conj_tac >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `val_in_memory tv v (w2n w) u.vs_memory` by
    (irule stack_results_val_in_memory >> conj_tac
     >- (qexists_tac `get_tenv cx` >> irule stack_return_value_layout >>
         goal_assum (drule_at Any) >> simp[]) >>
     simp[] >> qexists_tac `ws` >> simp[] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `wb_frame ce es0 es' sa s0 u` by
    (irule wb_frame_owned_memory_tail >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`aid`,`w2n w`,`si`,`32 * LENGTH results`] >>
     fs[stmt_state_rel_def] >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  `local_region ce es'.scopes s n lb lsz` by
    (irule local_region_frame >> conj_tac
     >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`si`,`es'.scopes`,`u`] >> simp[]) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

(* Count the concrete run without committing its endpoint to an expression post. *)
Theorem store_run_counted_endpoint:
  store_multi_results buf ops 0 si = ((),sb) /\
  fn_has_code si sb func /\ ~s.vs_halted /\
  s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts /\
  run_inst_seq (emitted_insts si sb) s = OK u /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s ==>
  gas_path ctx func s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts si sb)))
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  u.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule store_multi_results_shape >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def, same_blocks_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts si sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX sb.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >> simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`,`func`,`bb`] mp_tac) >> simp[] >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `u with <|vs_vars := _; vs_memory := _|> = s`
      (mp_tac o Q.AP_TERM `\z:venom_state. z.vs_current_bb`) >> simp[]) >>
  gvs[same_blocks_def]
QED
