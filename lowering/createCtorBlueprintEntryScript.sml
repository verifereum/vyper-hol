(* Constructor payload allocation for nonraw blueprint creation. *)
Theory createCtorBlueprintEntry
Ancestors
  bodyFullAllocaFresh bodyFullExtCallDirectState bodyFullHashKeccakFixed
  abiBufferAllocationCode exprSimAlloc externalReturnFootprint stateRelProj
  exprSimProps exprLoweringProps fragGasOriginPtr fragGasOrigin fragExec
  bodyPtrDefs loweringPosts loweringStateRelDefs ptrDiscipline
  venomMemDefs venomState venomInst venomExecSemantics frameGasEvents
  compileEnv context finite_map arithmetic list words
Libs horizonTypeLib

Theorem ctor_encoder_blueprint_entry:
  compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  capacity < dimword (:256) /\
  (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts ==>
  ?root pbase u Gu tu inst.
    buf.buf_operand = Var root /\
    inst = mk_inst se.cs_next_id ALLOCA [Lit (n2w capacity)] [root] /\
    MEM inst (fn_insts func) /\ not_local_ptr ce ee.scopes root /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase capacity root root 0 [] a u Gu tu /\
    u.vs_memory = s.vs_memory /\
    (!x. not_fresh_at se x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
    (!ms v. gas_origin_edge F explicit ctx func s ms (OK v) ==> ms = [] /\ v = u)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `hz` (drule_then strip_assume_tac)) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  drule_all (horizonTypeLib.at_horizon alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`root`,`w`,`u`,`Gu`,`tu`,`r`] strip_assume_tac)) >>
  drule compile_alloc_buffer_code >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `root = STRING #"%" (toString se.cs_next_var)` by fs[] >>
  qabbrev_tac `inst = mk_inst se.cs_next_id ALLOCA [Lit (n2w capacity)] [root]` >>
  `MEM inst (fn_insts func) /\ not_local_ptr ce ee.scopes root` by
    (simp[Abbr `inst`] >> irule local_ptrs_reserved_fresh >> qexists_tac `se` >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_halted = s.vs_halted` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _;
       vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id (w2n w) capacity root root 0 [] a u Gu tu` by suspend "state" >>
  `!ms v. gas_origin_edge F explicit ctx func s ms (OK v) ==> ms = [] /\ v = u` by
    suspend "arrival" >>
  qexistsl_tac [`root`,`w2n w`,`u`,`Gu`,`tu`,`inst`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[Abbr `inst`]
QED

Resume ctor_encoder_blueprint_entry[state]:
  rewrite_tac[abi_encode_saved_state_def] >>
  conj_tac >- suspend "horizon" >>
  conj_tac >- (rewrite_tac[wb_frame_def] >>
    `locals_kept ce ee ee s u` by (irule locals_kept_regions >> simp[]) >>
    metis_tac[]) >>
  conj_tac >- (irule alloc_buffer_ghost_kept_at >>
    qexistsl_tac [`G`,`w2n w + capacity`,`s`,`tn`] >>
    drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
    rpt conj_tac
    >- (rpt strip_tac >> qpat_assum `!x. not_fresh_at se x ==> _`
          (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)
    >- (rpt strip_tac >> irule return_local_region_frontier >> metis_tac[])
    >- (fs[alloca_inv_def,alloca_next_valid_def] >> rpt strip_tac >>
        qpat_assum `!aid base sz. FLOOKUP s.vs_allocas aid = _ ==> _` irule >>
        goal_assum (drule_at Any))
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >> simp[ghost_kept_at_def]) >>
  simp_tac (srw_ss()) [ADD_CLAUSES,SUB_0,LENGTH] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[eval_operand_def,read_memory_def]
QED

Resume ctor_encoder_blueprint_entry[horizon]:
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac >- (qpat_assum `!H'. stmt_state_rel H' _ _ _ _ _ s ==> _` irule >>
    first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule (horizonTypeLib.at_horizon_named "H" alloc_buffer_ghost_inv_at) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `ghost_inv_at (DF H) _ _ _ _ _ _ _ s` (irule_at Any) >>
  qpat_assum `stmt_state_rel H _ _ _ _ _ s` (irule_at Any) >>
  qpat_assum `local_ptrs_reserved ce se` (irule_at Any) >>
  qexists_tac `w2n w + capacity` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> qpat_assum `!x. not_fresh_at se x ==> _` (drule_then strip_assume_tac) >>
  first_assum ACCEPT_TAC
QED

Resume ctor_encoder_blueprint_entry[arrival]:
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    (mp_tac (Q.SPECL [`se`,`a`,`func`,`[inst]`] fn_has_code_same_block) >>
     simp[Abbr `inst`] >> disch_then (qx_choose_then `bb` strip_assume_tac) >>
     qexists_tac `bb` >> simp[] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base inst s = OK r` by
    (`emitted_insts se a = [inst]` by simp[Abbr `inst`] >>
     qpat_assum `emitted_insts se a = [inst]` (fn th =>
       qpat_assum `run_inst_seq _ _ = _` (mp_tac o REWRITE_RULE [th])) >>
     Cases_on `step_inst_base inst s` >> simp[run_inst_seq_def]) >>
  rpt gen_tac >> simp_tac bool_ss [gas_origin_edge_def] >> strip_tac >>
  gvs[Abbr `inst`,mk_inst_def,is_terminator_def,step_inst_non_invoke,
      frameGasEventsTheory.gas_events_step_plain,SUC_ONE_ADD,exit_result_def]
QED

Finalise ctor_encoder_blueprint_entry
