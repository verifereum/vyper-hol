(* Peel the initial allocation off the observed slot snapshot prefix. *)
Theory createSizeRawSlotBand
Ancestors
  copyExecution exprLowering emitHelperProps exprLoweringProps abiBufferAllocationCode
  stmtReasonLitFragMemory createMarkedPath fragGasOrigin fragFuel abiEncoderProps
  context compileEnv emitHelper fragExec venomWf loweringPosts
  gasEvents gasCount oracleExecProps venomInstIdsProps venomInstProofs venomExecProofs venomInstProofs1
  venomExecSemantics venomState venomInst loweringStateRelDefs
  list rich_list pair relation arithmetic pred_set

Theorem raw_slot_layout[local]:
  vv_location vv = SOME (slot_loc tr) /\
  compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,sm) /\
  compile_create_snapshot ce vv ty a = (snap,b) /\
  emit_op MLOAD [snap] b = (len,c) /\ fn_has_code a c func ==>
  b = slot_copy_final sm (vv_operand vv) buf.buf_operand
    ((type_memory_bytes ce ty + 31) DIV 32) (if tr then TLOAD else SLOAD) /\
  fn_has_code a sm func /\ fn_has_code sm b func /\ fn_has_code b c func
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `snap = buf.buf_operand /\
   b = slot_copy_final sm (vv_operand vv) buf.buf_operand
     ((type_memory_bytes ce ty + 31) DIV 32) (if tr then TLOAD else SLOAD)` by
    (Cases_on `tr` >>
     gvs[compile_create_snapshot_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, slot_loc_def, compile_slot_to_memory_shape, AllCaseEqs()]) >>
  `cs_extends a sm` by
    (Cases_on `emit_op ALLOCA [Lit (n2w (type_memory_bytes ce ty))] a` >>
     gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     metis_tac[ci_mono_def, ci_mono_emit_op, SND]) >>
  `cs_extends sm b /\ cs_extends b c` by
    metis_tac[slot_copy_extends, ci_mono_def, ci_mono_emit_op, SND] >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

Theorem raw_slot_loop_members[local]:
  fn_has_code sm (slot_copy_final sm src dst n load) func /\
  sm.cs_next_id <= id /\ id < sm.cs_next_id + 12 /\
  (load = SLOAD \/ load = TLOAD) ==>
  ?i. MEM i (fn_insts func) /\ i.inst_id = id /\
      i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE
Proof
  strip_tac >> drule slot_copy_lookup >> strip_tac >>
  `?i. (MEM i (slot_copy_init_insts sm) \/ MEM i (slot_copy_cond_insts sm n) \/
        MEM i (slot_copy_body_insts sm src dst load)) /\ i.inst_id = id /\
       i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE` by
    (Cases_on `load = SLOAD` >>
     gvs[slot_copy_init_insts_def, slot_copy_cond_insts_def, slot_copy_body_insts_def,
         mk_inst_def, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> decide_tac) >>
  qexists_tac `i` >> gvs[] >>
  irule lookup_block_fn_insts >>
  FIRST [qrefinel [`_`,`sm.cs_current_bb`] >> simp[] >> NO_TAC,
         qrefinel [`_`,`slot_copy_cond sm`] >> simp[] >> NO_TAC,
         qrefinel [`_`,`slot_copy_body sm`] >> fs[] >> NO_TAC]
QED

Theorem raw_slot_silent_edge[local]:
  lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME i /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  gas_origin_edge F explicit ctx func u ms (OK v) ==>
  ms = [] /\ v.vs_gas_readings = u.vs_gas_readings
Proof
  rw[gas_origin_edge_def, exit_result_def] >> gvs[gas_events_step_def] >>
  metis_tac[step_inst_noninvoke_gas_readings, gas_count_phis_ok]
QED

Theorem raw_slot_silent_rtc[local]:
  !p q. RTC (create_marked_edge E) p q ==>
    (!u ms v. E u ms v ==> ms = [] /\ v.vs_gas_readings = u.vs_gas_readings) ==>
    SND q = SND p /\ (FST q).vs_gas_readings = (FST p).vs_gas_readings
Proof
  ho_match_mp_tac RTC_INDUCT >>
  simp[FORALL_PROD, create_marked_edge_def] >> metis_tac[APPEND_NIL]
QED

Theorem raw_slot_alloc_edge[local]:
  lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME i /\
  i.inst_opcode = ALLOCA /\ gas_origin_edge F explicit ctx func u ms (OK x) ==>
  x.vs_current_bb = u.vs_current_bb /\ x.vs_inst_idx = SUC u.vs_inst_idx /\
  run_inst_seq [i] u = OK (x with vs_inst_idx := u.vs_inst_idx)
Proof
  strip_tac >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by simp[is_terminator_def] >>
  `?t. step_inst_base i u = OK t /\ x = t with vs_inst_idx := SUC u.vs_inst_idx` by
    (qpat_x_assum `gas_origin_edge _ _ _ _ _ _ _` mp_tac >>
     rw[gas_origin_edge_def] >> gvs[exit_result_def, step_inst_non_invoke, is_terminator_def] >>
     metis_tac[exit_result_def]) >>
  `t.vs_inst_idx = u.vs_inst_idx` by metis_tac[step_inst_base_preserves_inst_idx] >>
  `t.vs_current_bb = u.vs_current_bb` by metis_tac[step_inst_base_preserves_all] >>
  gvs[run_inst_seq_def] >>
  qpat_x_assum `t.vs_inst_idx = u.vs_inst_idx` (rewrite_tac o single o SYM) >> simp[]
QED

Theorem create_raw_snapshot_slot_band:
  vv_location vv = SOME (slot_loc tr) /\
  compile_create_snapshot ce vv ty a = (snap,b) /\
  emit_op MLOAD [snap] b = (len,c) /\ fn_has_code a c func /\
  fn_inst_ids_distinct func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = LENGTH b.cs_current_insts /\
  (!p ms q. E p ms q ==>
    (p.vs_current_bb <> b.cs_current_bb \/ p.vs_inst_idx <> LENGTH b.cs_current_insts) /\
    ?bb i. lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
           get_instruction bb p.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids a b /\
           gas_origin_edge F explicit ctx func p ms (OK q)) /\
  RTC (create_marked_edge E) (u,[]) (z,marks) ==>
  ?buf sm x exit.
    compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,sm) /\
    fn_has_code sm b func /\
    lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
    phi_prefix_length exit.bb_instructions = 0 /\
    x.vs_current_bb = sm.cs_current_bb /\ x.vs_inst_idx = LENGTH sm.cs_current_insts /\
    z.vs_inst_idx = 0 /\
    run_inst_seq (emitted_insts a sm) u = OK (x with vs_inst_idx := u.vs_inst_idx) /\
    RTC (\v w. (v.vs_current_bb <> b.cs_current_bb \/ v.vs_inst_idx <> 0) /\
               ?ms. gas_origin_edge F explicit ctx func v ms (OK w)) x z /\
    marks = [] /\ z.vs_gas_readings = u.vs_gas_readings
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce ty) a` >>
  rename1 `_ = (buf,sm)` >>
  drule_all raw_slot_layout >> strip_tac >>
  drule compile_alloc_buffer_code >> strip_tac >>
  drule_all fn_has_code_code >> strip_tac >>
  `?exit. lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
          phi_prefix_length exit.bb_instructions = 0` by
    (fs[fn_has_code_def] >> metis_tac[lookup_block_MEM]) >>
  `b.cs_current_insts = [] /\ b.cs_next_id = sm.cs_next_id + 12` by
    simp[slot_copy_final_def] >>
  `?i. MEM i (fn_insts func) /\ i.inst_id = a.cs_next_id /\ i.inst_opcode = ALLOCA /\
       get_instruction bb u.vs_inst_idx = SOME i /\ emitted_insts a sm = [i]` by
    (qexists_tac `HD (emitted_insts a sm)` >> fs[mk_inst_def] >>
     Cases_on `DROP (LENGTH a.cs_current_insts) bb.bb_instructions` >>
     gvs[] >> drule DROP_EQ_CONS >> simp[get_instruction_def]) >>
  rename1 `emitted_insts a sm = [alloc]` >>
  `!p ms q. E p ms q ==> ms = [] /\ q.vs_gas_readings = p.vs_gas_readings` by
    (rpt gen_tac >> disch_tac >> first_x_assum drule >>
     disch_then (CONJUNCTS_THEN2 assume_tac
       (qx_choose_then `blk` (qx_choose_then `i` (map_every assume_tac o CONJUNCTS)))) >>
     `MEM i (fn_insts func)` by metis_tac[lookup_block_get_instruction_fn_insts] >>
     `i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE` by
       (Cases_on `i.inst_id = a.cs_next_id`
        >- (`i = alloc` by metis_tac[fn_inst_ids_distinct_inj] >> simp[]) >>
        `sm.cs_next_id <= i.inst_id /\ i.inst_id < sm.cs_next_id + 12` by
          (fs[frag_ids_def] >> decide_tac) >>
        qpat_x_assum `b = _` (fn th => fs[th]) >>
        Cases_on `tr` >> gvs[] >>
        drule raw_slot_loop_members >>
        disch_then (qspec_then `i.inst_id` mp_tac) >> simp[] >>
        metis_tac[fn_inst_ids_distinct_inj]) >>
     metis_tac[raw_slot_silent_edge]) >>
  `marks = [] /\ z.vs_gas_readings = u.vs_gas_readings` by
    (drule raw_slot_silent_rtc >> simp[] >> metis_tac[]) >>
  (* The two boundary fetches cannot share a cursor: ALLOCA vs MLOAD. *)
  `u <> z` by
    (drule emitted_insts_emit_op >> strip_tac >>
     `c.cs_current_bb = b.cs_current_bb` by
       gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
           fresh_id_def, emit_def, comp_return_def] >>
     `?j. get_instruction exit z.vs_inst_idx = SOME j /\ j.inst_opcode = MLOAD` by
       (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
        simp[get_instruction_def, EL_APPEND_EQN, mk_inst_def]) >>
     strip_tac >> gvs[]) >>
  qpat_x_assum `RTC _ (u,[]) (z,marks)`
    (mp_tac o ONCE_REWRITE_RULE [RTC_CASES1]) >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choose_then `mid` (map_every assume_tac o CONJUNCTS)))
  >- fs[] >>
  PairCases_on `mid` >>
  qpat_x_assum `create_marked_edge E _ _`
    (strip_assume_tac o REWRITE_RULE [create_marked_edge_def, APPEND]) >>
  rename1 `E u ms x` >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `gas_origin_edge F explicit ctx func u ms (OK x)` by metis_tac[] >>
  drule_all raw_slot_alloc_edge >> strip_tac >>
  qexistsl_tac [`buf`,`sm`,`x`,`exit`] >> simp[ADD1] >>
  `!p q. RTC (create_marked_edge E) p q ==>
    RTC (\v w. (v.vs_current_bb <> b.cs_current_bb \/ v.vs_inst_idx <> 0) /\
               ?ms. gas_origin_edge F explicit ctx func v ms (OK w)) (FST p) (FST q)`
    suffices_by (disch_then drule >> simp[]) >>
  ho_match_mp_tac RTC_INDUCT >> simp[FORALL_PROD, create_marked_edge_def] >>
  rpt strip_tac >> irule (cj 2 RTC_RULES) >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  qpat_assum `!p ms q. E p ms q ==> _ /\ ?bb i. _` drule >> simp[] >> metis_tac[]
QED
