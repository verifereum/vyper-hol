(* Read fixed, silent instruction sequences from the supplied marked path. *)
Theory createSizeRawStraightBands
Ancestors
  createMarkedPath fragGasOrigin gasEvents oracleExecProps fragExec
  venomExecSemantics venomInst venomState venomInstProofs1 venomInstProofs
  instIdxIndep exprLowering exprLoweringProps emitHelper emitHelperProps
  abiBufferAllocationCode exprSimCopy context compileEnv
  relation pair list rich_list arithmetic

Theorem raw_band_origin_step[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ~is_terminator i.inst_opcode /\
  gas_origin_edge F explicit ctx fn s ms (OK t) ==>
  ?m. step_inst_base i s = OK m /\
      t = (m with vs_inst_idx := SUC s.vs_inst_idx) /\
      m.vs_current_bb = s.vs_current_bb /\ m.vs_gas_readings = s.vs_gas_readings /\
      ms = []
Proof
  rw[gas_origin_edge_def] >>
  gvs[step_inst_non_invoke, exit_result_def, Once gas_events_step_def]
  >- (drule_all step_inst_base_preserves_all >>
      drule_all step_inst_base_gas_readings >> simp[]) >>
  qpat_x_assum `OK _ = step_inst_base _ _` (assume_tac o SYM) >>
  fs[exit_result_def]
QED

Theorem raw_band_from_fetch[local]:
  !code s acc.
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                 ~is_terminator i.inst_opcode) code /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = code ++ rest /\
    s.vs_current_bb = t.vs_current_bb /\
    s.vs_inst_idx + LENGTH code = t.vs_inst_idx /\
    (!p ms q. E p ms q ==>
       (p.vs_current_bb <> t.vs_current_bb \/ p.vs_inst_idx <> t.vs_inst_idx) /\
       gas_origin_edge F explicit ctx fn p ms (OK q)) /\
    RTC (create_marked_edge E) (s,acc) (t,marks) ==>
    run_inst_seq code s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    marks = acc /\ t.vs_gas_readings = s.vs_gas_readings
Proof
  Induct >> rpt gen_tac >> simp[] >> strip_tac
  >- (qpat_x_assum `RTC _ _ _` (mp_tac o ONCE_REWRITE_RULE [RTC_CASES1]) >>
      simp[EXISTS_PROD, create_marked_edge_def, run_inst_seq_def] >> metis_tac[]) >>
  `s <> t` by (strip_tac >> gvs[] >> decide_tac) >>
  `?mid ms. E s ms mid /\ RTC (create_marked_edge E) (mid,acc ++ ms) (t,marks)` by
    (qpat_x_assum `RTC _ _ _` (mp_tac o ONCE_REWRITE_RULE [RTC_CASES1]) >>
     simp[EXISTS_PROD, create_marked_edge_def, PULL_EXISTS] >> metis_tac[]) >>
  drule DROP_EQ_CONS >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by simp[get_instruction_def] >>
  qpat_x_assum `!p ms q. E p ms q ==> _`
    (fn th => assume_tac th >> drule th >> strip_tac) >>
  drule_all raw_band_origin_step >> strip_tac >> gvs[] >>
  qpat_x_assum `!s acc. _ ==> run_inst_seq code s = _ /\ _`
    (qspecl_then [`m with vs_inst_idx := SUC s.vs_inst_idx`, `acc`] mp_tac) >>
  (impl_tac >- (simp[ADD_CLAUSES] >> metis_tac[])) >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  qmatch_asmsub_abbrev_tac `run_inst_seq code next` >>
  `next with vs_inst_idx := m.vs_inst_idx = m` by simp[Abbr `next`] >>
  qspecl_then [`code`, `next`, `m.vs_inst_idx`] mp_tac run_inst_seq_inst_idx >>
  `m.vs_inst_idx = s.vs_inst_idx` by metis_tac[step_inst_base_preserves_inst_idx] >>
  asm_rewrite_tac[] >> simp[run_inst_seq_def, exec_result_map_def, Abbr `next`]
QED

Theorem raw_band_embedded[local]:
  fn_has_code a b fn /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode) (emitted_insts a b) /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  (!p ms q. E p ms q ==>
       (p.vs_current_bb <> b.cs_current_bb \/ p.vs_inst_idx <> LENGTH b.cs_current_insts) /\
       gas_origin_edge F explicit ctx fn p ms (OK q)) /\
  RTC (create_marked_edge E) (s,[]) (t,marks) ==>
  run_inst_seq (emitted_insts a b) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
  marks = [] /\ t.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >>
  `?bb rest. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       bb.bb_instructions =
         a.cs_current_insts ++ (emitted_insts a b ++ rest)` by
    (qpat_x_assum `fn_has_code a b fn` mp_tac >>
     simp[fn_has_code_def, IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  irule raw_band_from_fetch >> simp[] >>
  qexistsl_tac [`E`, `bb`, `ctx`, `explicit`, `fn`, `rest`] >>
  simp[DROP_APPEND, DROP_LENGTH_NIL] >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!p ms q. E p ms q ==> _` drule >> simp[]) >>
  qmatch_goalsub_abbrev_tac `DROP n rest` >>
  `n = 0` by (simp[Abbr `n`] >> decide_tac) >> simp[]
QED

Theorem raw_snapshot_memory_code[local]:
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  compile_create_snapshot ce vv ty a = (snap,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode) (emitted_insts a b)
Proof
  strip_tac >> qpat_x_assum `compile_create_snapshot _ _ _ _ = _` mp_tac >>
  simp[compile_create_snapshot_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> simp[] >>
  simp[compile_copy_memory_dynamic_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  drule compile_alloc_buffer_code >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND, DROP_LENGTH_NIL, iterateTheory.ADD_SUBR2,
       mk_inst_def, is_terminator_def]
QED

Theorem raw_snapshot_immutable_code[local]:
  vv_location vv = SOME LocCode /\
  compile_create_snapshot ce vv ty a = (snap,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode) (emitted_insts a b)
Proof
  strip_tac >> qpat_x_assum `compile_create_snapshot _ _ _ _ = _` mp_tac >>
  simp[compile_create_snapshot_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  drule compile_alloc_buffer_code >> strip_tac >>
  rename1 `compile_alloc_buffer _ _ = (tmp,mid)` >>
  qmatch_asmsub_abbrev_tac `compile_imm_copy_to_memory _ _ _ _ n 0 mid` >>
  `compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca
     (vv_operand vv) tmp.buf_operand n 0 mid = ((),b)` by
    (Cases_on `compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca
       (vv_operand vv) tmp.buf_operand n 0 mid` >> gvs[]) >>
  `?is. same_blocks mid b /\ b.cs_current_insts = mid.cs_current_insts ++ is /\
    EVERY (\i. MEM i.inst_opcode [ADD; DLOAD; ILOAD; MSTORE]) is` by
    (Cases_on `ce.ce_is_ctor` >> gvs[]
     >- (drule code_ctor_copy_insts >> simp[EVERY_MEM] >> metis_tac[])
     >> drule code_copy_insts >> simp[EVERY_MEM] >> metis_tac[]) >>
  gvs[same_blocks_def] >>
  simp[emitted_insts_def, DROP_APPEND, DROP_LENGTH_NIL, iterateTheory.ADD_SUBR2,
       mk_inst_def, is_terminator_def] >>
  fs[EVERY_MEM] >> rpt gen_tac >> disch_tac >>
  qpat_x_assum `!i. MEM i is ==> _` drule >>
  disch_then strip_assume_tac >> simp[is_terminator_def]
QED

Theorem raw_band_scalar[local]:
  emit_op opc args a = (out,b) /\ opc <> GAS /\ opc <> INVOKE /\ ~is_terminator opc /\
  fn_has_code a b fn /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  (!p ms q. E p ms q ==>
       (p.vs_current_bb <> b.cs_current_bb \/ p.vs_inst_idx <> LENGTH b.cs_current_insts) /\
       gas_origin_edge F explicit ctx fn p ms (OK q)) /\
  RTC (create_marked_edge E) (s,[]) (t,marks) ==>
  run_inst_seq (emitted_insts a b) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
  marks = [] /\ t.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >> drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  irule raw_band_embedded >> fs[same_blocks_def, mk_inst_def] >> metis_tac[]
QED

Theorem create_raw_snapshot_straight_bands:
  compile_create_snapshot ce vv ty a = (snap,b) /\
  emit_op MLOAD [snap] b = (len,c) /\ emit_op ADD [snap; Lit 32w] c = (data,d) /\
  fn_has_code a b fn /\ fn_has_code b c fn /\ fn_has_code c d fn /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = LENGTH b.cs_current_insts /\
  l.vs_current_bb = c.cs_current_bb /\ l.vs_inst_idx = LENGTH c.cs_current_insts /\
  r.vs_current_bb = d.cs_current_bb /\ r.vs_inst_idx = LENGTH d.cs_current_insts /\
  (!p ms q. ES p ms q ==>
       (p.vs_current_bb <> b.cs_current_bb \/ p.vs_inst_idx <> LENGTH b.cs_current_insts) /\
       gas_origin_edge F explicit ctx fn p ms (OK q)) /\
  (!p ms q. length_edge p ms q ==>
       (p.vs_current_bb <> c.cs_current_bb \/ p.vs_inst_idx <> LENGTH c.cs_current_insts) /\
       gas_origin_edge F explicit ctx fn p ms (OK q)) /\
  (!p ms q. ED p ms q ==>
       (p.vs_current_bb <> d.cs_current_bb \/ p.vs_inst_idx <> LENGTH d.cs_current_insts) /\
       gas_origin_edge F explicit ctx fn p ms (OK q)) /\
  RTC (create_marked_edge ES) (u,[]) (z,msS) /\
  RTC (create_marked_edge length_edge) (z,[]) (l,msL) /\
  RTC (create_marked_edge ED) (l,[]) (r,msD) ==>
  (run_inst_seq (emitted_insts b c) z = OK (l with vs_inst_idx := z.vs_inst_idx) /\
   msL = [] /\ l.vs_gas_readings = z.vs_gas_readings) /\
  (run_inst_seq (emitted_insts c d) l = OK (r with vs_inst_idx := l.vs_inst_idx) /\
   msD = [] /\ r.vs_gas_readings = l.vs_gas_readings) /\
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/
    vv_location vv = SOME LocCode) ==>
   run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx) /\
   run_inst_seq (emitted_insts a c) u = OK (l with vs_inst_idx := u.vs_inst_idx) /\
   msS = [] /\ z.vs_gas_readings = u.vs_gas_readings)
Proof
  strip_tac >> conj_asm1_tac
  >- (irule raw_band_scalar >> simp[] >> conj_tac
      >- (qexistsl_tac [`[snap]`,`MLOAD`,`len`] >> simp[is_terminator_def]) >>
      qexistsl_tac [`length_edge`,`ctx`,`explicit`,`fn`] >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule raw_band_scalar >> simp[] >> conj_tac
      >- (qexistsl_tac [`[snap; Lit 32w]`,`ADD`,`data`] >> simp[is_terminator_def]) >>
      qexistsl_tac [`ED`,`ctx`,`explicit`,`fn`] >> simp[] >> metis_tac[]) >>
  strip_tac >>
  `b.cs_current_bb = a.cs_current_bb /\
   b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                ~is_terminator i.inst_opcode) (emitted_insts a b)` by
    metis_tac[raw_snapshot_memory_code, raw_snapshot_immutable_code] >>
  `run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx) /\
   msS = [] /\ z.vs_gas_readings = u.vs_gas_readings` by
    (irule raw_band_embedded >> simp[] >>
     qexistsl_tac [`ES`,`ctx`,`explicit`,`fn`] >> fs[] >> metis_tac[]) >>
  drule (Q.SPEC `MLOAD` emit_op_extends) >> strip_tac >>
  `emitted_insts a c = emitted_insts a b ++ emitted_insts b c` by
    metis_tac[emitted_insts_append] >>
  drule run_inst_seq_append >>
  disch_then (qspec_then `emitted_insts b c` assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts b c)` by
    (drule (Q.SPEC `MLOAD` emitted_insts_emit_op) >> simp[mk_inst_def, is_terminator_def]) >>
  fs[run_inst_seq_inst_idx, exec_result_map_def]
QED
