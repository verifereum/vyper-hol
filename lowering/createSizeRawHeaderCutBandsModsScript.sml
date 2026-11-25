(* Recover the silent snapshot and scalar runs at the observed raw header cuts. *)
Theory createSizeRawHeaderCutBandsMods
Ancestors
  bodyFullIfExpReach bodyFullPostsMods createSizePrefixReplay
  createSizeRawStraightBands createSizeRawSlotBand createSizeRawHeaderGeometry
  exprLowering exprLoweringProps exprSimCopy loweringPosts compileEnv context
  fragExec fragGasOrigin venomExecSemantics venomInst venomState relation list pair

Theorem create_raw_header_cut_bands_mods:
  contract_inv mods exps ctx ce cx /\ MEM fn ctx.ctx_functions /\
  fn_inst_ids_distinct fn /\ vv_post_mods H ctx fn ce cx e es sa a s0 ee tv vv u /\
  compile_create_snapshot ce vv tyS a = (snap,b) /\
  emit_op MLOAD [snap] b = (len,c) /\ emit_op ADD [snap; Lit 32w] c = (data,d) /\
  fn_has_code a d fn /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = LENGTH b.cs_current_insts /\
  l.vs_current_bb = c.cs_current_bb /\ l.vs_inst_idx = LENGTH c.cs_current_insts /\
  r.vs_current_bb = d.cs_current_bb /\ r.vs_inst_idx = LENGTH d.cs_current_insts /\
  create_expr_prefix a b explicit ctx fn u msS z /\
  create_expr_prefix b c explicit ctx fn z msL l /\
  create_expr_prefix c d explicit ctx fn l msD r ==>
  fn_has_code a b fn /\
  msS = [] /\ msL = [] /\ msD = [] /\
  r.vs_gas_readings = u.vs_gas_readings /\
  run_inst_seq (emitted_insts b c) z = OK (l with vs_inst_idx := z.vs_inst_idx) /\
  run_inst_seq (emitted_insts c d) l = OK (r with vs_inst_idx := l.vs_inst_idx) /\
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
   run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx) /\
   run_inst_seq (emitted_insts a c) u = OK (l with vs_inst_idx := u.vs_inst_idx)) /\
  (!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?buf sm x exit.
      compile_alloc_buffer (type_memory_bytes ce tyS) a = (buf,sm) /\
      fn_has_code a sm fn /\ fn_has_code sm b fn /\
      lookup_block b.cs_current_bb fn.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      x.vs_current_bb = sm.cs_current_bb /\ x.vs_inst_idx = LENGTH sm.cs_current_insts /\
      z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a sm) u = OK (x with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\v w. (v.vs_current_bb <> b.cs_current_bb \/ v.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx fn v ms (OK w)) x z)
Proof
  pure_rewrite_tac[create_expr_prefix_marked] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule body_inv_no_phi_mods >> disch_then drule >> strip_tac >>
  `cs_extends a b /\ cs_extends b c /\ cs_extends c d` by
    metis_tac[ci_mono_def, ci_mono_compile_create_snapshot, ci_mono_emit_op, SND] >>
  `fn_has_code a c fn /\ fn_has_code a b fn /\ fn_has_code b c fn /\ fn_has_code c d fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!p ms q. create_prefix_step a b explicit ctx fn p ms q ==>
     (p.vs_current_bb <> b.cs_current_bb \/ p.vs_inst_idx <> LENGTH b.cs_current_insts) /\
     gas_origin_edge F explicit ctx fn p ms (OK q)` by
    simp[create_prefix_step_def, PULL_EXISTS] >>
  `!p ms q. create_prefix_step b c explicit ctx fn p ms q ==>
     (p.vs_current_bb <> c.cs_current_bb \/ p.vs_inst_idx <> LENGTH c.cs_current_insts) /\
     gas_origin_edge F explicit ctx fn p ms (OK q)` by
    simp[create_prefix_step_def, PULL_EXISTS] >>
  `!p ms q. create_prefix_step c d explicit ctx fn p ms q ==>
     (p.vs_current_bb <> d.cs_current_bb \/ p.vs_inst_idx <> LENGTH d.cs_current_insts) /\
     gas_origin_edge F explicit ctx fn p ms (OK q)` by
    simp[create_prefix_step_def, PULL_EXISTS] >>
  drule_all (Q.INST [`ES` |-> `create_prefix_step a b explicit ctx fn`,
                     `length_edge` |-> `create_prefix_step b c explicit ctx fn`,
                     `ED` |-> `create_prefix_step c d explicit ctx fn`]
                    create_raw_snapshot_straight_bands) >> strip_tac >>
  `!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?buf sm x exit.
      compile_alloc_buffer (type_memory_bytes ce tyS) a = (buf,sm) /\
      fn_has_code sm b fn /\ lookup_block b.cs_current_bb fn.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      x.vs_current_bb = sm.cs_current_bb /\ x.vs_inst_idx = LENGTH sm.cs_current_insts /\
      z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a sm) u = OK (x with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\v w. (v.vs_current_bb <> b.cs_current_bb \/ v.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx fn v ms (OK w)) x z /\
      msS = [] /\ z.vs_gas_readings = u.vs_gas_readings` by
    (rpt strip_tac >>
     `!p ms q. create_prefix_step a b explicit ctx fn p ms q ==>
        (p.vs_current_bb <> b.cs_current_bb \/ p.vs_inst_idx <> LENGTH b.cs_current_insts) /\
        ?bb i. lookup_block p.vs_current_bb fn.fn_blocks = SOME bb /\
               get_instruction bb p.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids a b /\
               gas_origin_edge F explicit ctx fn p ms (OK q)` by
       (simp[create_prefix_step_def] >> metis_tac[]) >>
     drule_all (Q.INST [`E` |-> `create_prefix_step a b explicit ctx fn`]
                 create_raw_snapshot_slot_band) >> simp[]) >>
  `msS = [] /\ z.vs_gas_readings = u.vs_gas_readings` by
    (`vv_holds_mods ce cx (post_value_type ce e) tv vv ee u` by fs[vv_post_mods_def] >>
     `vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/
      vv_location vv = SOME LocCode \/ ?tr. vv_location vv = SOME (slot_loc tr)` by
       (Cases_on `vv` >> gvs[vv_location_def, vv_holds_mods_def, vv_holds_def] >>
        rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
        gvs[slot_loc_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `r.vs_gas_readings = u.vs_gas_readings` by simp[] >>
  `((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
     run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx) /\
     run_inst_seq (emitted_insts a c) u = OK (l with vs_inst_idx := u.vs_inst_idx))` by
    (qpat_assum `_ ==> run_inst_seq _ _ = _ /\ _ /\ msS = [] /\ _` mp_tac >> metis_tac[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!tr. vv_location vv = SOME (slot_loc tr) ==> _`
    (drule_then strip_assume_tac) >>
  `fn_has_code a sm fn` by metis_tac[create_raw_snapshot_alloc_interval] >>
  qexistsl_tac [`buf`,`sm`,`x`,`exit`] >> asm_rewrite_tac[]
QED
