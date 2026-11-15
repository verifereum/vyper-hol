Theory bodyFullBopRestWordCtorHeader
Ancestors
  bodyFullBopRestWordCtor bodyFullBopRestWordLoads
  bodyPtrBopInBoundedLayout bodyPtrBopInElementLoad bodyPtrBopInLoopLayout
  bodyPtrBopInLoopContract fragExec fragGasSeqPtr fragGasOriginPtr
  instMemFrontier memSafeRun ptrSafeRun ptrDiscipline memLocDefs exprLowering
  compileEnv contextCodegenRel codegenRel venomExecSemantics venomInst venomState
  finite_map words list rich_list

Theorem rest_word_membership_ctor_header_layout[local]:
  compile_var_array_membership cenv needle vv (ArrayT ety (Dynamic cap)) is_in sa = (op,sb) /\
  cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
  ?len sm.
    compile_ptr_load T cenv.ce_imm_alloca LocCode (vv_operand vv) sa = (len,sm) /\
    compile_array_membership_loop needle (vv_operand vv) len
      (elem_size_in_location cenv LocCode ety) (word_scale LocCode)
      (compile_ptr_load T cenv.ce_imm_alloca LocCode) (SOME cap) is_in sm = (op,sb) /\
    let width = (if IS_SOME cenv.ce_imm_alloca then 2 else 1);
        stage = "%" ++ toString sa.cs_next_var;
        dst = "%" ++ toString (sa.cs_next_var+width-1);
        code = (case cenv.ce_imm_alloca of NONE =>
          [mk_inst sa.cs_next_id ILOAD [vv_operand vv] [dst]]
         | SOME ib =>
          [mk_inst sa.cs_next_id ADD [vv_operand vv;ib] [stage];
           mk_inst (sa.cs_next_id+1) ILOAD [Var stage] [dst]]) in
    len = Var dst /\
    sm = sa with <| cs_next_var := sa.cs_next_var+width;
      cs_next_id := sa.cs_next_id+width;
      cs_current_insts := sa.cs_current_insts ++ code |> /\
    cs_extends sa sm
Proof
  strip_tac >>
  qpat_x_assum `compile_var_array_membership _ _ _ _ _ _ = _` mp_tac >>
  simp[exprLoweringTheory.compile_var_array_membership_def,
    compileEnvTheory.comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `compile_ptr_load _ _ _ _ _ = _` mp_tac >>
  Cases_on `cenv.ce_imm_alloca` >>
  simp[contextTheory.compile_ptr_load_def, contextTheory.compile_imm_load_word_def,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
    compileEnvTheory.comp_return_def, emitHelperTheory.emit_op_def,
    emitHelperTheory.emit_inst_def, compileEnvTheory.fresh_var_def,
    compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >>
  strip_tac >> rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  gvs[] >>
  simp[compileEnvTheory.cs_extends_def, IS_PREFIX_APPEND]
QED

Theorem rest_word_membership_ctor_header_full_joint:
  cenv.ce_is_ctor /\ vv_location vv = SOME LocCode /\
  compile_var_array_membership cenv needle vv (ArrayT ety (Dynamic cap)) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!ib x. cenv.ce_imm_alloca = SOME ib /\ ib = Var x ==> not_fresh_at sa x) /\
  (!H. guard H ==> ~s.vs_halted /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand (vv_operand vv) s = SOME w /\ op_prov (G H) (vv_operand vv) = NONE /\
    op_taint (TF H) (vv_operand vv) = {} /\
    w2n w + 32 <= lo /\ mem_word_taint (TF H).t_mem (w2n w) = {} /\
    mload (w2n w) s = n2w n /\
    (!ib. cenv.ce_imm_alloca = SOME ib ==>
      eval_operand ib s = SOME 0w /\ op_prov (G H) ib = NONE /\ op_taint (TF H) ib = {})) ==>
  ?len sm t GF TFF.
    compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode (vv_operand vv) sa = (len,sm) /\
    compile_array_membership_loop needle (vv_operand vv) len
      (elem_size_in_location cenv LocCode ety) (word_scale LocCode)
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) (SOME cap) is_in sm = (op,sb) /\
    (!H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G H,TF H) [] (OK t,GF H,TFF H) /\
      membership_loop_frame sa (G H) (TF H) s (GF H) (TFF H) t /\
      eval_operand len t = SOME (n2w n) /\ op_prov (GF H) len = NONE /\ op_taint (TFF H) len = {} /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts)
Proof
  strip_tac >> drule_all rest_word_membership_ctor_header_layout >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >>
  `cs_extends sm sb` by (drule membership_bounded_loop_extends >> simp[]) >>
  `fn_has_code sa sm fn` by
    (irule (cj 1 fn_has_code_split) >> conj_tac
     >- simp[] >>
     qexists_tac `sb` >> asm_rewrite_tac[]) >>
  qabbrev_tac `width = if IS_SOME cenv.ce_imm_alloca then 2 else 1` >>
  qabbrev_tac `stage = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `dst = "%" ++ toString (sa.cs_next_var+width-1)` >>
  qmatch_asmsub_abbrev_tac `sa.cs_current_insts ++ code` >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  qexistsl_tac [`len`, `sm`] >>
  qexists_tac `case run_inst_seq code s of
    OK u => u with vs_inst_idx := s.vs_inst_idx+width | _ => s` >>
  fs[] >> simp[GSYM SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
  gen_tac >> Cases_on `guard H` >> simp[] >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `?u. run_inst_seq code s = OK u` by suspend "run" >> simp[] >>
  `run_inst_seq_mem_ok code s` by suspend "memory" >>
  suspend "joint"
QED

Resume rest_word_membership_ctor_header_full_joint[run]:
  Cases_on `cenv.ce_imm_alloca` >> fs[] >>
  simp[Abbr `code`, Abbr `dst`, Abbr `stage`, Abbr `width`,
    exprLoweringPropsTheory.run_inst_seq_def, mk_inst_def,
    step_inst_base_opcode_eqs, exec_pure2_def, exec_read1_def, eval_operands_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, update_var_def]
QED

Resume rest_word_membership_ctor_header_full_joint[memory]:
  Cases_on `cenv.ce_imm_alloca` >> fs[] >>
  simp[Abbr `code`, Abbr `dst`, Abbr `stage`, Abbr `width`,
    fragExecMemTheory.run_inst_seq_mem_ok_def, mk_inst_def,
    unitTransformDefsTheory.inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    step_inst_base_opcode_eqs, exec_pure2_def, exec_read1_def, eval_operands_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, update_var_def, WORD_ADD_0] >> decide_tac
QED

Resume rest_word_membership_ctor_header_full_joint[joint]:
  suspend "stages"
QED

Resume rest_word_membership_ctor_header_full_joint[stages]:
  Cases_on `cenv.ce_imm_alloca`
  >- suspend "none" >>
  rename1 `cenv.ce_imm_alloca = SOME ib` >> suspend "some"
QED

Resume rest_word_membership_ctor_header_full_joint[none]:
  `width = 1 /\ dst = stage` by simp[Abbr `width`, Abbr `dst`, Abbr `stage`] >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id ILOAD [vv_operand vv] [dst]` >>
  `code = [ins]` by simp[Abbr `code`, Abbr `ins`] >>
  `u = update_var dst (n2w n) s` by
    (qpat_x_assum `run_inst_seq code s = OK u` mp_tac >>
     simp[exprLoweringPropsTheory.run_inst_seq_def, Abbr `ins`,
       mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def]) >>
  qabbrev_tac `g = DRESTRICT (G H) (COMPL {dst})` >>
  qabbrev_tac `tn = (TF H) with t_var := (TF H).t_var |+ (dst,{})` >>
  `step_prov PG (G H) ins u = g /\ step_taint ins s u (TF H) = tn` by
    suspend "none_ghost" >>
  `ptr_inst_ok (DF H) lo 0 ctx fn (G H) (TF H) ins s` by
    suspend "none_check" >>
  qexistsl_tac [`g`, `tn`] >> conj_tac
  >- (`inst_seq_ptr (DF H) lo ctx fn PG (G H) (TF H) code s g tn` by
        (`step_inst_base ins s = OK u` by
          simp[Abbr `ins`, mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def] >>
         pure_asm_rewrite_tac[inst_seq_ptr_def] >> simp[] >> metis_tac[]) >>
      `EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode) code /\
       FILTER (\ins. ins.inst_opcode = GAS) code = []` by
        simp[Abbr `ins`, mk_inst_def, is_terminator_def] >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
        (metis_tac[]) >>
      drule_all run_inst_seq_gas_origin_ptr_path >> simp[]) >>
  suspend "none_post"
QED

Resume rest_word_membership_ctor_header_full_joint[none_ghost]:
  simp[Abbr `ins`, Abbr `g`, mk_inst_def, step_prov_def, out_prov_def, set_prov_def] >>
  simp[Abbr `tn`, mk_inst_def, step_taint_def, mem_taint_def,
    out_taint_def, set_var_taint_def, store_taint_def, adopt_reset_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, source_memory_write_ranges_def, FLOOKUP_DEF,
    SF CONJ_ss, pred_setTheory.GSPEC_F, taint_component_equality, update_var_def]
QED

Resume rest_word_membership_ctor_header_full_joint[none_check]:
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, Abbr `ins`, mk_inst_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  simp[mem_read_ops_def, step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def,
    update_var_def]
QED

Resume rest_word_membership_ctor_header_full_joint[none_post]:
  qpat_assum `allocas_from lo s`
    (strip_assume_tac o REWRITE_RULE[allocas_from_def]) >>
  simp[Abbr `g`, Abbr `tn`, membership_loop_frame_def,
    update_var_def, eval_operand_def, lookup_var_def, op_prov_def, op_taint_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, pred_setTheory.COMPL_DEF,
    venom_state_component_equality, allocas_from_def] >>
  reverse conj_tac >- metis_tac[] >>
  rpt conj_tac >> qx_gen_tac `protected` >> strip_tac >>
  `protected <> dst` by
    (qpat_x_assum `not_fresh_at sa protected` mp_tac >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `dst`, Abbr `width`,
       Abbr `stage`, stringTheory.STRCAT_EQNS]) >>
  `protected <> stage` by metis_tac[] >> simp[]
QED

Resume rest_word_membership_ctor_header_full_joint[some]:
  `width = 2` by simp[Abbr `width`] >>
  `eval_operand ib s = SOME 0w /\ op_prov (G H) ib = NONE /\
   op_taint (TF H) ib = {}` by metis_tac[] >>
  qabbrev_tac `ai = mk_inst sa.cs_next_id ADD [vv_operand vv; ib] [stage]` >>
  qabbrev_tac `li = mk_inst (sa.cs_next_id+1) ILOAD [Var stage] [dst]` >>
  `code = [ai;li]` by simp[Abbr `code`, Abbr `ai`, Abbr `li`] >>
  qabbrev_tac `si = update_var stage w s` >>
  qabbrev_tac `gi = DRESTRICT (G H) (COMPL {stage})` >>
  qabbrev_tac `ti = (TF H) with t_var := (TF H).t_var |+ (stage,{})` >>
  qabbrev_tac `g = DRESTRICT gi (COMPL {dst})` >>
  qabbrev_tac `tn = ti with t_var := ti.t_var |+ (dst,{})` >>
  `step_inst_base ai s = OK si` by
    simp[Abbr `ai`, Abbr `si`, mk_inst_def, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operands_def, WORD_ADD_0] >>
  `step_prov PG (G H) ai si = gi` by
    simp[Abbr `ai`, Abbr `gi`, step_prov_def, out_prov_def, set_prov_def, first_prov_def] >>
  `step_taint ai s si (TF H) = ti` by
    (simp[Abbr `ai`, Abbr `si`, Abbr `ti`] >>
     irule stmtAppendStorageRunPtrTheory.scalar_add_taint >> simp[update_var_def]) >>
  `u = update_var dst (n2w n) si` by
    (qpat_assum `mload (w2n w) s = n2w n`
       (assume_tac o BETA_RULE o REWRITE_RULE[mload_def, LET_THM]) >>
     qpat_x_assum `run_inst_seq code s = OK u` mp_tac >>
     simp[exprLoweringPropsTheory.run_inst_seq_def, Abbr `ai`, Abbr `li`,
       Abbr `si`, mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
       exec_read1_def, eval_operands_def, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, WORD_ADD_0, mload_def]) >>
  suspend "some_finish"
QED

Resume rest_word_membership_ctor_header_full_joint[some_finish]:
  `eval_operand (Var stage) si = SOME w /\ op_prov gi (Var stage) = NONE /\
   op_taint ti (Var stage) = {} /\ ti.t_mem = (TF H).t_mem /\
   mload (w2n w) si = n2w n` by
    (simp[Abbr `si`, Abbr `gi`, Abbr `ti`, update_var_def, eval_operand_def,
      lookup_var_def, op_prov_def, op_taint_def, FLOOKUP_UPDATE,
      FLOOKUP_DRESTRICT, pred_setTheory.COMPL_DEF, mload_def] >>
     metis_tac[mload_def]) >>
  `step_inst_base li si = OK u` by
    simp[Abbr `li`, mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def] >>
  `step_prov PG gi li u = g /\ step_taint li si u ti = tn` by
    suspend "some_ghost" >>
  `ptr_inst_ok (DF H) lo 0 ctx fn (G H) (TF H) ai s /\
   ptr_inst_ok (DF H) lo 0 ctx fn gi ti li
     (si with vs_inst_idx := SUC (LENGTH sa.cs_current_insts))` by suspend "some_check" >>
  `!j. step_inst_base li (si with vs_inst_idx := j) = OK (u with vs_inst_idx := j)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep,
      instIdxIndepTheory.exec_result_map_def, Abbr `li`, mk_inst_def, is_terminator_def] >>
  qexistsl_tac [`g`, `tn`] >> conj_tac
  >- (`inst_seq_ptr (DF H) lo ctx fn PG (G H) (TF H) code s g tn` by
        (pure_asm_rewrite_tac[inst_seq_ptr_def] >> simp[] >> metis_tac[]) >>
      `EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode) code /\
       FILTER (\ins. ins.inst_opcode = GAS) code = []` by
        simp[Abbr `ai`, Abbr `li`, mk_inst_def, is_terminator_def] >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
      drule_all run_inst_seq_gas_origin_ptr_path >> simp[]) >>
  suspend "some_post"
QED

Resume rest_word_membership_ctor_header_full_joint[some_ghost]:
  simp[Abbr `li`, Abbr `g`, mk_inst_def, step_prov_def, out_prov_def, set_prov_def] >>
  simp[Abbr `tn`, mk_inst_def, step_taint_def, mem_taint_def,
    out_taint_def, set_var_taint_def, store_taint_def, adopt_reset_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, source_memory_write_ranges_def, FLOOKUP_DEF,
    SF CONJ_ss, pred_setTheory.GSPEC_F, taint_component_equality, update_var_def]
QED

Resume rest_word_membership_ctor_header_full_joint[some_check]:
  conj_tac
  >- (simp[Abbr `ai`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
        mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
        mem_read_ops_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
        exec_pure2_def, eval_operands_def, update_var_def, WORD_ADD_0] >>
      simp[Abbr `si`, update_var_def] >> gen_tac >>
      Cases_on `op' = vv_operand vv` >> simp[] >> Cases_on `op' = ib` >> simp[]) >>
  simp[Abbr `li`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
    mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
    mem_read_ops_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
    exec_read1_def, update_var_def, Abbr `si`, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE] >>
  simp[allocas_from_def] >>
  qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])
QED

Resume rest_word_membership_ctor_header_full_joint[some_post]:
  qpat_assum `allocas_from lo s`
    (strip_assume_tac o REWRITE_RULE[allocas_from_def]) >>
  simp[Abbr `g`, Abbr `tn`, Abbr `gi`, Abbr `ti`, Abbr `si`,
    membership_loop_frame_def, update_var_def, eval_operand_def, lookup_var_def,
    op_prov_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
    pred_setTheory.COMPL_DEF, venom_state_component_equality, allocas_from_def] >>
  reverse conj_tac >- metis_tac[] >>
  qx_gen_tac `protected` >> strip_tac >>
  `protected <> dst /\ protected <> stage` by
    (qpat_x_assum `not_fresh_at sa protected` mp_tac >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `dst`, Abbr `stage`,
       Abbr `width`, stringTheory.STRCAT_EQNS]) >> simp[]
QED

Finalise rest_word_membership_ctor_header_full_joint

Theorem rest_word_membership_ctor_header_const_full_joint:
  cenv.ce_is_ctor /\ vv_location vv = SOME LocCode /\
  compile_var_array_membership cenv needle vv (ArrayT ety (Dynamic cap)) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!ib x. cenv.ce_imm_alloca = SOME ib /\ ib = Var x ==> not_fresh_at sa x) /\
  (!H:'h. guard H ==> ~s.vs_halted /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand (vv_operand vv) s = SOME w /\ op_prov G (vv_operand vv) = NONE /\
    op_taint TF (vv_operand vv) = {} /\
    w2n w + 32 <= lo /\ mem_word_taint TF.t_mem (w2n w) = {} /\
    mload (w2n w) s = n2w n /\
    (!ib. cenv.ce_imm_alloca = SOME ib ==>
      eval_operand ib s = SOME 0w /\ op_prov G ib = NONE /\ op_taint TF ib = {})) ==>
  ?len sm t GF TFF.
    compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode (vv_operand vv) sa = (len,sm) /\
    compile_array_membership_loop needle (vv_operand vv) len
      (elem_size_in_location cenv LocCode ety) (word_scale LocCode)
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) (SOME cap) is_in sm = (op,sb) /\
    (!H:'h. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,TF) [] (OK t,GF,TFF) /\
      membership_loop_frame sa G TF s GF TFF t /\
      eval_operand len t = SOME (n2w n) /\ op_prov GF len = NONE /\ op_taint TFF len = {} /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts)
Proof
  strip_tac >> drule_all rest_word_membership_ctor_header_layout >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >>
  `cs_extends sm sb` by (drule membership_bounded_loop_extends >> simp[]) >>
  `fn_has_code sa sm fn` by
    (irule (cj 1 fn_has_code_split) >> conj_tac >- simp[] >>
     qexists_tac `sb` >> asm_rewrite_tac[]) >>
  qabbrev_tac `width = if IS_SOME cenv.ce_imm_alloca then 2 else 1` >>
  qabbrev_tac `stage = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `dst = "%" ++ toString (sa.cs_next_var+width-1)` >>
  qmatch_asmsub_abbrev_tac `sa.cs_current_insts ++ code` >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  qexistsl_tac [`len`, `sm`] >>
  qexists_tac `case run_inst_seq code s of
    OK u => u with vs_inst_idx := s.vs_inst_idx+width | _ => s` >>
  qexistsl_tac [`DRESTRICT
      (case cenv.ce_imm_alloca of NONE => G | SOME _ => DRESTRICT G (COMPL {stage}))
      (COMPL {dst})`,
    `TF with t_var :=
      (case cenv.ce_imm_alloca of NONE => TF.t_var | SOME _ => TF.t_var |+ (stage,{}))
        |+ (dst,{})`] >>
  fs[] >> gen_tac >> disch_tac >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `?u. run_inst_seq code s = OK u` by suspend "run" >> simp[] >>
  `run_inst_seq_mem_ok code s` by suspend "memory" >>
  Cases_on `cenv.ce_imm_alloca` >- suspend "none" >>
  rename1 `cenv.ce_imm_alloca = SOME ib` >> suspend "some"
QED

Resume rest_word_membership_ctor_header_const_full_joint[run]:
  Cases_on `cenv.ce_imm_alloca` >> fs[] >>
  simp[Abbr `code`, Abbr `dst`, Abbr `stage`, Abbr `width`,
    exprLoweringPropsTheory.run_inst_seq_def, mk_inst_def,
    step_inst_base_opcode_eqs, exec_pure2_def, exec_read1_def, eval_operands_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, update_var_def]
QED

Resume rest_word_membership_ctor_header_const_full_joint[memory]:
  Cases_on `cenv.ce_imm_alloca` >> fs[] >>
  simp[Abbr `code`, Abbr `dst`, Abbr `stage`, Abbr `width`,
    fragExecMemTheory.run_inst_seq_mem_ok_def, mk_inst_def,
    unitTransformDefsTheory.inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    step_inst_base_opcode_eqs, exec_pure2_def, exec_read1_def, eval_operands_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, update_var_def, WORD_ADD_0] >> decide_tac
QED

Resume rest_word_membership_ctor_header_const_full_joint[none]:
  simp[] >>
  qmatch_goalsub_abbrev_tac `(OK _,g,tn)` >>
  `width = 1 /\ dst = stage` by simp[Abbr `width`, Abbr `dst`, Abbr `stage`] >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id ILOAD [vv_operand vv] [dst]` >>
  `code = [ins]` by simp[Abbr `code`, Abbr `ins`] >>
  `u = update_var dst (n2w n) s` by
    (qpat_x_assum `run_inst_seq code s = OK u` mp_tac >>
     simp[exprLoweringPropsTheory.run_inst_seq_def, Abbr `ins`,
       mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def]) >>
  `step_prov PG G ins u = g /\ step_taint ins s u TF = tn` by suspend "none_ghost" >>
  `ptr_inst_ok (DF H) lo 0 ctx fn G TF ins s` by suspend "none_check" >>
  conj_tac
  >- (`inst_seq_ptr (DF H) lo ctx fn PG G TF code s g tn` by
        (`step_inst_base ins s = OK u` by
          simp[Abbr `ins`, mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def] >>
         pure_asm_rewrite_tac[inst_seq_ptr_def] >> simp[] >> metis_tac[]) >>
      `EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode) code /\
       FILTER (\ins. ins.inst_opcode = GAS) code = []` by
        simp[Abbr `ins`, mk_inst_def, is_terminator_def] >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
      drule_all run_inst_seq_gas_origin_ptr_path >> simp[]) >>
  suspend "none_post"
QED

Resume rest_word_membership_ctor_header_const_full_joint[none_ghost]:
  simp[Abbr `ins`, Abbr `g`, mk_inst_def, step_prov_def, out_prov_def, set_prov_def] >>
  simp[Abbr `tn`, mk_inst_def, step_taint_def, mem_taint_def,
    out_taint_def, set_var_taint_def, store_taint_def, adopt_reset_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, source_memory_write_ranges_def, FLOOKUP_DEF,
    SF CONJ_ss, pred_setTheory.GSPEC_F, taint_component_equality, update_var_def]
QED

Resume rest_word_membership_ctor_header_const_full_joint[none_check]:
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, Abbr `ins`, mk_inst_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  simp[mem_read_ops_def, step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def,
    update_var_def]
QED

Resume rest_word_membership_ctor_header_const_full_joint[none_post]:
  qpat_assum `allocas_from lo s`
    (strip_assume_tac o REWRITE_RULE[allocas_from_def]) >>
  simp[Abbr `g`, Abbr `tn`, membership_loop_frame_def,
    update_var_def, eval_operand_def, lookup_var_def, op_prov_def, op_taint_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, pred_setTheory.COMPL_DEF,
    venom_state_component_equality, allocas_from_def] >>
  reverse conj_tac >- metis_tac[] >>
  rpt conj_tac >> qx_gen_tac `protected` >> strip_tac >>
  `protected <> dst` by
    (qpat_x_assum `not_fresh_at sa protected` mp_tac >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `dst`, Abbr `width`,
       Abbr `stage`, stringTheory.STRCAT_EQNS]) >>
  `protected <> stage` by metis_tac[] >> simp[]
QED

Resume rest_word_membership_ctor_header_const_full_joint[some]:
  simp[] >> qmatch_goalsub_abbrev_tac `(OK _,g,tn)` >>
  `width = 2` by simp[Abbr `width`] >>
  `eval_operand ib s = SOME 0w /\ op_prov G ib = NONE /\ op_taint TF ib = {}` by metis_tac[] >>
  qabbrev_tac `ai = mk_inst sa.cs_next_id ADD [vv_operand vv; ib] [stage]` >>
  qabbrev_tac `li = mk_inst (sa.cs_next_id+1) ILOAD [Var stage] [dst]` >>
  `code = [ai;li]` by simp[Abbr `code`, Abbr `ai`, Abbr `li`] >>
  qabbrev_tac `si = update_var stage w s` >>
  qabbrev_tac `gi = DRESTRICT G (COMPL {stage})` >>
  qabbrev_tac `ti = TF with t_var := TF.t_var |+ (stage,{})` >>
  `step_inst_base ai s = OK si` by
    simp[Abbr `ai`, Abbr `si`, mk_inst_def, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operands_def, WORD_ADD_0] >>
  `step_prov PG G ai si = gi` by
    simp[Abbr `ai`, Abbr `gi`, step_prov_def, out_prov_def, set_prov_def, first_prov_def] >>
  `step_taint ai s si TF = ti` by
    (simp[Abbr `ai`, Abbr `si`, Abbr `ti`] >>
     irule stmtAppendStorageRunPtrTheory.scalar_add_taint >> simp[update_var_def]) >>
  `u = update_var dst (n2w n) si` by
    (qpat_assum `mload (w2n w) s = n2w n`
       (assume_tac o BETA_RULE o REWRITE_RULE[mload_def, LET_THM]) >>
     qpat_x_assum `run_inst_seq code s = OK u` mp_tac >>
     simp[exprLoweringPropsTheory.run_inst_seq_def, Abbr `ai`, Abbr `li`,
       Abbr `si`, mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
       exec_read1_def, eval_operands_def, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, WORD_ADD_0, mload_def]) >>
  suspend "some_finish"
QED

Resume rest_word_membership_ctor_header_const_full_joint[some_finish]:
  `eval_operand (Var stage) si = SOME w /\ op_prov gi (Var stage) = NONE /\
   op_taint ti (Var stage) = {} /\ ti.t_mem = TF.t_mem /\ mload (w2n w) si = n2w n` by
    (simp[Abbr `si`, Abbr `gi`, Abbr `ti`, update_var_def, eval_operand_def,
      lookup_var_def, op_prov_def, op_taint_def, FLOOKUP_UPDATE,
      FLOOKUP_DRESTRICT, pred_setTheory.COMPL_DEF, mload_def] >> metis_tac[mload_def]) >>
  `step_inst_base li si = OK u` by
    simp[Abbr `li`, mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def] >>
  `step_prov PG gi li u = g /\ step_taint li si u ti = tn` by suspend "some_ghost" >>
  `ptr_inst_ok (DF H) lo 0 ctx fn G TF ai s /\
   ptr_inst_ok (DF H) lo 0 ctx fn gi ti li
     (si with vs_inst_idx := SUC (LENGTH sa.cs_current_insts))` by suspend "some_check" >>
  `!j. step_inst_base li (si with vs_inst_idx := j) = OK (u with vs_inst_idx := j)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep,
      instIdxIndepTheory.exec_result_map_def, Abbr `li`, mk_inst_def, is_terminator_def] >>
  conj_tac
  >- (`inst_seq_ptr (DF H) lo ctx fn PG G TF code s g tn` by
        (pure_asm_rewrite_tac[inst_seq_ptr_def] >> simp[] >> metis_tac[]) >>
      `EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode) code /\
       FILTER (\ins. ins.inst_opcode = GAS) code = []` by
        simp[Abbr `ai`, Abbr `li`, mk_inst_def, is_terminator_def] >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
      drule_all run_inst_seq_gas_origin_ptr_path >> simp[]) >>
  suspend "some_post"
QED

Resume rest_word_membership_ctor_header_const_full_joint[some_ghost]:
  simp[Abbr `li`, Abbr `g`, Abbr `gi`, mk_inst_def, step_prov_def, out_prov_def, set_prov_def] >>
  simp[Abbr `tn`, Abbr `ti`, mk_inst_def, step_taint_def, mem_taint_def,
    out_taint_def, set_var_taint_def, store_taint_def, adopt_reset_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, source_memory_write_ranges_def, FLOOKUP_DEF,
    SF CONJ_ss, pred_setTheory.GSPEC_F, taint_component_equality, update_var_def]
QED

Resume rest_word_membership_ctor_header_const_full_joint[some_check]:
  conj_tac
  >- (simp[Abbr `ai`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
        mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
        mem_read_ops_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
        exec_pure2_def, eval_operands_def, update_var_def, WORD_ADD_0] >>
      simp[Abbr `si`, update_var_def] >> gen_tac >>
      Cases_on `op' = vv_operand vv` >> simp[] >> Cases_on `op' = ib` >> simp[]) >>
  simp[Abbr `li`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
    mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
    mem_read_ops_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
    exec_read1_def, update_var_def, Abbr `si`, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE] >> simp[allocas_from_def] >>
  qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])
QED

Resume rest_word_membership_ctor_header_const_full_joint[some_post]:
  qpat_assum `allocas_from lo s`
    (strip_assume_tac o REWRITE_RULE[allocas_from_def]) >>
  simp[Abbr `g`, Abbr `tn`, Abbr `gi`, Abbr `ti`, Abbr `si`,
    membership_loop_frame_def, update_var_def, eval_operand_def, lookup_var_def,
    op_prov_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
    pred_setTheory.COMPL_DEF, venom_state_component_equality, allocas_from_def] >>
  reverse conj_tac >- metis_tac[] >> qx_gen_tac `protected` >> strip_tac >>
  `protected <> dst /\ protected <> stage` by
    (qpat_x_assum `not_fresh_at sa protected` mp_tac >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `dst`, Abbr `stage`,
       Abbr `width`, stringTheory.STRCAT_EQNS]) >> simp[]
QED

Finalise rest_word_membership_ctor_header_const_full_joint
