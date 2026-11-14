(* The dynamic membership header, including constructor immutable loads. *)
Theory bodyFullBopRestWordCtorHeader
Ancestors
  bodyPtrBopInBoundedLayout bodyPtrBopInLoopContract bodyPtrBopInElementLoad
  entryReachBodyFirstEmissionSupport exprSimBopRestWordLoadPath
  exprLowering compileEnv exprLoweringProps fragExec fragGasSeqPtr fragGasOriginPtr memSafeRun
  instMemFrontier unitTransformDefs ptrSafeRun ptrDiscipline gasEvents contextCodegenRel
  codegenRel venomExecSemantics venomInst venomState finite_map words list rich_list memLocDefs

Theorem rest_word_membership_ctor_header_joint:
  cenv.ce_is_ctor /\ vv_location vv = SOME LocCode /\
  compile_var_array_membership cenv needle vv (ArrayT ety (Dynamic cap)) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!ib x. cenv.ce_imm_alloca = SOME ib /\ ib = Var x ==> not_fresh_at sa x) /\
  (!H:num. guard H ==>
    ~s.vs_halted /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand (vv_operand vv) s = SOME w /\ op_prov (G H) (vv_operand vv) = NONE /\
    op_taint (TF H) (vv_operand vv) = {} /\ w2n w + 32 <= lo /\
    mem_word_taint (TF H).t_mem (w2n w) = {} /\ mload (w2n w) s = n2w n /\
    (!ib. cenv.ce_imm_alloca = SOME ib ==> eval_operand ib s = SOME 0w /\
      op_prov (G H) ib = NONE /\ op_taint (TF H) ib = {})) ==>
  ?len sm t GF TFF.
    compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode (vv_operand vv) sa = (len,sm) /\
    compile_array_membership_loop needle (vv_operand vv) len
      (elem_size_in_location cenv LocCode ety) (word_scale LocCode)
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) (SOME cap) is_in sm = (op,sb) /\
    (!H:num. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,G H,TF H) [] (OK t,GF H,TFF H) /\
      membership_loop_frame sa (G H) (TF H) s (GF H) (TFF H) t /\
      eval_operand len t = SOME (n2w n) /\
      op_prov (GF H) len = NONE /\ op_taint (TFF H) len = {} /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts)
Proof
  strip_tac >>
  qpat_x_assum `compile_var_array_membership _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_var_array_membership_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_array_membership_loop _ _ len _ _ _ _ _ sm = _` >>
  `fn_has_code sa sm fn` by
    (irule (cj 1 fn_has_code_split) >>
     conj_tac
     >- metis_tac[first_emission_ptr_load] >>
     qexists_tac `sb` >> simp[] >>
     metis_tac[membership_bounded_loop_extends]) >>
  simp[] >>
  Cases_on `cenv.ce_imm_alloca`
  >- suspend "direct" >>
  suspend "staged"
QED

Resume rest_word_membership_ctor_header_joint[direct]:
  gvs[contextTheory.compile_ptr_load_def, contextTheory.compile_imm_load_word_def,
      emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
      compileEnvTheory.emit_def] >>
  qabbrev_tac `dst = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id ILOAD [vv_operand vv] [dst]` >>
  qabbrev_tac `u = update_var dst (n2w n) s` >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`,
    `\H. step_prov PG (G H) ins u`, `\H. step_taint ins s u (TF H)`] >>
  gen_tac >> disch_tac >>
  first_x_assum (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME ins` by
    (qpat_x_assum `fn_has_code sa _ fn` mp_tac >>
     simp[fragExecTheory.fn_has_code_def, Abbr `ins`, Abbr `dst`] >>
     strip_tac >> qexists_tac `bb` >>
     gvs[IS_PREFIX_APPEND] >> simp[get_instruction_def, EL_APPEND]) >>
  suspend "direct_step"
QED

Resume rest_word_membership_ctor_header_joint[staged]:
  gvs[contextTheory.compile_ptr_load_def, contextTheory.compile_imm_load_word_def,
      emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
      compileEnvTheory.emit_def] >>
  qabbrev_tac `a = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `b = "%" ++ toString (sa.cs_next_var + 1)` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ADD [vv_operand vv; x] [a]` >>
  qabbrev_tac `j = mk_inst (sa.cs_next_id + 1) ILOAD [Var a] [b]` >>
  qabbrev_tac `u = update_var a w s` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = update_var b (n2w n) s1` >>
  qexistsl_tac [`v with vs_inst_idx := SUC s1.vs_inst_idx`,
    `\H. step_prov PG (step_prov PG (G H) i u) j v`,
    `\H. step_taint j s1 v (step_taint i s u (TF H))`] >>
  gen_tac >> disch_tac >>
  first_x_assum (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `!z. not_fresh_at sa z ==> z <> a /\ z <> b` by
    (simp[Abbr `a`, Abbr `b`, loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum (qspec_then `0` mp_tac) >>
     first_x_assum (qspec_then `1` mp_tac) >> simp[]) >>
  `a <> b` by (simp[Abbr `a`, Abbr `b`]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME j` by
    (qpat_x_assum `fn_has_code sa _ fn` mp_tac >>
     simp[fragExecTheory.fn_has_code_def, Abbr `i`, Abbr `j`, Abbr `a`, Abbr `b`] >>
     strip_tac >> qexists_tac `bb` >>
     gvs[IS_PREFIX_APPEND] >> simp[get_instruction_def, EL_APPEND]) >>
  suspend "staged_edges"
QED

Resume rest_word_membership_ctor_header_joint[direct_step]:
  `step_inst_base ins s = OK u` by
    (simp[Abbr `ins`, Abbr `u`, mk_inst_def,
       step_inst_base_opcode_eqs, exec_read1_def]) >>
  `ptr_inst_ok (DF H) lo 0 ctx fn (G H) (TF H) ins s` by
    suspend "direct_checks" >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,fn,PG) (s,G H,TF H) []
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
      step_prov PG (G H) ins u, step_taint ins s u (TF H))` by
    (`ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode /\
       inst_mem_below_frontier ins s /\ inst_dload_in_section ins s` by
       (gvs[Abbr `ins`, mk_inst_def, is_terminator_def,
         inst_mem_below_frontier_def, inst_dload_in_section_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def,
         allocas_from_def]) >>
     drule_all straight_line_origin_ptr_edge >>
     simp[Abbr `ins`, mk_inst_def]) >>
  conj_tac
  >- (drule (cj 2 gas_origin_ptr_path_rules) >>
      disch_then (qspec_then `[]` mp_tac) >>
      simp[] >> disch_then irule >>
      irule (cj 1 gas_origin_ptr_path_rules) >>
      simp[Abbr `u`, update_var_def]) >>
  suspend "direct_post"
QED

Resume rest_word_membership_ctor_header_joint[direct_checks]:
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
    Abbr `ins`, mk_inst_def, source_memory_read_ranges_def,
    source_memory_write_ranges_def] >>
  conj_tac
  >- simp[mem_read_ops_def] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def,
       Abbr `u`, update_var_def]
QED

Resume rest_word_membership_ctor_header_joint[direct_post]:
  `!x. not_fresh_at sa x ==> x <> dst` by
    (simp[Abbr `dst`, loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[Abbr `ins`, Abbr `u`, Abbr `dst`, membership_loop_frame_def,
    step_prov_def, out_prov_def, set_prov_def, step_taint_def,
    mem_taint_def, out_taint_def, set_var_taint_def, store_taint_def,
    adopt_reset_def, imm_taint_def, mk_inst_def, update_var_def,
    eval_operand_def, lookup_var_def, op_prov_def, op_taint_def,
    FLOOKUP_UPDATE, allocas_from_def,
    new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, FLOOKUP_DRESTRICT, pred_setTheory.COMPL_DEF,
    venom_state_component_equality] >>
  rpt strip_tac >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  simp[source_memory_write_ranges_def, FLOOKUP_DEF] >>
  simp[SF CONJ_ss, pred_setTheory.EXTENSION] >> fs[allocas_from_def] >> metis_tac[]
QED

Resume rest_word_membership_ctor_header_joint[staged_edges]:
  `step_inst_base i s = OK u` by
    (simp[Abbr `i`, Abbr `u`, mk_inst_def, step_inst_base_opcode_eqs,
          exec_pure2_def, eval_operands_def, WORD_ADD_0]) >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,fn,PG) (s,G H,TF H) []
    (OK s1, step_prov PG (G H) i u, step_taint i s u (TF H))` by
    suspend "staged_add" >>
  `eval_operand (Var a) s1 = SOME w /\ ~s1.vs_halted /\
   s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = SUC s.vs_inst_idx /\
   s1.vs_alloca_next = s.vs_alloca_next /\ mload (w2n w) s1 = n2w n` by
    gvs[Abbr `s1`, Abbr `u`, update_var_def, eval_operand_def, lookup_var_def,
         mload_def, FLOOKUP_UPDATE] >>
  `op_prov (step_prov PG (G H) i u) (Var a) = NONE /\
   op_taint (step_taint i s u (TF H)) (Var a) = {} /\
   mem_word_taint (step_taint i s u (TF H)).t_mem (w2n w) = {}` by
    suspend "staged_clean" >>
  `step_inst_base j s1 = OK v` by
    (simp[Abbr `j`, Abbr `v`, mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def]) >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,fn,PG)
    (s1,step_prov PG (G H) i u,step_taint i s u (TF H)) []
    (OK (v with vs_inst_idx := SUC s1.vs_inst_idx),
     step_prov PG (step_prov PG (G H) i u) j v,
     step_taint j s1 v (step_taint i s u (TF H)))` by
    suspend "staged_load" >>
  conj_tac
  >- (qpat_assum `gas_origin_ptr_edge _ (s,_,_) _ _`
        (mp_then Any mp_tac (cj 2 gas_origin_ptr_path_rules)) >>
      disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >>
      drule (cj 2 gas_origin_ptr_path_rules) >>
      disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >>
      irule (cj 1 gas_origin_ptr_path_rules) >>
      simp[Abbr `v`, update_var_def]) >>
  suspend "staged_post"
QED

Resume rest_word_membership_ctor_header_joint[staged_add]:
  `ptr_inst_ok (DF H) lo 0 ctx fn (G H) (TF H) i s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, Abbr `i`, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def, mem_read_ops_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def,
       eval_operands_def, WORD_ADD_0, Abbr `u`, update_var_def] >> metis_tac[]) >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    simp[Abbr `i`, mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
      inst_dload_in_section_def, source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  simp[Abbr `s1`] >>
  drule_all straight_line_origin_ptr_edge >> simp[Abbr `i`, mk_inst_def]
QED

Resume rest_word_membership_ctor_header_joint[staged_clean]:
  simp[Abbr `i`, mk_inst_def, step_prov_def, out_prov_def, set_prov_def,
    step_taint_def, mem_taint_def, out_taint_def, set_var_taint_def,
    store_taint_def, adopt_reset_def, imm_taint_def, op_prov_def, op_taint_def,
    FLOOKUP_UPDATE, new_site_bytes_def, step_writes_def, written_taint_def,
    source_memory_write_ranges_def, range_bytes_def, first_prov_def,
    Abbr `u`, update_var_def, FLOOKUP_DRESTRICT, pred_setTheory.COMPL_DEF,
    FLOOKUP_DEF, FDOM_DRESTRICT, SF CONJ_ss]
QED

Resume rest_word_membership_ctor_header_joint[staged_load]:
  `allocas_from lo s1` by
    (gvs[Abbr `s1`, Abbr `u`, update_var_def, allocas_from_def] >> metis_tac[]) >>
  `ptr_inst_ok (DF H) lo 0 ctx fn (step_prov PG (G H) i u)
    (step_taint i s u (TF H)) j s1` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `j`, mk_inst_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >>
     conj_tac >- simp[mem_read_ops_def] >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def,
          Abbr `v`, update_var_def]) >>
  `j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode /\
   inst_mem_below_frontier j s1 /\ inst_dload_in_section j s1` by
    (simp[Abbr `j`, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME j` by metis_tac[] >>
  drule_all straight_line_origin_ptr_edge >> simp[Abbr `j`, mk_inst_def]
QED

Resume rest_word_membership_ctor_header_joint[staged_post]:
  qpat_x_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `fn_has_code sa sb fn` kall_tac >>
  qpat_x_assum `fn_has_code sa _ fn` kall_tac >>
  qpat_x_assum `gas_origin_ptr_edge _ (s,_,_) _ _` kall_tac >>
  qpat_x_assum `gas_origin_ptr_edge _ (s1,_,_) _ _` kall_tac >>
  qpat_x_assum `step_inst_base i _ = _` kall_tac >>
  qpat_x_assum `step_inst_base j _ = _` kall_tac >>
  `step_prov PG (G H) i u = DRESTRICT (G H) (COMPL {a})` by
    simp[Abbr `i`, mk_inst_def, step_prov_def, out_prov_def, set_prov_def,
      first_prov_def] >>
  `step_taint i s u (TF H) = (TF H) with t_var := (TF H).t_var |+ (a,{})` by
    suspend "staged_add_ghost" >>
  conj_tac >- suspend "staged_frame" >>
  simp[Abbr `j`, Abbr `v`, Abbr `s1`, Abbr `u`, Abbr `b`,
    membership_loop_frame_def, step_prov_def, out_prov_def, set_prov_def,
    step_taint_def, mem_taint_def, out_taint_def, set_var_taint_def, store_taint_def,
    adopt_reset_def, imm_taint_def, mk_inst_def, update_var_def,
    eval_operand_def, lookup_var_def, op_prov_def, op_taint_def,
    FLOOKUP_UPDATE, allocas_from_def, first_prov_def,
    new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, FLOOKUP_DRESTRICT, pred_setTheory.COMPL_DEF,
    venom_state_component_equality] >>
  rpt strip_tac >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  simp[source_memory_write_ranges_def, FLOOKUP_DEF] >>
  simp[SF CONJ_ss, pred_setTheory.EXTENSION] >> fs[allocas_from_def] >> metis_tac[]
QED

Resume rest_word_membership_ctor_header_joint[staged_add_ghost]:
  simp[Abbr `i`, Abbr `u`, mk_inst_def, update_var_def,
    step_taint_def, mem_taint_def, out_taint_def, set_var_taint_def,
    store_taint_def, adopt_reset_def, imm_taint_def, new_site_bytes_def,
    step_writes_def, written_taint_def, source_memory_write_ranges_def,
    range_bytes_def, FLOOKUP_DEF, SF CONJ_ss, taint_component_equality]
QED

Resume rest_word_membership_ctor_header_joint[staged_frame]:
  simp[Abbr `j`, Abbr `v`, Abbr `s1`, Abbr `u`, membership_loop_frame_def,
    step_prov_def, out_prov_def, set_prov_def, step_taint_def,
    mem_taint_def, out_taint_def, set_var_taint_def, store_taint_def,
    adopt_reset_def, imm_taint_def, mk_inst_def, update_var_def,
    lookup_var_def, op_prov_def, op_taint_def, FLOOKUP_UPDATE,
    new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, FLOOKUP_DRESTRICT, pred_setTheory.COMPL_DEF,
    venom_state_component_equality] >>
  rpt strip_tac >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  simp[source_memory_write_ranges_def, FLOOKUP_DEF, SF CONJ_ss,
    pred_setTheory.EXTENSION] >> metis_tac[]
QED

Finalise rest_word_membership_ctor_header_joint
