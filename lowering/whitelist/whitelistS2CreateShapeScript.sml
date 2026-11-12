Theory whitelistS2CreateShape
Ancestors
  list loweringShapeProps loweringShapeRules loweringShapeDefs
  builtinCreate context compileEnv emitHelper unitShapeDefs venomInst
  exprLowering supportedExprTraverse vyperAST

Theorem compile_multi_vvs_length:
  !args cfn cenv st vs st'.
    compile_multi_vvs cfn cenv args st = (vs, st') ==>
    LENGTH vs = LENGTH args
Proof
  Induct >> simp[compile_multi_vvs_def, comp_return_def] >>
  rpt gen_tac >>
  simp[comp_bind_def] >>
  pairarg_tac >> pairarg_tac >> simp[comp_return_def] >>
  Cases_on `compile_multi_vvs cfn cenv args cs'` >>
  simp[] >> strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem compile_create_proxy_buf_shape[local]:
  shape_step internal compiler_label (\st. plain_operand st target)
    (compile_create_proxy_buf target) (\v st. plain_operand st v)
Proof
  simp[compile_create_proxy_buf_def] >>
  irule shape_step_bind >>
  qexists_tac `\buf st. plain_operand st target /\ plain_operand st buf.buf_operand` >>
  reverse conj_tac >- (ho_match_mp_tac compile_alloc_buffer_shape_framed >>
    mp_tac (Q.SPEC `[target]` shape_stable_plain_operands) >> simp[]) >>
  qx_gen_tac `buf` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\op st. op = buf.buf_operand /\ plain_operand st target /\ plain_operand st buf.buf_operand` >>
  reverse conj_tac >- (irule shape_step_return >> simp[]) >>
  gen_tac >> BETA_TAC >>
  ho_match_mp_tac shape_step_pure_pre >> strip_tac >> gvs[] >>
  qabbrev_tac `B = \st. plain_operand st target /\ plain_operand st buf.buf_operand` >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. B st` >>
  reverse conj_tac >- suspend "store_preamble" >> gen_tac >> simp[] >>
  irule shape_step_bind >>
  qexists_tac `\a st. B st /\ plain_operand st a` >>
  reverse conj_tac >- suspend "align" >> qx_gen_tac `aligned` >> simp[] >>
  qabbrev_tac `A = \st. B st /\ plain_operand st aligned` >>
  irule shape_step_bind >>
  qexists_tac `\p st. A st /\ plain_operand st p` >>
  reverse conj_tac >- suspend "preamble_offset" >> qx_gen_tac `preamble` >> simp[] >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. A st` >>
  reverse conj_tac >- suspend "store_target" >> gen_tac >> simp[] >>
  irule shape_step_bind >>
  qexists_tac `\p st. A st /\ plain_operand st p` >>
  reverse conj_tac >- suspend "post_offset" >> qx_gen_tac `post` >> simp[] >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. A st` >>
  reverse conj_tac >- suspend "store_post" >> gen_tac >> simp[] >>
  irule shape_step_return >> simp[Abbr `A`, Abbr `B`]
QED

Resume compile_create_proxy_buf_shape[store_preamble]:
  irule shape_step_conseq >>
  irule_at Any shape_step_emit_void_plain >>
  qexists_tac `B` >> conj_tac
  >- (mp_tac (Q.SPEC `[target; buf.buf_operand]` shape_stable_plain_operands) >>
      simp[Abbr `B`]) >>
  simp[Abbr `B`, plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
       lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
       mk_inst_def, label_positions_ok_def, inst_jump_labels_ok_def,
       is_terminator_def, is_param_opcode_def, is_read0_opcode_def]
QED
Resume compile_create_proxy_buf_shape[align]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_op_plain >>
  qexists_tac `B` >> conj_tac
  >- (mp_tac (Q.SPEC `[target; buf.buf_operand]` shape_stable_plain_operands) >> simp[Abbr `B`]) >>
  simp[Abbr `B`, label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
       raw_opcode_ok_def, inst_shape_ok_def, mk_inst_def,
       label_positions_ok_def, inst_jump_labels_ok_def,
       is_terminator_def, is_param_opcode_def, is_read0_opcode_def]
QED
Resume compile_create_proxy_buf_shape[preamble_offset]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_op_plain >>
  qexists_tac `A` >> conj_tac
  >- (mp_tac (Q.SPEC `[target; buf.buf_operand; aligned]` shape_stable_plain_operands) >>
      simp[Abbr `A`, Abbr `B`, GSYM CONJ_ASSOC]) >>
  simp[Abbr `A`, Abbr `B`, label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
       raw_opcode_ok_def, inst_shape_ok_def, mk_inst_def,
       label_positions_ok_def, inst_jump_labels_ok_def,
       is_terminator_def, is_param_opcode_def, is_read0_opcode_def]
QED
Resume compile_create_proxy_buf_shape[post_offset]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_op_plain >>
  qexists_tac `A` >> conj_tac
  >- (mp_tac (Q.SPEC `[target; buf.buf_operand; aligned]` shape_stable_plain_operands) >>
      simp[Abbr `A`, Abbr `B`, GSYM CONJ_ASSOC]) >>
  simp[Abbr `A`, Abbr `B`, label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
       raw_opcode_ok_def, inst_shape_ok_def, mk_inst_def,
       label_positions_ok_def, inst_jump_labels_ok_def,
       is_terminator_def, is_param_opcode_def, is_read0_opcode_def]
QED
Resume compile_create_proxy_buf_shape[store_target]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_void_plain >>
  qexists_tac `A` >> conj_tac
  >- (mp_tac (Q.SPEC `[target; buf.buf_operand; aligned]` shape_stable_plain_operands) >>
      simp[Abbr `A`, Abbr `B`, GSYM CONJ_ASSOC]) >>
  simp[Abbr `A`, Abbr `B`, plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
       lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
       mk_inst_def, label_positions_ok_def, inst_jump_labels_ok_def,
       is_terminator_def, is_param_opcode_def, is_read0_opcode_def]
QED
Resume compile_create_proxy_buf_shape[store_post]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_void_plain >>
  qexists_tac `A` >> conj_tac
  >- (mp_tac (Q.SPEC `[target; buf.buf_operand; aligned]` shape_stable_plain_operands) >>
      simp[Abbr `A`, Abbr `B`, GSYM CONJ_ASSOC]) >>
  simp[Abbr `A`, Abbr `B`, plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
       lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
       mk_inst_def, label_positions_ok_def, inst_jump_labels_ok_def,
       is_terminator_def, is_param_opcode_def, is_read0_opcode_def]
QED
Finalise compile_create_proxy_buf_shape[local]

Theorem compile_check_create_result_shape[local]:
  shape_step internal compiler_label (\st. plain_operand st result)
    (compile_check_create_result result rof) (\v st. plain_operand st v)
Proof
  reverse (Cases_on `rof`) >> simp[compile_check_create_result_def]
  >- (irule shape_step_return >> simp[]) >>
  `shape_stable (\st. plain_operand st result)` by
    (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule shape_step_bind >>
  qexists_tac `\fail_lbl st. plain_operand st result /\ compiler_label fail_lbl /\ label_sfx "create_fail" fail_lbl` >>
  reverse conj_tac >- (ho_match_mp_tac shape_step_fresh_label_sfx >> simp[]) >>
  qx_gen_tac `fail_lbl` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\ok st. (plain_operand st result /\ compiler_label fail_lbl /\ label_sfx "create_fail" fail_lbl) /\ compiler_label ok /\ label_sfx "create_ok" ok` >>
  reverse conj_tac >- (ho_match_mp_tac shape_step_fresh_label_sfx >>
    simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `ok` >> BETA_TAC >>
  irule shape_step_conseq >>
  irule_at Any shape_step_pure_pre >>
  qexists_tac `compiler_label fail_lbl /\ compiler_label ok /\ label_sfx "create_fail" fail_lbl /\ label_sfx "create_ok" ok` >>
  qexistsl [`\v st. plain_operand st v`, `\st. plain_operand st result`, `compiler_label`] >>
  simp[] >> strip_tac >>
  `ok <> fail_lbl` by (irule label_sfx_distinct >>
    qexistsl [`"create_ok"`, `"create_fail"`] >> simp[]) >>
  suspend "check_tail"
QED

Resume compile_check_create_result_shape[check_tail]:
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st result` >>
  reverse conj_tac >- suspend "check_jump" >> gen_tac >> BETA_TAC >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st result` >>
  reverse conj_tac >- (ho_match_mp_tac shape_step_new_block >> simp[]) >>
  gen_tac >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\rds st. plain_operand st result /\ plain_operand st rds` >>
  reverse conj_tac >- suspend "check_size" >> qx_gen_tac `rds` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\buf st. (plain_operand st result /\ plain_operand st rds) /\ plain_operand st buf.buf_operand` >>
  reverse conj_tac >- (ho_match_mp_tac compile_alloc_buffer_shape_framed >>
    mp_tac (Q.SPEC `[result; rds]` shape_stable_plain_operands) >> simp[]) >>
  qx_gen_tac `buf` >> BETA_TAC >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. (plain_operand st result /\ plain_operand st rds) /\ plain_operand st buf.buf_operand` >>
  reverse conj_tac >- suspend "check_copy" >> gen_tac >> BETA_TAC >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st result` >>
  reverse conj_tac >- suspend "check_revert" >> gen_tac >> BETA_TAC >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st result` >>
  reverse conj_tac >- (ho_match_mp_tac shape_step_new_block >> simp[]) >>
  gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]
QED
Resume compile_check_create_result_shape[check_jump]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_inst_guarded_framed >>
  qexists_tac `\st. plain_operand st result` >> simp[] >>
  simp[label_or_plain_def, plain_operand_def,
    stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
    raw_opcode_ok_def, inst_shape_ok_def, mk_inst_def,
    label_positions_ok_def, inst_jump_labels_ok_def,
    is_terminator_def, is_param_opcode_def, is_read0_opcode_def,
    jump_label_ok_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[stackPlanTypesTheory.is_label_operand_def]
QED
Resume compile_check_create_result_shape[check_size]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_op_plain >>
  qexists_tac `\st. plain_operand st result` >> simp[] >>
  simp[lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
    mk_inst_def, label_positions_ok_def, inst_jump_labels_ok_def,
    is_terminator_def, is_param_opcode_def, is_read0_opcode_def]
QED
Resume compile_check_create_result_shape[check_copy]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_void_plain >>
  qexists_tac `\st. (plain_operand st result /\ plain_operand st rds) /\ plain_operand st buf.buf_operand` >>
  conj_tac >- (mp_tac (Q.SPEC `[result; rds; buf.buf_operand]` shape_stable_plain_operands) >> simp[GSYM CONJ_ASSOC]) >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
    lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
    mk_inst_def, label_positions_ok_def, inst_jump_labels_ok_def,
    is_terminator_def, is_param_opcode_def, is_read0_opcode_def]
QED
Resume compile_check_create_result_shape[check_revert]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_inst_guarded_framed >>
  qexists_tac `\st. (plain_operand st result /\ plain_operand st rds) /\ plain_operand st buf.buf_operand` >>
  conj_tac >- (mp_tac (Q.SPEC `[result; rds; buf.buf_operand]` shape_stable_plain_operands) >> simp[GSYM CONJ_ASSOC]) >>
  simp[label_or_plain_def, plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
    lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
    mk_inst_def, label_positions_ok_def, inst_jump_labels_ok_def,
    is_terminator_def, is_param_opcode_def, is_read0_opcode_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[stackPlanTypesTheory.is_label_operand_def]
QED
Finalise compile_check_create_result_shape[local]

Theorem compile_create_dispatch_shape[local]:
  shape_step internal compiler_label
    (\st. EVERY (plain_operand st) [code_ptr; code_len; value_op] /\
          (case salt_opt of NONE => T | SOME salt => plain_operand st salt))
    (compile_create_dispatch code_ptr code_len value_op salt_opt rof)
    (\v st. plain_operand st v)
Proof
  simp[compile_create_dispatch_def] >>
  irule shape_step_bind >> qexists_tac `\v st. plain_operand st v` >>
  conj_tac >- (gen_tac >> BETA_TAC >> irule compile_check_create_result_shape) >>
  Cases_on `salt_opt` >> simp[] >>
  irule shape_step_conseq >> irule_at Any shape_step_emit_op_plain >>
  qexists_tac `\st. T` >> simp[shape_stable_def] >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
    lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
    mk_inst_def, label_positions_ok_def, inst_jump_labels_ok_def,
    is_terminator_def, is_param_opcode_def, is_read0_opcode_def]
QED

Theorem compile_create_salt_shape[local]:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  (case salt_e of NONE => T | SOME e => ~supported_expr_exists expr_shape_root e) ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_create_salt cfn cenv salt_e)
    (\v st. case v of NONE => T | SOME salt => plain_operand st salt)
Proof
  strip_tac >> Cases_on `salt_e` >> gvs[compile_create_salt_def]
  >- (irule shape_step_return >> simp[]) >>
  irule shape_step_bind >> qexists_tac `\v st. plain_operand st v` >>
  conj_tac >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  irule shape_step_conseq >> irule_at Any lower_value_callback_shape >>
  qexists_tac `\st. T` >> simp[shape_stable_def]
QED


Theorem compile_create_ctor_tuple_shape[local]:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_exprs_exists expr_shape_root args ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_create_ctor_tuple cfn cenv args) (\v st. plain_operand st v)
Proof
  strip_tac >> simp[compile_create_ctor_tuple_def] >>
  irule shape_step_bind >>
  qexists_tac `\vs st. cenv_shape_ok st cenv /\ EVERY (value_shape_ok st) vs /\ LENGTH vs = LENGTH args` >>
  reverse conj_tac >- (
    drule compile_multi_vvs_shape >>
    disch_then (qspecl_then [`cenv`, `args`, `\st. cenv_shape_ok st cenv`] mp_tac) >>
    simp[cenv_shape_ok_stable, shape_step_def] >>
    metis_tac[compile_multi_vvs_length]) >>
  qx_gen_tac `vs` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\buf st. (cenv_shape_ok st cenv /\ EVERY (value_shape_ok st) vs /\ LENGTH vs = LENGTH args) /\ plain_operand st buf.buf_operand` >>
  reverse conj_tac >- (ho_match_mp_tac compile_alloc_buffer_shape_framed >>
    simp[shape_stable_def, EVERY_MEM] >> rpt strip_tac
    >- (mp_tac cenv_shape_ok_stable >> simp[shape_stable_def] >> metis_tac[]) >>
    mp_tac (Q.SPEC `e` value_shape_ok_stable) >> simp[shape_stable_def] >>
    disch_then irule >> goal_assum (drule_at Any) >> simp[]) >>
  qx_gen_tac `buf` >> BETA_TAC >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. plain_operand st buf.buf_operand` >>
  conj_tac >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  irule shape_step_conseq >> irule_at Any compile_extcall_store_values_shape_under >>
  qexists_tac `\st. plain_operand st buf.buf_operand` >>
  simp[] >> conj_tac
  >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  rpt strip_tac >>
  `LENGTH vs = LENGTH (MAP expr_type args)` by simp[] >>
  gvs[EVERY_MEM, MEM_ZIP] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[MEM_EL]
QED

Theorem compile_create_snapshot_memory_shape[local]:
  shape_step internal compiler_label
    (\st. plain_operand st dst /\ plain_operand st src)
    (do len <- emit_op MLOAD [src];
        copy_size <- emit_op ADD [len; Lit 32w];
        compile_copy_memory_dynamic dst src copy_size od)
    (\u st. plain_operand st dst)
Proof
  irule shape_step_bind >>
  qexists_tac `\len st. (plain_operand st dst /\ plain_operand st src) /\ plain_operand st len` >>
  reverse conj_tac >- suspend "snapshot_load" >> qx_gen_tac `len` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\n st. (plain_operand st dst /\ plain_operand st src) /\ plain_operand st n` >>
  reverse conj_tac >- suspend "snapshot_add" >> qx_gen_tac `copy_size` >> BETA_TAC >>
  irule shape_step_frame_from >> irule_at Any compile_copy_memory_dynamic_shape >>
  qexists_tac `\st. plain_operand st dst` >>
  simp[] >> simp[shape_stable_def] >> metis_tac[plain_operand_mono]
QED
Resume compile_create_snapshot_memory_shape[snapshot_load]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_op_plain >>
  qexists_tac `\st. plain_operand st dst /\ plain_operand st src` >>
  conj_tac >- (mp_tac (Q.SPEC `[dst;src]` shape_stable_plain_operands) >> simp[]) >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
    lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
    mk_inst_def, label_positions_ok_def, inst_jump_labels_ok_def,
    is_terminator_def, is_param_opcode_def, is_read0_opcode_def]
QED
Resume compile_create_snapshot_memory_shape[snapshot_add]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_op_plain >>
  qexists_tac `\st. plain_operand st dst /\ plain_operand st src` >>
  conj_tac >- (mp_tac (Q.SPEC `[dst;src]` shape_stable_plain_operands) >> simp[]) >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
    lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
    mk_inst_def, label_positions_ok_def, inst_jump_labels_ok_def,
    is_terminator_def, is_param_opcode_def, is_read0_opcode_def]
QED
Finalise compile_create_snapshot_memory_shape[local]

Theorem compile_create_snapshot_shape[local]:
  shape_step internal compiler_label
    (\st. cenv_shape_ok st cenv /\ value_shape_ok st vv)
    (compile_create_snapshot cenv vv bytecode_ty) (\v st. plain_operand st v)
Proof
  simp[compile_create_snapshot_def] >>
  irule shape_step_conseq >>
  qexistsl [`compiler_label`, `\st. cenv_shape_ok st cenv /\ plain_operand st (vv_operand vv)`, `\v st. plain_operand st v`] >>
  conj_tac >- simp[] >>
  conj_tac >- (Cases_on `vv` >> simp[value_shape_ok_def, vv_operand_def]) >>
  conj_tac >- simp[] >>
  irule shape_step_bind >>
  qexists_tac `\buf st. (cenv_shape_ok st cenv /\ plain_operand st (vv_operand vv)) /\ plain_operand st buf.buf_operand` >>
  reverse conj_tac >- (ho_match_mp_tac compile_alloc_buffer_shape_framed >>
    ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
    simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `buf` >> BETA_TAC >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. plain_operand st buf.buf_operand` >>
  conj_tac >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  Cases_on `vv_location vv` >- suspend "snapshot_mem_none" >>
  Cases_on `x` >> simp[]
  >- suspend "snapshot_mem"
  >- suspend "snapshot_storage"
  >- suspend "snapshot_transient"
  >- suspend "snapshot_code"
  >> suspend "snapshot_calldata"
QED

Resume compile_create_snapshot_shape[snapshot_storage]:
  irule shape_step_ignore_bind >> qexists_tac `\u st. plain_operand st buf.buf_operand` >>
  conj_tac >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  irule shape_step_frame_from >> irule_at Any compile_slot_to_memory_shape >>
  qexists_tac `\st. plain_operand st buf.buf_operand` >>
  simp[] >> simp[shape_stable_def] >> metis_tac[plain_operand_mono]
QED
Resume compile_create_snapshot_shape[snapshot_transient]:
  irule shape_step_ignore_bind >> qexists_tac `\u st. plain_operand st buf.buf_operand` >>
  conj_tac >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  irule shape_step_frame_from >> irule_at Any compile_slot_to_memory_shape >>
  qexists_tac `\st. plain_operand st buf.buf_operand` >>
  simp[] >> simp[shape_stable_def] >> metis_tac[plain_operand_mono]
QED
Resume compile_create_snapshot_shape[snapshot_code]:
  irule shape_step_ignore_bind >> qexists_tac `\u st. plain_operand st buf.buf_operand` >>
  conj_tac >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  irule shape_step_conseq >> irule_at Any compile_imm_copy_to_memory_shape >> simp[]
QED
Resume compile_create_snapshot_shape[snapshot_mem_none]:
  simp[] >> irule shape_step_conseq >>
  irule_at Any compile_create_snapshot_memory_shape >> simp[]
QED
Resume compile_create_snapshot_shape[snapshot_mem]:
  irule shape_step_conseq >>
  irule_at Any compile_create_snapshot_memory_shape >> simp[]
QED
Resume compile_create_snapshot_shape[snapshot_calldata]:
  irule shape_step_conseq >>
  irule_at Any compile_create_snapshot_memory_shape >> simp[]
QED
Finalise compile_create_snapshot_shape[local]

Theorem compile_raw_create_shape[local]:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_expr_exists expr_shape_root bytecode_e /\
  ~supported_expr_exists expr_shape_root value_e /\
  ~supported_exprs_exists expr_shape_root ctor_args /\
  (case salt_e of NONE => T | SOME e => ~supported_expr_exists expr_shape_root e) ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_raw_create cfn cenv bytecode_e value_e ctor_args salt_e rof)
    (\v st. plain_operand st v)
Proof
  strip_tac >> simp[compile_raw_create_def] >>
  irule shape_step_bind >>
  qexists_tac `\vv st. cenv_shape_ok st cenv /\ value_shape_ok st vv` >>
  reverse conj_tac >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
    qexists_tac `\st. cenv_shape_ok st cenv` >>
    qexistsl [`\v st. value_shape_ok st v`, `\st. cenv_shape_ok st cenv`, `compiler_label`] >>
    simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `vv` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\p st. cenv_shape_ok st cenv /\ plain_operand st p` >>
  reverse conj_tac >- (irule shape_step_frame_from >>
    irule_at Any compile_create_snapshot_shape >>
    qexists_tac `\st. cenv_shape_ok st cenv` >> simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `bytecode` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\v st. (cenv_shape_ok st cenv /\ plain_operand st bytecode) /\ plain_operand st v` >>
  reverse conj_tac >- (irule shape_step_conseq >> irule_at Any lower_value_callback_shape >>
    qexists_tac `\st. cenv_shape_ok st cenv /\ plain_operand st bytecode` >> simp[] >>
    ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
    simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `value` >> BETA_TAC >>
  qabbrev_tac `B = \st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) [bytecode;value]` >>
  `shape_stable B` by (simp[Abbr `B`] >> ho_match_mp_tac shape_stable_conj >>
    simp[cenv_shape_ok_stable] >>
    mp_tac (Q.SPEC `[bytecode;value]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_bind >> qexists_tac `\len st. B st /\ plain_operand st len` >>
  reverse conj_tac >- suspend "raw_load" >> qx_gen_tac `len` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\data st. (B st /\ plain_operand st len) /\ plain_operand st data` >>
  reverse conj_tac >- suspend "raw_data" >> qx_gen_tac `data` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\pair st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) [value;FST pair;SND pair]` >>
  reverse conj_tac >- suspend "raw_ctor" >>
  qx_gen_tac `pair` >> PairCases_on `pair` >> simp[] >>
  irule shape_step_bind >>
  qexists_tac `\salt st. (cenv_shape_ok st cenv /\ EVERY (plain_operand st) [value;pair0;pair1]) /\ (case salt of NONE => T | SOME op => plain_operand st op)` >>
  reverse conj_tac >- suspend "raw_salt" >> qx_gen_tac `salt` >> BETA_TAC >>
  irule shape_step_conseq >> irule_at Any compile_create_dispatch_shape >> simp[]
QED

Resume compile_raw_create_shape[raw_load]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_op_plain >>
  qexists_tac `B` >> simp[Abbr `B`, GSYM CONJ_ASSOC] >>
  simp[shape_stable_def, plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
    lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
    mk_inst_def, label_positions_ok_def, inst_jump_labels_ok_def,
    is_terminator_def, is_param_opcode_def, is_read0_opcode_def]
QED
Resume compile_raw_create_shape[raw_data]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_op_plain >>
  qexists_tac `\st. B st /\ plain_operand st len` >>
  conj_tac >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
    simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[Abbr `B`, plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
    lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
    mk_inst_def, label_positions_ok_def, inst_jump_labels_ok_def,
    is_terminator_def, is_param_opcode_def, is_read0_opcode_def]
QED
Resume compile_raw_create_shape[raw_salt]:
  irule shape_step_frame_from >> irule_at Any compile_create_salt_shape >>
  qexists_tac `\st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) [value;pair0;pair1]` >>
  simp[] >> ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
  mp_tac (Q.SPEC `[value;pair0;pair1]` shape_stable_plain_operands) >> simp[]
QED
Resume compile_raw_create_shape[raw_ctor]:
  Cases_on `ctor_args = []` >> simp[]
  >- (irule shape_step_return >> simp[Abbr `B`]) >>
  qabbrev_tac `C = \st. B st /\ EVERY (plain_operand st) [len;data]` >>
  `shape_stable C` by (simp[Abbr `C`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
    mp_tac (Q.SPEC `[len;data]` shape_stable_plain_operands) >> simp[]) >>
  irule shape_step_bind >> qexists_tac `\buf st. C st /\ plain_operand st buf.buf_operand` >>
  reverse conj_tac >- (irule shape_step_conseq >> irule_at Any compile_alloc_buffer_shape_framed >>
    qexists_tac `C` >> simp[Abbr `C`]) >>
  qx_gen_tac `buf` >> BETA_TAC >>
  qabbrev_tac `D = \st. C st /\ plain_operand st buf.buf_operand` >>
  `shape_stable D` by (simp[Abbr `D`] >> ho_match_mp_tac shape_stable_conj >> simp[] >>
    simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. D st` >>
  reverse conj_tac >- (irule shape_step_frame_from >> irule_at Any compile_copy_memory_dynamic_shape >>
    qexists_tac `D` >> simp[Abbr `D`, Abbr `C`]) >> gen_tac >> BETA_TAC >>
  irule shape_step_bind >> qexists_tac `\src st. D st /\ plain_operand st src` >>
  reverse conj_tac >- (irule shape_step_frame_from >> irule_at Any compile_create_ctor_tuple_shape >>
    qexists_tac `D` >> simp[Abbr `D`, Abbr `C`, Abbr `B`]) >>
  qx_gen_tac `src` >> BETA_TAC >>
  irule shape_step_bind >> qexists_tac `\dst st. (D st /\ plain_operand st src) /\ plain_operand st dst` >>
  reverse conj_tac >- suspend "raw_destination" >> qx_gen_tac `dst` >> BETA_TAC >>
  irule shape_step_bind >> qexists_tac `\n st. D st /\ plain_operand st n` >>
  reverse conj_tac >- (irule shape_step_frame_from >> irule_at Any (cj 2 compile_abi_encode_shape) >>
    qexists_tac `D` >> simp[]) >> qx_gen_tac `args_len` >> BETA_TAC >>
  irule shape_step_bind >> qexists_tac `\total st. D st /\ plain_operand st total` >>
  reverse conj_tac >- suspend "raw_total" >> qx_gen_tac `total_op` >> BETA_TAC >>
  irule shape_step_return >> simp[Abbr `D`, Abbr `C`, Abbr `B`]
QED

Resume compile_raw_create_shape[raw_destination]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_op_plain >>
  qexists_tac `\st. D st /\ plain_operand st src` >>
  conj_tac >- (ho_match_mp_tac shape_stable_conj >> simp[] >>
    simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[Abbr `D`, Abbr `C`, plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
    lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
    mk_inst_def, label_positions_ok_def, inst_jump_labels_ok_def,
    is_terminator_def, is_param_opcode_def, is_read0_opcode_def] >>
  Cases_on `len` >> simp[stackPlanTypesTheory.is_label_operand_def]
QED
Resume compile_raw_create_shape[raw_total]:
  irule shape_step_conseq >> irule_at Any shape_step_emit_op_plain >>
  qexists_tac `D` >> simp[] >>
  simp[Abbr `D`, Abbr `C`, plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
    lowered_inst_ok_def, raw_opcode_ok_def, inst_shape_ok_def,
    mk_inst_def, label_positions_ok_def, inst_jump_labels_ok_def,
    is_terminator_def, is_param_opcode_def, is_read0_opcode_def] >>
  Cases_on `args_len` >> simp[stackPlanTypesTheory.is_label_operand_def]
QED
Finalise compile_raw_create_shape[local]

(* These two creation paths reserve statically bounded buffers. *)
Theorem compile_call_create_shape_widen:
  (!ce t child. ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\st. cenv_shape_ok st ce)
       (cfn ce t child) (\v st. value_shape_ok st v)) /\
  ~supported_exprs_exists expr_shape_root args /\
  (ck = CreateMinimalProxy \/ ck = RawCreate) ==>
  shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (compile_call cfn cenv ret_ty ty
      (CreateTarget ck has_salt rof order) args default_ret)
    (\v st. value_shape_ok st v)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[compile_call_def] >> irule shape_step_as_stack_val >>
  `shape_step internal compiler_label (\st. cenv_shape_ok st cenv)
    (do emit_inst INVALID [] []; return (Lit 0w) od) (\op st. plain_operand st op)` by
    (mp_tac invalid_expr_call_shape >>
     simp[shape_step_def, exprCallBoundsTheory.invalid_expr_call_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def, value_shape_ok_def] >>
     disch_tac >> rpt gen_tac >>
     Cases_on `emit_inst INVALID [] [] st` >> simp[] >> strip_tac >> gvs[] >>
     first_x_assum (qspec_then `st` mp_tac) >> simp[value_shape_ok_def]) >>
  Cases_on `args` >> simp[compile_create_call_def] >>
  Cases_on `t` >> simp[] >>
  rename1 `target_e::value_e::rest` >>
  Cases_on `ck = RawCreate` >> gvs[]
  >- suspend "raw_call" >>
  suspend "proxy_call"
QED

Resume compile_call_create_shape_widen[raw_call]:
  Cases_on `LENGTH rest < if has_salt then 1 else 0` >> simp[] >>
  irule compile_raw_create_shape >> simp[] >>
  gvs[supported_exprs_exists_every] >>
  Cases_on `has_salt` >> simp[] >>
  `rest <> []` by (Cases_on `rest` >> gvs[]) >>
  `rest = FRONT rest ++ [LAST rest]` by simp[APPEND_FRONT_LAST] >>
  qpat_x_assum `rest = _` (fn th =>
    qpat_x_assum `EVERY _ rest` (mp_tac o ONCE_REWRITE_RULE [th])) >>
  simp[EVERY_APPEND]
QED
Resume compile_call_create_shape_widen[proxy_call]:
  Cases_on `LENGTH rest < if has_salt then 1 else 0` >> simp[] >>
  gvs[supported_exprs_exists_every] >>
  irule shape_step_bind >>
  qexists_tac `\target st. cenv_shape_ok st cenv /\ plain_operand st target` >>
  reverse conj_tac >- (irule shape_step_conseq >> irule_at Any lower_value_callback_shape >>
    qexists_tac `\st. cenv_shape_ok st cenv` >> simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `target` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\value st. (cenv_shape_ok st cenv /\ plain_operand st target) /\ plain_operand st value` >>
  reverse conj_tac >- (irule shape_step_conseq >> irule_at Any lower_value_callback_shape >>
    qexists_tac `\st. cenv_shape_ok st cenv /\ plain_operand st target` >> simp[] >>
    ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
    simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `value` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\buf st. (cenv_shape_ok st cenv /\ plain_operand st value) /\ plain_operand st buf` >>
  reverse conj_tac >- (irule shape_step_frame_from >> irule_at Any compile_create_proxy_buf_shape >>
    qexists_tac `\st. cenv_shape_ok st cenv /\ plain_operand st value` >> simp[] >>
    ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
    simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `buf` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\salt st. (cenv_shape_ok st cenv /\ plain_operand st value /\ plain_operand st buf) /\ (case salt of NONE => T | SOME op => plain_operand st op)` >>
  reverse conj_tac >- suspend "proxy_salt" >> qx_gen_tac `salt` >> BETA_TAC >>
  irule shape_step_conseq >> irule_at Any compile_create_dispatch_shape >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED
Resume compile_call_create_shape_widen[proxy_salt]:
  irule shape_step_frame_from >> irule_at Any compile_create_salt_shape >>
  qexists_tac `\st. cenv_shape_ok st cenv /\ plain_operand st value /\ plain_operand st buf` >>
  simp[] >> conj_tac
  >- (Cases_on `has_salt` >> simp[] >> Cases_on `rest` >> gvs[]) >>
  ho_match_mp_tac shape_stable_conj >> simp[cenv_shape_ok_stable] >>
  mp_tac (Q.SPEC `[value;buf]` shape_stable_plain_operands) >> simp[]
QED

Finalise compile_call_create_shape_widen
