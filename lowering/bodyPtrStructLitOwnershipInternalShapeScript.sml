Theory bodyPtrStructLitOwnershipInternalShape
Ancestors
  list loweringShapeProps loweringShapeRules loweringShapeDefs
  moduleLowering compileEnv context emitHelper unitShapeDefs venomInst stackPlanTypes

Theorem structlit_internal_cenv_install_shape:
  !cenv rb pc st.
    cenv_static_ok cenv /\
    (case rb of NONE => T | SOME op => plain_operand st op) /\
    retpc_operand st pc ==>
    cenv_shape_ok st
      (cenv with <|ce_return_buf :=
        (case (rb,cenv.ce_return_buf) of
          (SOME op,SOME (MemLoc off sz)) => SOME (PtrVar op sz)
        | _ => cenv.ce_return_buf);
        ce_return_pc := SOME (PtrVar pc 0)|>)
Proof
  rpt gen_tac >> strip_tac >>
  `cenv_shape_ok st
     (cenv with <|ce_return_pc := NONE; ce_ctor_exit_label := NONE|>)` by
    (irule cenv_static_ok_shape_ok >>
     gvs[cenv_static_ok_def] >> metis_tac[]) >>
  `!loc. cenv.ce_return_buf = SOME loc ==> ?off sz. loc = MemLoc off sz`
    by metis_tac[cenv_static_ok_def] >>
  fs[cenv_shape_ok_def] >>
  Cases_on `rb` >> Cases_on `cenv.ce_return_buf` >>
  rw[loc_shape_ok_def] >> res_tac >> gvs[loc_shape_ok_def]
QED


Theorem structlit_compile_fixed_region_with_id_shape:
  !sz. shape_step T compiler_label (\st. T)
    (compile_fixed_region_with_id sz)
    (\r st. plain_operand st (SND r).buf_operand)
Proof
  gen_tac >> simp[compile_fixed_region_with_id_def] >>
  irule shape_step_bind >> qexists `\id st. T` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_id >> simp[shape_stable_def]) >>
  qx_gen_tac `id` >> BETA_TAC >>
  irule shape_step_bind >> qexists `\out st. plain_operand st (Var out)` >>
  reverse conj_tac
  >- (mp_tac (Q.SPECL [`T`, `compiler_label`, `\st. T`]
        shape_step_fresh_var) >> simp[shape_stable_def]) >>
  qx_gen_tac `out` >> BETA_TAC >>
  irule shape_step_ignore_bind >> qexists `\u st. plain_operand st (Var out)` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  irule shape_step_conseq >> irule_at Any shape_step_emit >>
  qexists `\st. plain_operand st (Var out)` >>
  simp[mk_inst_def, label_or_plain_def, is_label_operand_def] >>
  simp[shape_stable_def, plain_operand_mono] >>
  qexists `compiler_label` >>
  simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, is_read0_opcode_def,
       label_positions_ok_def, operand_case_not_label, is_terminator_def] >>
  conj_tac
  >- (rpt strip_tac >> drule_all plain_operand_mono >> simp[]) >>
  simp[plain_operand_def, is_label_operand_def]
QED

Theorem structlit_compile_internal_imm_alloc_shape:
  !is_ctor imm_len. shape_step T compiler_label (\st. T)
    (if is_ctor /\ imm_len > 0 then
       do alloc_result <- compile_fixed_region_with_id imm_len;
          return (SOME (SND alloc_result).buf_operand) od
     else return NONE) (\imm st. !b. imm = SOME b ==> plain_operand st b)
Proof
  rpt gen_tac >> IF_CASES_TAC >> simp[]
  >- (irule shape_step_bind >>
      qexists `\r st. plain_operand st (SND r).buf_operand` >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
      irule structlit_compile_fixed_region_with_id_shape) >>
  irule shape_step_return >> simp[]
QED

Theorem structlit_param_op_shape[local]:
  shape_step T compiler_label (\st. T)
    (emit_op PARAM [Lit (n2w idx)]) (\op st. plain_operand st op)
Proof
  mp_tac (Q.SPECL [`T`, `compiler_label`, `\st. T`, `PARAM`,
    `[Lit (n2w idx)]`] shape_step_emit_op) >>
  simp[shape_stable_def, label_or_plain_def, plain_operand_def,
       is_label_operand_def, lowered_inst_ok_def, mk_inst_def,
       raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
       is_read0_opcode_def, label_positions_ok_def,
       operand_case_not_label, is_terminator_def]
QED

Theorem structlit_compile_internal_param_decls_shape:
  !params idx.
    shape_step T compiler_label (\st. T)
      (compile_internal_param_decls params idx)
      (\r st. EVERY (\(name,is_stack,op). plain_operand st op) (FST r))
Proof
  Induct_on `params`
  >- (gen_tac >> simp[compile_internal_param_decls_def] >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[compile_internal_param_decls_def] >>
  irule shape_step_bind >> qexists `\op st. plain_operand st op` >>
  reverse conj_tac >- irule structlit_param_op_shape >>
  gen_tac >> BETA_TAC >> irule shape_step_bind >>
  qexists `\r st. plain_operand st x /\
    EVERY (\(name,is_stack,op). plain_operand st op) (FST r)` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  first_x_assum (qspec_then `idx + 1` assume_tac) >>
  drule shape_step_frame >>
  disch_then (qspec_then `\st. plain_operand st x` mp_tac) >>
  simp[] >> disch_then irule >>
  rw[shape_stable_def] >> metis_tac[plain_operand_mono]
QED

Theorem structlit_cenv_shape_ok_var_update:
  !st ce op name sz.
    cenv_shape_ok st ce /\ plain_operand st op ==>
    cenv_shape_ok st
      (ce with ce_vars updated_by (\m. m |+ (name, PtrVar op sz)))
Proof
  rw[cenv_shape_ok_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[loc_shape_ok_def] >>
  Cases_on `name = n` >> gvs[loc_shape_ok_def] >> metis_tac[]
QED

Theorem structlit_captured_params_shape_stable:
  !captured. shape_stable
    (\st. EVERY (\(name,is_stack,op). plain_operand st op) captured)
Proof
  rw[shape_stable_def, EVERY_MEM] >>
  PairCases_on `e` >> gvs[] >>
  first_x_assum (qspec_then `(e0,e1,e2)` mp_tac) >> simp[] >>
  strip_tac >> drule_all plain_operand_mono >> simp[]
QED

Theorem structlit_alloca_shape[local]:
  shape_step T compiler_label (\st. T)
    (emit_op ALLOCA [Lit (n2w sz)]) (\op st. plain_operand st op)
Proof
  mp_tac (Q.SPECL [`T`, `compiler_label`, `\st. T`, `ALLOCA`,
    `[Lit (n2w sz)]`] shape_step_emit_op) >>
  simp[shape_stable_def, label_or_plain_def, plain_operand_def,
       is_label_operand_def, lowered_inst_ok_def, mk_inst_def,
       raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
       is_read0_opcode_def, label_positions_ok_def,
       operand_case_not_label, is_terminator_def]
QED

Theorem structlit_mstore_shape[local]:
  !ptr value. ~is_label_operand ptr /\ ~is_label_operand value ==>
  shape_step T compiler_label
    (\st. plain_operand st ptr /\ plain_operand st value)
    (emit_void MSTORE [ptr;value])
    (\u st. plain_operand st ptr /\ plain_operand st value)
Proof
  rpt gen_tac >> strip_tac >>
  irule shape_step_conseq >> irule_at Any shape_step_emit_void >>
  qexists `\st. plain_operand st ptr' /\ plain_operand st value` >>
  simp[shape_stable_def, label_or_plain_def, lowered_inst_ok_def,
       mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
       inst_jump_labels_ok_def, is_read0_opcode_def,
       label_positions_ok_def, operand_case_not_label, is_terminator_def] >>
  qexists `compiler_label` >> simp[] >>
  rpt strip_tac >> metis_tac[plain_operand_mono]
QED

Theorem structlit_materialize_internal_params_shape:
  !captured ce.
    shape_step T compiler_label
      (\st. cenv_shape_ok st ce /\
        EVERY (\(name,is_stack,op). plain_operand st op) captured)
      (materialize_internal_params ce captured)
      (\ce' st. cenv_shape_ok st ce' /\ ce'.ce_return_pc = ce.ce_return_pc)
Proof
  Induct_on `captured`
  >- (gen_tac >> simp[materialize_internal_params_def] >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[materialize_internal_params_def] >> Cases_on `h1` >> simp[]
  >- suspend "stack" >>
  first_x_assum (qspec_then
    `ce with ce_vars updated_by (\m. m |+ (h0, PtrVar h2
      (case FLOOKUP ce.ce_vars h0 of SOME (MemLoc _ sz) => sz | _ => 0)))`
    mp_tac) >>
  simp[shape_step_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[structlit_cenv_shape_ok_var_update] >>
  disch_then irule >> irule structlit_cenv_shape_ok_var_update >> simp[]
QED

Resume structlit_materialize_internal_params_shape[stack]:
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
  >- (first_x_assum (qspec_then `ce` mp_tac) >>
      simp[shape_step_def] >> metis_tac[]) >>
  Cases_on `x` >> simp[]
  >~ [`emit_op ALLOCA _`] >- suspend "allocate" >>
  first_x_assum (qspec_then `ce` mp_tac) >>
  simp[shape_step_def] >> metis_tac[]
QED

Resume structlit_materialize_internal_params_shape[allocate]:
  rename1 `emit_op ALLOCA [Lit (n2w sz)]` >>
  irule shape_step_bind >>
  qexists `\ptr st. cenv_shape_ok st ce /\ plain_operand st h2 /\
    EVERY (\(name,is_stack,op). plain_operand st op) captured /\
    plain_operand st ptr` >> reverse conj_tac
  >- suspend "alloc_rule" >>
  gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
  qexists `\u st. cenv_shape_ok st ce /\ plain_operand st h2 /\
    EVERY (\(name,is_stack,op). plain_operand st op) captured /\
    plain_operand st x` >> reverse conj_tac
  >- suspend "store_rule" >>
  gen_tac >> BETA_TAC >>
  first_x_assum (qspec_then
    `ce with ce_vars updated_by (\m. m |+ (h0, PtrVar x sz))` mp_tac) >>
  simp[shape_step_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[structlit_cenv_shape_ok_var_update] >>
  disch_then irule >> irule structlit_cenv_shape_ok_var_update >> simp[]
QED

Resume structlit_materialize_internal_params_shape[alloc_rule]:
  assume_tac (Q.SPEC `sz` (GEN_ALL structlit_alloca_shape)) >>
  drule shape_step_frame >>
  disch_then (qspec_then `\st. cenv_shape_ok st ce /\ plain_operand st h2 /\
    EVERY (\(name,is_stack,op). plain_operand st op) captured` mp_tac) >>
  simp[GSYM CONJ_ASSOC] >> disch_then irule >>
  ho_match_mp_tac shape_stable_conj >> conj_tac
  >- simp[cenv_shape_ok_stable] >>
  ho_match_mp_tac shape_stable_conj >> conj_tac
  >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[structlit_captured_params_shape_stable]
QED

Resume structlit_materialize_internal_params_shape[store_rule]:
  simp[shape_step_def] >> rpt strip_tac >>
  `~is_label_operand x /\ ~is_label_operand h2` by
    fs[plain_operand_def] >>
  qspecl_then [`x`, `h2`] mp_tac structlit_mstore_shape >>
  simp[] >> disch_then assume_tac >>
  `shape_stable (\st. cenv_shape_ok st ce /\
    EVERY (\(name,is_stack,op). plain_operand st op) captured)` by
    (ho_match_mp_tac shape_stable_conj >>
     simp[cenv_shape_ok_stable, structlit_captured_params_shape_stable]) >>
  drule shape_step_frame >>
  disch_then (qspec_then `\st. cenv_shape_ok st ce /\
    EVERY (\(name,is_stack,op). plain_operand st op) captured` mp_tac) >>
  simp[shape_step_def] >> strip_tac >> first_x_assum drule_all >> simp[]
QED
Finalise structlit_materialize_internal_params_shape
