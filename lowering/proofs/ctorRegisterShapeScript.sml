Theory ctorRegisterShape
Ancestors
  ctorDecoderShape loweringShapeProps loweringShapeDefs loweringShapeRules
  moduleLowering compileEnv context emitHelper abiEncoder unitShapeDefs venomInst

val ctor_opcode_tac =
  simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
       inst_jump_labels_ok_def, jump_label_ok_def, is_terminator_def,
       is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
       operand_case_not_label, plain_operand_def, label_or_plain_def,
       stackPlanTypesTheory.is_label_operand_def];

fun ctor_cenv_emit_bind live name cont =
  irule shape_step_bind >>
  qexists_tac (`\x st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) (x::` @ live @ `)`) >>
  conj_tac >- (qx_gen_tac name >> BETA_TAC >> cont) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) ` @ live,
    `\x st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) (x::` @ live @ `)`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_cenv_frame >>
  ho_match_mp_tac extbodies_emit_plain >> ctor_opcode_tac;

val ctor_decode_tail_tac =
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. cenv_shape_ok st cenv /\ T` >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) [dst; src; Lit 0w; Lit (n2w data_size)]`,
    `\u st. cenv_shape_ok st cenv /\ T`] >>
  conj_tac >- simp[] >> conj_tac
  >- (BETA_TAC >> rpt strip_tac >> drule_all cenv_decode_operand_plain >>
      simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
       operand_case_not_label] >> gvs[plain_operand_def]) >>
  conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_cenv_frame >>
  simp[] >> MATCH_ACCEPT_TAC (SRULE [] (cj 1 compile_abi_decode_dload_shape));

Theorem compile_decode_constructor_arg_shape[local]:
  !cenv name is_prim is_dynamic abi_size dec_info offset data_size.
    shape_step F compiler_label (\st. cenv_shape_ok st cenv)
      (compile_decode_args cenv
        [(name, is_prim, is_dynamic, abi_size, dec_info)]
        offset DLOAD (Lit (n2w data_size)) 0)
      (\u st. cenv_shape_ok st cenv)
Proof
  map_every qx_gen_tac [`cenv`, `name`, `prim`, `dyn`, `abi_size`,
    `dec_info`, `offset`, `data_size`] >>
  pure_rewrite_tac[compile_decode_args_def, LET_THM] >> BETA_TAC >>
  Cases_on `prim` >> pure_rewrite_tac[COND_CLAUSES]
  >- suspend "primitive" >>
  Cases_on `dyn` >> pure_rewrite_tac[COND_CLAUSES]
  >- suspend "dynamic" >>
  Cases_on `FLOOKUP cenv.ce_vars name` >>
  asm_simp_tac bool_ss [optionTheory.option_case_def]
  >- (irule shape_step_return >> simp[]) >>
  rename1 `FLOOKUP cenv.ce_vars name = SOME loc` >>
  Cases_on `var_location_decode_operand loc` >>
  asm_simp_tac bool_ss [optionTheory.option_case_def]
  >- (irule shape_step_return >> simp[]) >>
  rename1 `var_location_decode_operand loc = SOME dst` >>
  ctor_cenv_emit_bind `[]` `src` (suspend "static_tail")
QED
Resume compile_decode_constructor_arg_shape[static_tail]:
  ctor_decode_tail_tac
QED
Resume compile_decode_constructor_arg_shape[dynamic]:
  Cases_on `FLOOKUP cenv.ce_vars name` >>
  asm_simp_tac bool_ss [optionTheory.option_case_def]
  >- (irule shape_step_return >> simp[]) >>
  rename1 `FLOOKUP cenv.ce_vars name = SOME loc` >>
  Cases_on `var_location_decode_operand loc` >>
  asm_simp_tac bool_ss [optionTheory.option_case_def]
  >- (irule shape_step_return >> simp[]) >>
  rename1 `var_location_decode_operand loc = SOME dst` >>
  ctor_cenv_emit_bind `[]` `head`
    (ctor_cenv_emit_bind `[head]` `offv`
      (ctor_cenv_emit_bind `[offv; head]` `src` ctor_decode_tail_tac))
QED
Resume compile_decode_constructor_arg_shape[primitive]:
  ctor_cenv_emit_bind `[]` `src`
    (ctor_cenv_emit_bind `[src]` `v` (suspend "clamp"))
QED
Resume compile_decode_constructor_arg_shape[clamp]:
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. cenv_shape_ok st cenv /\ (EVERY (plain_operand st) [v] /\ T)` >>
  conj_tac >- suspend "store" >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) [v]`,
    `\u st. cenv_shape_ok st cenv /\ (EVERY (plain_operand st) [v] /\ T)`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_cenv_frame >>
  ho_match_mp_tac extbodies_frame >> qexists_tac `\st. EVERY (plain_operand st) [v]` >>
  simp_tac bool_ss [shape_stable_plain_operands] >>
  irule compile_abi_clamp_basetype_shape
QED
Resume compile_decode_constructor_arg_shape[store]:
  gen_tac >> BETA_TAC >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. cenv_shape_ok st cenv` >>
  conj_tac >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  Cases_on `FLOOKUP cenv.ce_vars name` >> asm_simp_tac bool_ss [optionTheory.option_case_def]
  >- (irule shape_step_return >> simp[]) >>
  rename1 `FLOOKUP cenv.ce_vars name = SOME loc` >>
  Cases_on `var_location_decode_operand loc` >> asm_simp_tac bool_ss [optionTheory.option_case_def]
  >- (irule shape_step_return >> simp[]) >>
  rename1 `var_location_decode_operand loc = SOME dst` >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) [dst; v]`,
    `\u st. cenv_shape_ok st cenv /\ EVERY (plain_operand st) [dst; v]`] >>
  conj_tac >- simp[] >> conj_tac
  >- (BETA_TAC >> rpt strip_tac >> drule_all cenv_decode_operand_plain >> simp[] >> gvs[]) >>
  conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_cenv_frame >>
  ho_match_mp_tac extbodies_emit_void_plain >> ctor_opcode_tac
QED
Finalise compile_decode_constructor_arg_shape

Theorem compile_register_constructor_args_shape:
  !args cenv offset data_size.
    shape_step F compiler_label (\st. cenv_shape_ok st cenv)
      (compile_register_constructor_args cenv args offset data_size)
      (\cenv' st. cenv_shape_ok st cenv' /\
                  cenv'.ce_return_pc = cenv.ce_return_pc)
Proof
  Induct >> rpt gen_tac
  >- (pure_rewrite_tac[compile_register_constructor_args_def] >>
      irule shape_step_return >> simp[]) >>
  PairCases_on `h` >> pure_rewrite_tac[compile_register_constructor_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> asm_simp_tac bool_ss [optionTheory.option_case_def] >>
  rename1 `FLOOKUP cenv.ce_vars h0 = SOME loc` >>
  Cases_on `var_location_memory_size loc` >> asm_simp_tac bool_ss [optionTheory.option_case_def] >>
  rename1 `var_location_memory_size loc = SOME sz` >>
  irule shape_step_bind >>
  qexists_tac `\buf st. cenv_shape_ok st cenv /\ plain_operand st buf.buf_operand` >>
  conj_tac >- suspend "allocated" >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`, `\st. cenv_shape_ok st cenv /\ T`,
    `\buf st. cenv_shape_ok st cenv /\ plain_operand st buf.buf_operand`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_cenv_frame >> irule compile_alloc_buffer_shape
QED
Resume compile_register_constructor_args_shape[allocated]:
  qx_gen_tac `buf` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\ce st. ce = (cenv with ce_vars updated_by
    (\m. m |+ (h0, PtrVar buf.buf_operand sz))) /\ cenv_shape_ok st ce` >>
  conj_tac >- suspend "registered" >>
  irule shape_step_return >> simp[] >> rpt strip_tac >>
  `cenv with ce_vars updated_by (\m. m |+ (h0, PtrVar buf.buf_operand sz)) =
   cenv with ce_vars := cenv.ce_vars |+ (h0, PtrVar buf.buf_operand sz)`
    by simp[compile_env_component_equality] >>
  asm_rewrite_tac[] >> irule cenv_shape_ok_ptr_update >> simp[]
QED
Resume compile_register_constructor_args_shape[registered]:
  qx_gen_tac `ce` >> BETA_TAC >>
  irule shape_step_conseq >>
  qexistsl_tac [`compiler_label`,
    `\st. cenv_shape_ok st ce /\
      ce = (cenv with ce_vars updated_by (\m. m |+ (h0, PtrVar buf.buf_operand sz)))`,
    `\cenv' st. cenv_shape_ok st cenv' /\ cenv'.ce_return_pc = cenv.ce_return_pc`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  ho_match_mp_tac extbodies_assume >> strip_tac >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. cenv_shape_ok st ce` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_conseq >>
      qexistsl_tac [`compiler_label`, `\st. cenv_shape_ok st ce`,
        `\cenv' st. cenv_shape_ok st cenv' /\ cenv'.ce_return_pc = ce.ce_return_pc`] >>
      conj_tac >- (gvs[]) >> conj_tac >- simp[] >> conj_tac >- simp[] >>
      first_x_assum irule) >>
  irule compile_decode_constructor_arg_shape
QED
Finalise compile_register_constructor_args_shape
