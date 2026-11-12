Theory runtimeSymSrcBinops
Ancestors
  runtimeSymSrcEmission runtimeSymSrcInterfaces exprLowering compileEnv
  emitHelper loweringShapeDefs venomInst list stackPlanTypes

Theorem runtime_sym_clamp:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_clamp v ty s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `is_signed_type ty` >>
  simp[compile_clamp_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >>
  pairarg_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_clamp_and_return:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  clamp_and_return v ty s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[clamp_and_return_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  drule_all runtime_sym_clamp >> simp[]
QED

Theorem runtime_sym_wrap_truncate:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  wrap_truncate v ty s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[wrap_truncate_def, comp_return_def] >> strip_tac >> gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_safe_add:
  ~is_label_operand x /\ ~is_label_operand y /\
  EVERY runtime_sym_inst (state_insts s) /\ compile_safe_add x y ty s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_add_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[] >> strip_tac
  >- (drule_all runtime_sym_clamp_and_return >> simp[])
  >- (drule_all runtime_sym_clamp_and_return >> simp[]) >>
  gvs[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
      runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_safe_sub:
  ~is_label_operand x /\ ~is_label_operand y /\
  EVERY runtime_sym_inst (state_insts s) /\ compile_safe_sub x y ty s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_sub_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[] >> strip_tac
  >- (drule_all runtime_sym_clamp_and_return >> simp[])
  >- (drule_all runtime_sym_clamp_and_return >> simp[]) >>
  gvs[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
      runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_mul_overflow:
  ~is_label_operand x /\ ~is_label_operand y /\ ~is_label_operand res /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_mul_overflow_check x y res sign bits s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `sign` >> Cases_on `bits = 256` >>
  simp[compile_mul_overflow_check_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
      runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_safe_mul:
  ~is_label_operand x /\ ~is_label_operand y /\
  EVERY runtime_sym_inst (state_insts s) /\ compile_safe_mul x y ty s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `type_bits ty > 128` >> Cases_on `is_decimal_type ty` >>
  Cases_on `is_signed_type ty` >> Cases_on `type_bits ty < 256` >>
  simp[compile_safe_mul_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_return_def]) >> strip_tac >> gvs[] >>
  qpat_x_assum `emit_op MUL _ _ = _`
    (mp_then (Pat `emit_op _ _ _ = _`) mp_tac runtime_sym_emit_op) >>
  simp[] >> strip_tac >>
  rpt (qpat_x_assum `compile_mul_overflow_check _ _ _ _ _ _ = _`
    (mp_then (Pat `compile_mul_overflow_check _ _ _ _ _ _ = _`)
      mp_tac runtime_sym_mul_overflow) >> simp[] >> strip_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _`
    (mp_then (Pat `emit_op _ _ _ = _`) mp_tac runtime_sym_emit_op) >>
    simp[is_label_operand_def] >> strip_tac) >>
  gvs[] >> drule_all runtime_sym_clamp_and_return >> simp[]
QED

Theorem runtime_sym_safe_div:
  ~is_label_operand x /\ ~is_label_operand y /\
  EVERY runtime_sym_inst (state_insts s) /\ compile_safe_div x y ty s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `is_signed_type ty` >> Cases_on `type_bits ty = 256` >>
  Cases_on `type_bits ty < 256` >>
  simp[compile_safe_div_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
      runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  rpt (qpat_x_assum `clamp_and_return _ _ _ = _`
    (mp_then (Pat `clamp_and_return _ _ _ = _`) mp_tac runtime_sym_clamp_and_return) >>
    simp[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
         runtime_sym_inst_def, mk_inst_def, is_label_operand_def]) >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_safe_mod:
  ~is_label_operand x /\ ~is_label_operand y /\
  EVERY runtime_sym_inst (state_insts s) /\ compile_safe_mod x y ty s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `is_signed_type ty` >>
  simp[compile_safe_mod_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
      runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_safe_decimal_div:
  ~is_label_operand x /\ ~is_label_operand y /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_safe_decimal_div x y divisor ty s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_safe_decimal_div_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  drule_at (Pat `clamp_and_return _ _ _ = _`) runtime_sym_clamp_and_return >>
  simp[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
       runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  fs[state_insts_def, all_blocks_def, EVERY_APPEND] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_safe_pow:
  ~is_label_operand x /\ ~is_label_operand y /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_safe_pow x y ty bl el s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `bl` >> Cases_on `el` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_pow_def] >>
  rpt IF_CASES_TAC >>
  simp[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_return_def]) >> strip_tac >> gvs[] >>
  rpt (qpat_x_assum `compile_clamp _ _ _ = _`
    (mp_then (Pat `compile_clamp _ _ _ = _`) mp_tac runtime_sym_clamp) >>
    simp[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
         runtime_sym_inst_def, mk_inst_def, is_label_operand_def]) >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
      runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_neg:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_neg v ty s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_neg_def] >> pairarg_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
      runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_invert:
  runtime_sym_env ce /\ ~is_label_operand v /\
  EVERY runtime_sym_inst (state_insts s) /\ compile_invert v ty ce s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `ty` >> simp[compile_invert_def] >> strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_compare:
  ~is_label_operand x /\ ~is_label_operand y /\
  EVERY runtime_sym_inst (state_insts s) /\ compile_compare bop x y ty s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `bop` >> Cases_on `is_uint256 ty` >>
  simp[compile_compare_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_inst_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
      runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_binop:
  ~is_label_operand x /\ ~is_label_operand y /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_binop bop x y ty bl el s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `bop` >> simp[compile_binop_def]
  >~ [`compile_safe_add _ _ _ _ = _`] >- MATCH_ACCEPT_TAC runtime_sym_safe_add
  >~ [`compile_safe_sub _ _ _ _ = _`] >- MATCH_ACCEPT_TAC runtime_sym_safe_sub
  >~ [`compile_safe_mul _ _ _ _ = _`] >- MATCH_ACCEPT_TAC runtime_sym_safe_mul
  >~ [`compile_safe_mod _ _ _ _ = _`] >- MATCH_ACCEPT_TAC runtime_sym_safe_mod
  >~ [`compile_safe_pow _ _ _ _ _ _ = _`] >- MATCH_ACCEPT_TAC runtime_sym_safe_pow
  >~ [`compile_safe_decimal_div`] >-
    (Cases_on `is_decimal_type ty` >> simp[] >>
     FIRST [MATCH_ACCEPT_TAC runtime_sym_safe_decimal_div,
            MATCH_ACCEPT_TAC runtime_sym_safe_div])
  >>~- ([`compile_compare _ _ _ _ _ = _`],
    rpt strip_tac >> drule_all runtime_sym_compare >> simp[]) >>
  rpt strip_tac >>
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  Cases_on `is_uint256 ty` >>
  gvs[builtinSimpleTheory.compile_select_def, wrap_truncate_def] >>
  rpt IF_CASES_TAC >>
  gvs[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_inst_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
      runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED
