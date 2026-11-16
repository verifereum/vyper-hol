Theory runtimeSymSrcContextValues
Ancestors
  runtimeSymSrcContext runtimeSymSrcInterfaces runtimeSymSrcEmission
  exprLowering context stackPlanTypes
  compileEnv emitHelper list loweringShapeDefs

Theorem runtime_sym_unwrap_value_cond:
  (!op loc bytes words ctor imm s v s'.
    ~is_label_operand op /\
    (!b. imm = SOME b ==> ~is_label_operand b) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_ensure_in_memory op loc bytes words ctor imm s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) ==>
  runtime_sym_env ce /\ runtime_sym_value vv /\
  EVERY runtime_sym_inst (state_insts s) /\
  unwrap_value ce vv s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  strip_tac >> Cases_on `vv` >>
  simp[unwrap_value_def, runtime_sym_value_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  `!b. ce.ce_imm_alloca = SOME b ==> ~is_label_operand b` by
    gvs[runtime_sym_env_def] >>
  Cases_on `is_word_type t` >> gvs[]
  >- (drule_all runtime_sym_ptr_load >> simp[]) >>
  Cases_on `p.ptr_location` >> gvs[comp_return_def] >> metis_tac[]
QED

Theorem runtime_sym_bytestring_widen_copy:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_bytestring_widen_copy n v m s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_bytestring_widen_copy_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  drule_all runtime_sym_copy_memory >> simp[]
QED

Theorem runtime_sym_materialize_vv_cond:
  (!vv s op s'. runtime_sym_value vv /\
    EVERY runtime_sym_inst (state_insts s) /\ unwrap_value ce vv s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!src dst dt st s u s'. ~is_label_operand src /\ ~is_label_operand dst /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory ce src dst dt st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_value vv /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_materialize_vv ce ty vv s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  strip_tac >>
  simp[compile_materialize_vv_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 3 (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  qpat_x_assum `!vv s op s'. _` drule_all >> strip_tac >>
  qpat_x_assum `!src dst dt st s s'. _` drule_all >> simp[]
QED

Theorem runtime_sym_ifexp_arm_cond:
  (!vv s op s'. runtime_sym_value vv /\
    EVERY runtime_sym_inst (state_insts s) /\ unwrap_value ce vv s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!src dst dt st s u s'. ~is_label_operand src /\ ~is_label_operand dst /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory ce src dst dt st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_value vv /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_ifexp_arm ce rt at vv s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  strip_tac >>
  Cases_on `is_word_type rt \/ same_memory_layout ce at rt` >>
  simp[compile_ifexp_arm_def]
  >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  ntac 3 (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  qpat_x_assum `!vv s op s'. _` drule_all >> strip_tac >>
  qpat_x_assum `!src dst dt st s s'. _` drule_all >> simp[]
QED

Theorem runtime_sym_snapshot_vv_cond:
  (!vv s op s'. runtime_sym_value vv /\
    EVERY runtime_sym_inst (state_insts s) /\ unwrap_value ce vv s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!ty vv s op s'. runtime_sym_value vv /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_materialize_vv ce ty vv s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_value vv /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_snapshot_vv ce copy vv s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> Cases_on `is_word_type (vv_type vv)` >>
  simp[compile_snapshot_vv_def, comp_bind_def]
  >- (pairarg_tac >> simp[comp_return_def] >> strip_tac >> gvs[] >>
      qpat_x_assum `!vv s op s'. _` drule_all >>
      simp[runtime_sym_value_def]) >>
  Cases_on `copy` >> simp[comp_return_def, comp_bind_def]
  >- (pairarg_tac >> simp[comp_return_def] >> strip_tac >> gvs[] >>
      qpat_x_assum `!ty vv s op s'. _` drule_all >>
      simp[runtime_sym_value_def, mk_ptr_def]) >>
  strip_tac >> gvs[]
QED

Theorem runtime_sym_load_bytestring_as_word:
  shift <> CODESIZE /\ shift <> CODECOPY /\
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  load_bytestring_as_word v shift s = ((op,bits),s') ==>
  EVERY runtime_sym_inst (state_insts s') /\
  ~is_label_operand op /\ ~is_label_operand bits
Proof
  Cases_on `shift = SAR` >>
  simp[load_bytestring_as_word_def, comp_bind_def, comp_return_def] >>
  ntac 3 (pairarg_tac >> simp[]) >>
  ntac 3 (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  qpat_assum `emit_op MLOAD [v] s = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op MLOAD [data_ptr] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac
  >- (qmatch_asmsub_rename_tac `emit_op ISZERO [length] st3` >>
      Cases_on `emit_op ISZERO [length] st3` >>
      Cases_on `emit_op ISZERO [q] r` >> gvs[] >>
      qpat_assum `emit_op ISZERO [length] _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
      qpat_assum `emit_op ISZERO [q] _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
      qpat_assum `emit_op MUL [data; _] _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
      qpat_assum `emit_op SUB _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
      qpat_assum `emit_op MUL [sub32; _] _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
      qmatch_asmsub_rename_tac `emit_op SAR [num_zero_bits; data'] st6` >>
      Cases_on `emit_op SAR [num_zero_bits; data'] st6` >> gvs[] >>
      qpat_assum `emit_op SAR _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[]) >>
  qpat_assum `emit_op SUB _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op MUL _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op shift _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[]
QED
