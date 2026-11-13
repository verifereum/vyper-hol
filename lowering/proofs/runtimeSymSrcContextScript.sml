Theory runtimeSymSrcContext
Ancestors
  runtimeSymSrcEmission context exprLowering compileEnv emitHelper list
  loweringShapeDefs venomInst stackPlanTypes

Theorem runtime_sym_imm_load_word:
  ~is_label_operand off /\
  (!b. imm = SOME b ==> ~is_label_operand b) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_imm_load_word ctor imm off s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, comp_bind_def] >>
  rpt gen_tac >> strip_tac
  >- (drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >> simp[])
  >- (Cases_on `emit_op ADD [off; x] s` >> gvs[] >>
      `EVERY runtime_sym_inst (state_insts r) /\ ~is_label_operand q` by
        (qpat_assum `emit_op ADD _ _ = _`
          (mp_then Any mp_tac runtime_sym_emit_op) >> simp[]) >>
      qpat_assum `emit_op ILOAD _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[])
  >> drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >> simp[]
QED

Theorem runtime_sym_imm_store_word:
  ~is_label_operand off /\ ~is_label_operand v /\
  (!b. imm = SOME b ==> ~is_label_operand b) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_imm_store_word imm off v s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `imm` >>
  simp[compile_imm_store_word_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt gen_tac >> strip_tac
  >- (qpat_assum `emit_void _ _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]) >>
  Cases_on `emit_op ADD [x; off] s` >> gvs[] >>
  `EVERY runtime_sym_inst (state_insts r) /\ ~is_label_operand q` by
    (qpat_assum `emit_op ADD _ _ = _`
      (mp_then Any mp_tac runtime_sym_emit_op) >> simp[]) >>
  qpat_assum `emit_void _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]
QED

Theorem runtime_sym_ptr_load:
  ~is_label_operand op /\
  (!b. imm = SOME b ==> ~is_label_operand b) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_ptr_load ctor imm loc op s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `loc` >> simp[compile_ptr_load_def] >> strip_tac
  >- (qpat_assum `emit_op _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >> simp[])
  >- (qpat_assum `emit_op _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >> simp[])
  >- (qpat_assum `emit_op _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >> simp[])
  >- (drule_all runtime_sym_imm_load_word >> simp[]) >>
  qpat_assum `emit_op _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >> simp[]
QED

Theorem runtime_sym_ptr_store:
  ~is_label_operand dst /\ ~is_label_operand v /\
  (!b. imm = SOME b ==> ~is_label_operand b) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_ptr_store ctor imm loc dst v s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `loc` >> Cases_on `ctor` >> simp[compile_ptr_store_def] >> strip_tac
  >~ [`compile_imm_store_word _ _ _ _ = _`]
  >- (drule_all runtime_sym_imm_store_word >> simp[]) >>
  qpat_assum `emit_void _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]
QED

Theorem runtime_sym_alloc_buffer:
  EVERY runtime_sym_inst (state_insts s) /\
  compile_alloc_buffer sz s = (buf,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand buf.buf_operand
Proof
  simp[compile_alloc_buffer_def, comp_bind_def] >>
  Cases_on `emit_op ALLOCA [Lit (n2w sz)] s` >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  qpat_assum `emit_op _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_alloc_dynamic:
  ~is_label_operand sz /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_alloc_dynamic sz s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_alloc_dynamic_def] >> strip_tac >>
  qpat_assum `emit_op _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >> simp[]
QED

Theorem runtime_sym_copy_memory:
  ~is_label_operand dst /\ ~is_label_operand src /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_copy_memory dst src sz s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `sz` >> simp[compile_copy_memory_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  qpat_assum `emit_void _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_bytes_data_ptr:
  ~is_label_operand ptr_op /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_bytes_data_ptr ptr_op loc s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_bytes_data_ptr_def] >> strip_tac >>
  qpat_assum `emit_op _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_lit_byte_offset:
  ~is_label_operand op /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_lit_byte_offset op off s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `off = 0` >> simp[compile_lit_byte_offset_def, comp_return_def]
  >- (strip_tac >> gvs[]) >>
  Cases_on `op` >> simp[comp_return_def, is_label_operand_def] >>
  strip_tac >> gvs[is_label_operand_def] >>
  qpat_assum `emit_op _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_bytestring_length:
  ~is_label_operand op /\
  (!b. imm = SOME b ==> ~is_label_operand b) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_bytestring_length ctor imm op loc s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_bytestring_length_def] >> strip_tac >>
  drule_all runtime_sym_ptr_load >> simp[]
QED

Theorem runtime_sym_imm_copy_to_memory:
  !n s s' src dst off ctor imm u.
  ~is_label_operand src /\ ~is_label_operand dst /\
  (!b. imm = SOME b ==> ~is_label_operand b) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_imm_copy_to_memory ctor imm src dst n off s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Induct >- (simp[compile_imm_copy_to_memory_def, comp_return_def] >>
    rpt strip_tac >> gvs[]) >>
  simp[compile_imm_copy_to_memory_def] >>
  rpt gen_tac >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  ntac 4 (pairarg_tac >> simp[]) >> strip_tac >>
  qpat_assum `compile_lit_byte_offset src _ _ = _`
    (mp_then Any mp_tac runtime_sym_lit_byte_offset) >> simp[] >> strip_tac >>
  qpat_assum `compile_imm_load_word _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_imm_load_word) >> simp[] >> strip_tac >>
  qpat_assum `compile_lit_byte_offset dst _ _ = _`
    (mp_then Any mp_tac runtime_sym_lit_byte_offset) >> simp[] >> strip_tac >>
  qpat_assum `emit_void _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >> simp[] >> strip_tac >>
  first_x_assum irule >>
  qexistsl [`ctor`, `dst`, `imm`, `off + 32`] >>
  goal_assum (drule_at Any) >> simp[] >> qexists `src` >> simp[]
QED

Theorem runtime_sym_imm_store_words:
  !n s s' src dst off imm u.
  ~is_label_operand src /\ ~is_label_operand dst /\
  (!b. imm = SOME b ==> ~is_label_operand b) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_imm_store_words imm src dst n off s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Induct >- (simp[compile_imm_store_words_def, comp_return_def] >>
    rpt strip_tac >> gvs[]) >>
  simp[compile_imm_store_words_def] >> rpt gen_tac >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  ntac 4 (pairarg_tac >> simp[]) >> strip_tac >>
  qpat_assum `compile_lit_byte_offset src _ _ = _`
    (mp_then Any mp_tac runtime_sym_lit_byte_offset) >> simp[] >> strip_tac >>
  qpat_assum `emit_op _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_assum `compile_lit_byte_offset dst _ _ = _`
    (mp_then Any mp_tac runtime_sym_lit_byte_offset) >> simp[] >> strip_tac >>
  qpat_assum `compile_imm_store_word _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_imm_store_word) >> simp[] >> strip_tac >>
  first_x_assum irule >>
  qexistsl [`dst`, `imm`, `off + 32`] >>
  goal_assum (drule_at Any) >> simp[] >> qexists `src` >> simp[]
QED

Theorem runtime_sym_load_memory:
  ~is_label_operand op /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_load_memory op prim s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `prim` >> simp[compile_load_memory_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  qpat_assum `emit_op _ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >> simp[]
QED

Theorem runtime_sym_bytestring_word_count:
  ~is_label_operand src /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_bytestring_word_count src s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_bytestring_word_count_def, comp_bind_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op SHR _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def]
QED
