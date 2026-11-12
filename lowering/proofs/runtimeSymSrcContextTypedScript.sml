Theory runtimeSymSrcContextTyped
Ancestors
  runtimeSymSrcContext runtimeSymSrcEmission context compileEnv emitHelper loweringShapeDefs
  venomInst stackPlanTypes list

Theorem runtime_sym_with_byte_offset:
  ~is_label_operand base_op /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_with_byte_offset base_op off s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `off = 0` >>
  simp[compile_with_byte_offset_def, comp_return_def] >> strip_tac >> gvs[] >>
  qpat_assum `emit_op _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def]
QED

Theorem runtime_sym_copy_memory_dynamic:
  ~is_label_operand dst /\ ~is_label_operand src /\ ~is_label_operand len /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_copy_memory_dynamic dst src len s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_copy_memory_dynamic_def] >> strip_tac >>
  qpat_assum `emit_void _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]
QED

Theorem runtime_sym_bytestring_copy_len:
  ~is_label_operand src /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_bytestring_copy_len src s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_bytestring_copy_len_def, comp_bind_def] >>
  ntac 4 (pairarg_tac >> simp[]) >> strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_assum `emit_op NOT _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op ADD [_; Lit 31w] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op AND _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_assum `emit_op ADD [_; Lit 32w] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def]
QED

Theorem runtime_sym_store_bytestring:
  ~is_label_operand src /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_store_bytestring src dst s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_store_bytestring_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_assum `compile_bytestring_copy_len _ _ = _`
    (mp_then Any mp_tac runtime_sym_bytestring_copy_len) >> simp[] >> strip_tac >>
  qpat_assum `emit_void _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]
QED

Theorem runtime_sym_store_memory_typed_all:
  (!ce dst dty src sty s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory_typed ce dst dty src sty s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!ce dst src dtys stys doff soff s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_typed_copy_fields ce dst src dtys stys doff soff s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!ce dst dty src sty n s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_copy_sarray_typed ce dst dty src sty n s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!ce dst dty cap src sty s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_copy_dynarray_typed ce dst dty cap src sty s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!ce dst src dfs sfs doff soff s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_struct_typed_copy ce dst src dfs sfs doff soff s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s'))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- (simp[compile_store_memory_typed_def, comp_return_def])
  >- (simp[compile_store_memory_typed_def, comp_return_def])
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- (simp[compile_store_memory_typed_def, comp_return_def])
  >> suspend "struct"
QED

Resume runtime_sym_store_memory_typed_all[dispatch]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  Cases_on `is_word_type dty`
  >- (rpt (qpat_x_assum `!a. _` kall_tac) >>
      simp[comp_bind_def] >>
      pairarg_tac >> simp[] >> strip_tac >>
      qpat_assum `emit_op _ _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
      qpat_assum `emit_void _ _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]) >>
  Cases_on `is_bytestring_type dty /\ is_bytestring_type sty`
  >- (rpt (qpat_x_assum `!a. _` kall_tac) >> simp[] >>
      metis_tac[runtime_sym_store_bytestring]) >>
  Cases_on `acyclic_struct_metadata ce.ce_struct_fields`
  >- (qpat_assum `~is_word_type _` (fn th => rewrite_tac[th]) >>
      qpat_assum `~(is_bytestring_type _ /\ is_bytestring_type _)`
        (fn th => rewrite_tac[th]) >>
      qpat_assum `acyclic_struct_metadata _` (fn th => rewrite_tac[th]) >>
      strip_tac >> Cases_on `dty` >> Cases_on `sty` >>
      ntac 4 (qpat_x_assum `!a. _` mp_tac) >>
      qpat_x_assum `_ s = (u,s')` mp_tac >>
      simp[] >> rpt strip_tac >>
      imp_res_tac runtime_sym_copy_memory >>
      FIRST [first_assum ACCEPT_TAC, FAIL_TAC "recursive dispatch"]) >>
  rpt (qpat_x_assum `!a. _` kall_tac) >> simp[] >> strip_tac >>
  qpat_assum `emit_void _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]
QED

Resume runtime_sym_store_memory_typed_all[fields]:
  FAIL_TAC "fields"
QED
Resume runtime_sym_store_memory_typed_all[sarray]:
  FAIL_TAC "sarray"
QED
Resume runtime_sym_store_memory_typed_all[dynarray]:
  FAIL_TAC "dynarray"
QED
Resume runtime_sym_store_memory_typed_all[struct]:
  FAIL_TAC "struct"
QED
Finalise runtime_sym_store_memory_typed_all
