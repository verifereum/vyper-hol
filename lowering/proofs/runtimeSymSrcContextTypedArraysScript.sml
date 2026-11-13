Theory runtimeSymSrcContextTypedArrays
Ancestors
  runtimeSymSrcContextTypedBase runtimeSymSrcContextCopy runtimeSymSrcContext
  runtimeSymSrcEmission context compileEnv emitHelper loweringShapeDefs
  venomInst stackPlanTypes list

Theorem runtime_sym_typed_array_setup:
  fresh_label a s0 = (cl,s1) /\ fresh_label b s1 = (bl,s2) /\
  fresh_label c s2 = (el,s3) /\ fresh_var s3 = (ctr,s4) /\
  emit_inst ASSIGN [Lit 0w] [ctr] s4 = (u1,s5) /\
  emit_inst JMP [Label cl] [] s5 = (u2,s6) /\
  new_block cl s6 = (u3,s7) /\
  emit_op LT [Var ctr; len] s7 = (lt,s8) /\
  emit_op ISZERO [lt] s8 = (done,s9) /\
  emit_inst JNZ [done; Label el; Label bl] [] s9 = (u4,s10) /\
  new_block bl s10 = (u5,s11) /\
  emit_op MUL [Var ctr; Lit (n2w ss)] s11 = (so,s12) /\
  emit_op MUL [Var ctr; Lit (n2w ds)] s12 = (dof,s13) /\
  emit_op ADD [src; so] s13 = (sp,s14) /\
  emit_op ADD [dst; dof] s14 = (dp,s15) /\
  ~is_label_operand src /\ ~is_label_operand dst /\ ~is_label_operand len /\
  EVERY runtime_sym_inst (state_insts s0) ==>
  EVERY runtime_sym_inst (state_insts s15) /\
  ~is_label_operand sp /\ ~is_label_operand dp /\ runtime_sym_label cl
Proof
  strip_tac >>
  ntac 3 (qpat_x_assum `fresh_label _ _ = _`
    (mp_then Any mp_tac runtime_sym_fresh_label) >> strip_tac) >>
  qpat_x_assum `fresh_var _ = _`
    (mp_then Any mp_tac runtime_sym_fresh_var) >> strip_tac >> gvs[] >>
  qpat_x_assum `emit_inst ASSIGN _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_assign) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_inst JMP _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_jump) >> simp[] >> strip_tac >>
  qpat_x_assum `new_block cl _ = _`
    (mp_then Any mp_tac runtime_sym_copy_new_block) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_op LT _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_op ISZERO _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_jnz) >> simp[] >> strip_tac >>
  qpat_x_assum `new_block bl _ = _`
    (mp_then Any mp_tac runtime_sym_copy_new_block) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_op MUL _ s11 = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_op MUL _ s12 = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_op ADD _ s13 = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_op ADD _ s14 = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[]
QED

Theorem runtime_sym_typed_array_tail:
  runtime_sym_label cl /\ EVERY runtime_sym_inst (state_insts s0) /\
  emit_op ADD [Var ctr; Lit 1w] s0 = (nc,s1) /\
  emit_inst ASSIGN [nc] [ctr] s1 = (u1,s2) /\
  emit_inst JMP [Label cl] [] s2 = (u2,s3) /\
  new_block el s3 = (u3,s4) ==>
  EVERY runtime_sym_inst (state_insts s4)
Proof
  strip_tac >>
  qpat_x_assum `emit_op ADD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_inst ASSIGN _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_assign) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_inst JMP _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_jump) >> simp[] >> strip_tac >>
  drule_all runtime_sym_copy_new_block >> simp[]
QED

Theorem runtime_sym_copy_sarray_typed_branch:
  (!dp sp s u s'.
    ~is_label_operand dp /\ ~is_label_operand sp /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory_typed ce dp dty sp sty s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !dst src n s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_copy_sarray_typed ce dst dty src sty n s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  disch_then (mk_asm "callback") >> rpt gen_tac >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  simp[NoAsms] >>
  Cases_on `type_memory_bytes ce dty = type_memory_bytes ce sty /\
            ~is_abi_dynamic ce.ce_struct_fields dty`
  >- (simp[] >> metis_tac[runtime_sym_copy_memory]) >>
  simp[] >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def, NoAsms] >>
  ntac 5 (pairarg_tac >> simp[]) >>
  ntac 5 (pairarg_tac >> simp[]) >>
  ntac 5 (pairarg_tac >> simp[]) >>
  ntac 5 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  `~is_label_operand (Lit (n2w n))` by simp[is_label_operand_def] >>
  drule_all runtime_sym_typed_array_setup >>
  simp[is_label_operand_def] >> strip_tac >>
  asm "callback" drule_all >> strip_tac >>
  drule_all runtime_sym_typed_array_tail >> simp[]
QED

Theorem runtime_sym_typed_dynarray_header:
  ~is_label_operand src /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s0) /\
  emit_op MLOAD [src] s0 = (len,s1) /\
  emit_op GT [len; Lit (n2w cap)] s1 = (big,s2) /\
  emit_op ISZERO [big] s2 = (ok,s3) /\
  emit_void ASSERT [ok] s3 = (u1,s4) /\
  emit_void MSTORE [dst; len] s4 = (u2,s5) /\
  emit_op ADD [src; Lit 32w] s5 = (sp,s6) /\
  emit_op ADD [dst; Lit 32w] s6 = (dp,s7) ==>
  EVERY runtime_sym_inst (state_insts s7) /\
  ~is_label_operand len /\ ~is_label_operand sp /\ ~is_label_operand dp
Proof
  strip_tac >>
  qpat_x_assum `emit_op MLOAD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_op GT _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_op ISZERO _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_void ASSERT _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_op ADD _ s5 = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_op ADD _ s6 = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def]
QED

Theorem runtime_sym_copy_dynarray_typed_branch:
  (!dp sp s u s'.
    ~is_label_operand dp /\ ~is_label_operand sp /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory_typed ce dp dty sp sty s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !dst src cap s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_copy_dynarray_typed ce dst dty cap src sty s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  disch_then (mk_asm "callback") >> rpt gen_tac >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def, NoAsms] >>
  ntac 4 (pairarg_tac >> simp[]) >>
  ntac 3 (pairarg_tac >> simp[]) >>
  Cases_on `type_memory_bytes ce dty = type_memory_bytes ce sty /\ dty = sty`
  >- (simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      drule_all runtime_sym_typed_dynarray_header >> strip_tac >>
      qpat_x_assum `emit_op MUL _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >>
      simp[is_label_operand_def] >> strip_tac >>
      drule_all runtime_sym_copy_memory_dynamic >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 5 (pairarg_tac >> simp[]) >>
  ntac 5 (pairarg_tac >> simp[]) >>
  ntac 5 (pairarg_tac >> simp[]) >>
  ntac 5 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule_all runtime_sym_typed_dynarray_header >> strip_tac >>
  drule_all runtime_sym_typed_array_setup >> strip_tac >>
  asm "callback" drule_all >> strip_tac >>
  drule_all runtime_sym_typed_array_tail >> simp[]
QED
