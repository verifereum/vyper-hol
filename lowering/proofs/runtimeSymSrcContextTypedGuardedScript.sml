Theory runtimeSymSrcContextTypedGuarded
Ancestors
  runtimeSymSrcContextTypedArrays runtimeSymSrcContextTypedBase
  runtimeSymSrcContextCopy runtimeSymSrcContext
  runtimeSymSrcEmission context compileEnv emitHelper loweringShapeDefs
  venomInst stackPlanTypes list

Theorem runtime_sym_copy_dynarray_typed_fast:
  type_memory_bytes ce dty = type_memory_bytes ce sty /\ dty = sty /\
  ~is_label_operand dst /\ ~is_label_operand src /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_copy_dynarray_typed ce dst dty cap src sty s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 4 (pairarg_tac >> simp[]) >>
  ntac 4 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule_all runtime_sym_typed_dynarray_header >> strip_tac >>
  qpat_x_assum `emit_op MUL _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  drule_all runtime_sym_copy_memory_dynamic >> simp[]
QED

Theorem runtime_sym_copy_dynarray_typed_guarded:
  (~(type_memory_bytes ce dty = type_memory_bytes ce sty /\ dty = sty) ==>
   (!dp sp s u s'.
    ~is_label_operand dp /\ ~is_label_operand sp /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory_typed ce dp dty sp sty s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s'))) ==>
  !dst src cap s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_copy_dynarray_typed ce dst dty cap src sty s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `type_memory_bytes ce dty = type_memory_bytes ce sty /\ dty = sty`
  >- (rpt strip_tac >> metis_tac[runtime_sym_copy_dynarray_typed_fast]) >>
  strip_tac >> ho_match_mp_tac runtime_sym_copy_dynarray_typed_branch >>
  metis_tac[]
QED
