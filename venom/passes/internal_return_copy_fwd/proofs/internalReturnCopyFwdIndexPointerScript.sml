Theory internalReturnCopyFwdIndexPointer
Ancestors
  internalReturnCopyFwdIndexProbe ptrDiscipline pointerConfinedDefs
  venomExecSemantics venomState venomInst finite_map words list memLocDefs
  unitShapeDefs venomWf relation contextCodegenRel codegenRel

Definition ircf_index_pointer_params_def:
  ircf_index_pointer_params nm = if nm = "callee" then {0:num} else {}
End

Theorem ircf_index_pointer_roots:
  ptr_roots ircf_index_pointer_params ircf_index_main = {} /\
  ptr_roots ircf_index_pointer_params ircf_index_fn = {"%src"; "%dst"} /\
  ptr_roots ircf_index_pointer_params ircf_index_callee = {"%buf"}
Proof
  simp[ptr_roots_def, alloca_roots_def, ircf_index_main_def,
    ircf_index_fn_def, ircf_index_callee_def, ircf_index_entry_def,
    ircf_index_changed_def, mk_raw_function_def, fn_insts_def,
    fn_insts_blocks_def, mk_inst_def, inst_output_def,
    ircf_index_pointer_params_def, EXISTS_OR_THM] >>
  simp[venomInstTheory.EXISTS_instruction, pred_setTheory.EXTENSION,
       DISJ_IMP_THM, EXISTS_OR_THM] >>
  simp[pred_setTheory.EXTENSION] >> dsimp[]
QED

Theorem ircf_index_pointer_pv:
  fn_pv ircf_index_pointer_params ircf_index_main = {} /\
  fn_pv ircf_index_pointer_params ircf_index_fn = {"%src"; "%dst"} /\
  fn_pv ircf_index_pointer_params ircf_index_callee = {"%buf"}
Proof
  rpt conj_tac >> simp[fn_pv_def, ircf_index_pointer_roots,
    pointer_derived_vars_def] >>
  EVAL_TAC >> pure_once_rewrite_tac[WhileTheory.OWHILE_THM] >>
  simp[] >> pure_once_rewrite_tac[WhileTheory.OWHILE_THM] >>
  simp[listTheory.SET_TO_LIST_INV]
QED

Theorem ircf_index_pointer_alloca_roots:
  alloca_roots ircf_index_main = {} /\
  alloca_roots ircf_index_fn = {"%src"; "%dst"} /\
  alloca_roots ircf_index_callee = {}
Proof
  simp[alloca_roots_def, ircf_index_main_def, ircf_index_fn_def,
       ircf_index_callee_def, ircf_index_entry_def, ircf_index_changed_def,
       fn_insts_def, fn_insts_blocks_def, mk_raw_function_def,
       mk_inst_def, inst_output_def, venomInstTheory.EXISTS_instruction,
       pred_setTheory.EXTENSION] >> dsimp[]
QED

Theorem ircf_index_pointer_derived:
  pointer_derived_vars ircf_index_fn {} = {} /\
  pointer_derived_vars ircf_index_callee {} = {}
Proof
  conj_tac >> simp[pointer_derived_vars_def] >> EVAL_TAC >>
  pure_once_rewrite_tac[WhileTheory.OWHILE_THM] >> simp[] >>
  pure_once_rewrite_tac[WhileTheory.OWHILE_THM] >> simp[]
QED

Theorem ircf_index_pointer_fn_ok:
  fn_ptr_ok ircf_index_pointer_params ircf_index_main /\
  fn_ptr_ok ircf_index_pointer_params ircf_index_fn /\
  fn_ptr_ok ircf_index_pointer_params ircf_index_callee
Proof
  simp[fn_ptr_ok_def, ircf_index_pointer_roots, ircf_index_pointer_pv,
       ircf_index_pointer_alloca_roots, ircf_index_pointer_derived] >>
  simp[ircf_index_fn_def, ircf_index_entry_def, ircf_index_changed_def,
    ircf_index_main_def, ircf_index_callee_def, mk_raw_function_def,
    fn_insts_def, fn_insts_blocks_def, mk_inst_def] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, ptr_use_ok_def,
    affine_pointer_ops_def, phi_pv_all_var_def, is_pointer_preserving_op_def,
    mem_write_ops_def, mem_read_ops_def, inst_output_def,
    ircf_index_pointer_params_def, decode_invoke_def] >>
  rpt strip_tac >> gvs[] >> EVAL_TAC >>
  simp[memLocDefsTheory.EXISTS_inst_access_ops]
QED
