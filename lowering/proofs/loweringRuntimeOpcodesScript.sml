(* Opcode preservation for the ordinary runtime generator. *)
Theory loweringRuntimeOpcodes
Ancestors
  moduleLowering compileEnv context emitHelper loweringShapeDefs loweringShapeProps
  venomInst list pair supportedStmtTraverse
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeStmtReturns loweringFunctionOpcodes


Definition package_body_avoids_def:
  package_body_avoids root ce body <=>
    EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults /\
    ~supported_stmts_expr_exists root body
End

Definition external_package_avoids_def:
  external_package_avoids root
    (label, ce, args, min_cds, payable, nr, nkey, trans, view, body, ty) <=>
    package_body_avoids root ce body
End

Definition internal_package_avoids_def:
  internal_package_avoids root
    (label, ce, params, ret_buf, nr, nkey, trans, view, ctor, imm, body, ty) <=>
    package_body_avoids root ce body
End

Definition fallback_package_avoids_def:
  fallback_package_avoids root NONE = T /\
  fallback_package_avoids root (SOME (ce, payable, nr, nkey, trans, view, body, ty)) =
    package_body_avoids root ce body
End

Theorem every_state_insts_defaults_bind:
  (!st. EVERY (\nd. ~supported_exprs_exists root (SND nd))
      (FST (m st)).ce_func_defaults) /\
  (!st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (m st)))) /\
  (!ce st. EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (comp_bind m f st)))
Proof
  rpt strip_tac >> simp[comp_bind_def] >> pairarg_tac >> gvs[] >>
  metis_tac[FST, SND]
QED

local
  fun preserve ths = rpt (FIRST [
    CHANGED_TAC (simp[stmt_return_bind]),
    IF_CASES_TAC >> gvs[] >> qid_spec_tac `st`,
    ho_match_mp_tac every_state_insts_defaults_bind >>
      (conj_tac >- (simp ths >> NO_TAC)) >> conj_tac,
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp (ths @ [opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst,
      every_state_insts_return, every_state_insts_get,
      every_state_insts_fresh_label, every_state_insts_new_block])),
    CASE_TAC >> gvs[] >> qid_spec_tac `st`]);
in

Theorem opcode_every_register_positional_args:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !args ce off. !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_register_positional_args ce args off st)))
Proof
  strip_tac >>
  Induct >> simp[compile_register_positional_args_def, every_state_insts_return] >>
  qx_gen_tac `arg` >> PairCases_on `arg` >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[compile_register_positional_args_def] >>
  preserve [UNDISCH opcode_every_alloc_buffer, UNDISCH opcode_every_decode_args]
QED

Theorem opcode_every_internal_param_decls:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !params idx. !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_internal_param_decls params idx st)))
Proof
  strip_tac >>
  Induct >> simp[compile_internal_param_decls_def, every_state_insts_return] >>
  qx_gen_tac `param` >> PairCases_on `param` >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[compile_internal_param_decls_def] >> preserve []
QED

Theorem opcode_every_materialize_internal_params:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !params ce. !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (materialize_internal_params ce params st)))
Proof
  strip_tac >>
  Induct >> simp[materialize_internal_params_def, every_state_insts_return] >>
  qx_gen_tac `param` >> PairCases_on `param` >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[materialize_internal_params_def] >> preserve []
QED

Theorem register_positional_args_defaults:
  !args ce off st.
    (FST (compile_register_positional_args ce args off st)).ce_func_defaults =
      ce.ce_func_defaults
Proof
  Induct >> simp[compile_register_positional_args_def, comp_return_def] >>
  qx_gen_tac `arg` >> PairCases_on `arg` >> rpt gen_tac >>
  simp[compile_register_positional_args_def] >>
  rpt (CASE_TAC >> gvs[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem materialize_internal_params_defaults:
  !params ce st.
    (FST (materialize_internal_params ce params st)).ce_func_defaults =
      ce.ce_func_defaults
Proof
  Induct >> simp[materialize_internal_params_def, comp_return_def] >>
  qx_gen_tac `param` >> PairCases_on `param` >> rpt gen_tac >>
  simp[materialize_internal_params_def] >>
  rpt (CASE_TAC >> gvs[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem opcode_every_guarded_body:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ce ty st.
    EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty fbody st)))) ==>
  EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_guarded_body ce nr key trans view fbody ret st)))
Proof
  strip_tac >>
  strip_tac >> strip_tac >> simp[compile_guarded_body_def] >>
  preserve [UNDISCH opcode_every_nonreentrant_lock,
    UNDISCH opcode_every_nonreentrant_unlock]
QED

Theorem opcode_every_external_function_body:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ce ty st.
    EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty fbody st)))) ==>
  EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_external_function_body ce args nr key trans view fbody ret st)))
Proof
  strip_tac >>
  strip_tac >> strip_tac >> simp[compile_external_function_body_def] >>
  preserve [register_positional_args_defaults,
    UNDISCH opcode_every_register_positional_args,
    UNDISCH opcode_every_guarded_body] >>
  rpt strip_tac >> irule (UNDISCH opcode_every_guarded_body) >>
  TRY (qexists_tac `root`) >> simp[] >> metis_tac[]
QED

Theorem opcode_every_fallback_body:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ce ty st.
    EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty fbody st)))) ==>
  EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_fallback_body ce pay nr key trans view fbody ret st)))
Proof
  strip_tac >>
  strip_tac >> strip_tac >> simp[compile_fallback_body_def] >>
  preserve [UNDISCH opcode_every_guarded_body] >>
  rpt strip_tac >> irule (UNDISCH opcode_every_guarded_body) >>
  TRY (qexists_tac `root`) >> simp[] >> metis_tac[]
QED

Theorem opcode_every_internal_function:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ce ty st.
    EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty fbody st)))) ==>
  EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_internal_function ce params rb nr key trans view ctor imm fbody ret st)))
Proof
  strip_tac >> strip_tac >> strip_tac >>
  simp[compile_internal_function_def] >>
  let val ths = [materialize_internal_params_defaults,
        UNDISCH opcode_every_internal_param_decls,
        UNDISCH opcode_every_materialize_internal_params,
        UNDISCH opcode_every_alloc_buffer, UNDISCH opcode_every_fixed_region,
        UNDISCH opcode_every_nonreentrant_lock,
        UNDISCH opcode_every_nonreentrant_unlock]
  in
    preserve ths >> disch_tac >> qid_spec_tac `st` >> preserve ths
  end
QED

Theorem opcode_every_entry_checks:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_entry_checks mincds pay st)))
Proof
  strip_tac >>
  simp[compile_entry_checks_def] >> preserve []
QED

Theorem opcode_every_external_fn_bodies:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ce ty ss st.
    EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
    ~supported_stmts_expr_exists root ss ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty ss st)))) ==>
  !fns. EVERY (external_package_avoids root) fns ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_external_fn_bodies fns st)))
Proof
  strip_tac >>
  strip_tac >> Induct >> simp[compile_external_fn_bodies_def, every_state_insts_return] >>
  qx_gen_tac `fn` >> PairCases_on `fn` >>
  simp[external_package_avoids_def, package_body_avoids_def] >> strip_tac >>
  simp[compile_external_fn_bodies_def] >>
  preserve [UNDISCH opcode_every_entry_checks,
    UNDISCH opcode_every_external_function_body] >>
  rpt strip_tac >> irule (UNDISCH opcode_every_external_function_body) >>
  TRY (qexists_tac `root`) >> simp[] >> metis_tac[]
QED

Theorem opcode_every_internal_fn_bodies:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ce ty ss st.
    EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
    ~supported_stmts_expr_exists root ss ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty ss st)))) ==>
  !fns. EVERY (internal_package_avoids root) fns ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_internal_fn_bodies fns st)))
Proof
  strip_tac >>
  strip_tac >> Induct >> simp[compile_internal_fn_bodies_def, every_state_insts_return] >>
  qx_gen_tac `fn` >> PairCases_on `fn` >>
  simp[internal_package_avoids_def, package_body_avoids_def] >> strip_tac >>
  simp[compile_internal_fn_bodies_def] >>
  preserve [UNDISCH opcode_every_internal_function] >>
  rpt strip_tac >> irule (UNDISCH opcode_every_internal_function) >>
  TRY (qexists_tac `root`) >> simp[] >> metis_tac[]
QED

Theorem opcode_every_selector_checks:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !sels mid. !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_selector_checks mid sels st)))
Proof
  strip_tac >>
  Induct >> simp[compile_selector_checks_def, every_state_insts_return] >>
  qx_gen_tac `sel` >> PairCases_on `sel` >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[compile_selector_checks_def] >> preserve []
QED

Theorem opcode_every_selector_dispatch_linear:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_selector_dispatch_linear sels fb st)))
Proof
  strip_tac >>
  simp[compile_selector_dispatch_linear_def] >>
  preserve [UNDISCH opcode_every_selector_checks]
QED

Theorem opcode_every_generate_runtime_linear:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ce ty ss st.
    EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
    ~supported_stmts_expr_exists root ss ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty ss st)))) /\
  EVERY (external_package_avoids root) exts /\ EVERY (internal_package_avoids root) ints /\
  (fallback_package_avoids root) fb ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_generate_runtime sels exts ints fb Linear buckets metadata dense info st)))
Proof
  strip_tac >>
  strip_tac >> simp[compile_generate_runtime_def] >>
  preserve [UNDISCH opcode_every_selector_dispatch_linear,
    UNDISCH opcode_every_external_fn_bodies,
    UNDISCH opcode_every_internal_fn_bodies,
    UNDISCH opcode_every_fallback_body, fallback_package_avoids_def, package_body_avoids_def] >>
  rpt strip_tac >>
  FIRST [irule (UNDISCH opcode_every_external_fn_bodies),
         irule (UNDISCH opcode_every_internal_fn_bodies),
         irule (UNDISCH opcode_every_fallback_body)] >>
  TRY (qexists_tac `root`) >>
  gvs[fallback_package_avoids_def, package_body_avoids_def] >> metis_tac[]
QED

end
