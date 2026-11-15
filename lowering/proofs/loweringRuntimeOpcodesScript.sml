(* Opcode preservation for the ordinary runtime generator. *)
Theory loweringRuntimeOpcodes
Ancestors
  moduleLowering compileEnv context emitHelper loweringShapeDefs loweringShapeProps
  venomInst list pair supportedStmtTraverse
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeStmtReturns loweringFunctionOpcodes

local
  fun preserve ths = rpt (FIRST [
    IF_CASES_TAC >> gvs[] >> qid_spec_tac `st`,
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

Theorem opcode_every_guarded_body:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ce ty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty fbody st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_guarded_body ce nr key trans view fbody ret st)))
Proof
  strip_tac >>
  strip_tac >> simp[compile_guarded_body_def] >>
  preserve [UNDISCH opcode_every_nonreentrant_lock,
    UNDISCH opcode_every_nonreentrant_unlock]
QED

Theorem opcode_every_external_function_body:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ce ty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty fbody st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_external_function_body ce args nr key trans view fbody ret st)))
Proof
  strip_tac >>
  strip_tac >> simp[compile_external_function_body_def] >>
  preserve [UNDISCH opcode_every_register_positional_args,
    UNDISCH opcode_every_guarded_body]
QED

Theorem opcode_every_fallback_body:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ce ty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty fbody st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_fallback_body ce pay nr key trans view fbody ret st)))
Proof
  strip_tac >>
  strip_tac >> simp[compile_fallback_body_def] >>
  preserve [UNDISCH opcode_every_guarded_body]
QED

Theorem opcode_every_internal_function:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ce ty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty fbody st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_internal_function ce params rb nr key trans view ctor imm fbody ret st)))
Proof
  strip_tac >>
  strip_tac >> simp[compile_internal_function_def] >>
  preserve [UNDISCH opcode_every_internal_param_decls,
    UNDISCH opcode_every_materialize_internal_params,
    UNDISCH opcode_every_alloc_buffer, UNDISCH opcode_every_fixed_region,
    UNDISCH opcode_every_nonreentrant_lock, UNDISCH opcode_every_nonreentrant_unlock]
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
  (!ce ty ss st. ~supported_stmts_expr_exists expr_shape_root ss ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty ss st)))) ==>
  !fns. EVERY external_fn_shape_ok fns ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_external_fn_bodies fns st)))
Proof
  strip_tac >>
  strip_tac >> Induct >> simp[compile_external_fn_bodies_def, every_state_insts_return] >>
  qx_gen_tac `fn` >> PairCases_on `fn` >>
  simp[external_fn_shape_ok_def] >> strip_tac >>
  simp[compile_external_fn_bodies_def] >>
  preserve [UNDISCH opcode_every_entry_checks,
    UNDISCH opcode_every_external_function_body]
QED

Theorem opcode_every_internal_fn_bodies:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ce ty ss st. ~supported_stmts_expr_exists expr_shape_root ss ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty ss st)))) ==>
  !fns. EVERY internal_fn_shape_ok fns ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_internal_fn_bodies fns st)))
Proof
  strip_tac >>
  strip_tac >> Induct >> simp[compile_internal_fn_bodies_def, every_state_insts_return] >>
  qx_gen_tac `fn` >> PairCases_on `fn` >>
  simp[internal_fn_shape_ok_def] >> strip_tac >>
  simp[compile_internal_fn_bodies_def] >>
  preserve [UNDISCH opcode_every_internal_function]
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
  (!ce ty ss st. ~supported_stmts_expr_exists expr_shape_root ss ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty ss st)))) /\
  EVERY external_fn_shape_ok exts /\ EVERY internal_fn_shape_ok ints /\
  fallback_shape_ok fb ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_generate_runtime sels exts ints fb Linear buckets metadata dense info st)))
Proof
  strip_tac >>
  strip_tac >> simp[compile_generate_runtime_def] >>
  preserve [UNDISCH opcode_every_selector_dispatch_linear,
    UNDISCH opcode_every_external_fn_bodies,
    UNDISCH opcode_every_internal_fn_bodies,
    UNDISCH opcode_every_fallback_body, fallback_shape_ok_def] >>
  gvs[fallback_shape_ok_def] >> qid_spec_tac `st` >>
  simp[UNDISCH opcode_every_fallback_body]
QED

end
