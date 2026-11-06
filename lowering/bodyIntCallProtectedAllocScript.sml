(* Allocation preserves the lower bound on every callee-owned allocation. *)
Theory bodyIntCallProtectedAlloc
Ancestors
  intCallFrame context emitHelper emitHelperProps exprLoweringProps compileEnv
  venomExecSemantics venomInst venomState rich_list list

Theorem alloc_buffer_allocas_above:
  compile_alloc_buffer sz sa = (buf,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK t /\ allocas_above lo s ==>
  allocas_above lo t
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_def,
      step_inst_base_def, mk_inst_def] >>
  gvs[AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `exec_alloca inst s _` >>
  drule (INST_TYPE [alpha |-> ``:256``] exec_alloca_allocas_above) >>
  disch_then (qspecl_then [`inst`, `n2w sz : bytes32`] mp_tac) >>
  simp[result_allocas_above_def]
QED
