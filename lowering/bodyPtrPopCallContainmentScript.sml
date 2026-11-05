Theory bodyPtrPopCallContainment
Ancestors
  exprOpenTerminals intCallResult fragExec rich_list list
  exprLowering emitHelper compileEnv venomInst

Theorem pop_fn_has_code_current_member:
  fn_has_code sa sb fn /\ MEM i sb.cs_current_insts ==>
  MEM i (fn_insts fn)
Proof
  simp[fn_has_code_def] >> rpt strip_tac >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  gvs[IS_PREFIX_APPEND] >> gvs[MEM_APPEND]
QED

Theorem pop_compile_intcall_current_invoke:
  compile_call cfn cenv ret_ty ty (IntCall fid) args default_ret sa = (vv,sb) ==>
  ?i. MEM i sb.cs_current_insts /\ i.inst_opcode = INVOKE
Proof
  rpt gen_tac >> simp[compile_call_def] >>
  ntac 4 (pairarg_tac >> simp[]) >>
  IF_CASES_TAC
  >- (BasicProvers.TOP_CASE_TAC
      >- (simp[] >> pairarg_tac >> simp[] >>
          strip_tac >>
          gvs[emit_op_def, fresh_id_def, fresh_var_def, emit_def,
              comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_inst_def] >>
          dsimp[]) >>
      simp[] >> ntac 2 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      drule store_multi_results_shape >> strip_tac >>
      gvs[emit_multi_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      Cases_on `fresh_vars returns_count st3` >>
      gvs[fresh_id_def, emit_def, mk_inst_def] >> dsimp[]) >>
  pairarg_tac >> simp[] >> BasicProvers.TOP_CASE_TAC >>
  simp[] >> strip_tac >> gvs[] >>
  gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def,
      comp_return_def, mk_inst_def] >> dsimp[]
QED

Theorem pop_compile_intcall_fn_invoke:
  compile_call cfn cenv ret_ty ty (IntCall fid) args default_ret sa = (vv,sb) /\
  fn_has_code sa sb fn ==>
  ?i. MEM i (fn_insts fn) /\ i.inst_opcode = INVOKE
Proof
  rpt strip_tac >> drule pop_compile_intcall_current_invoke >> strip_tac >>
  qexists_tac `i` >> simp[] >>
  metis_tac[pop_fn_has_code_current_member]
QED
