(* Resource transport along loop-control instructions. *)
Theory bodyIntCallFamStmtForTransport
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtJump bodySim compileEnv
  stmtSimProps exprLoweringProps loweringPosts intCallFrame bodyMemoryDefs
  venomState venomExecSemantics finite_map

Theorem intcall_joint_res_update_var:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  not_local_ptr ce es.scopes x /\
  (!op. fp.jc_reserved op ==> op <> Var x) ==>
  intcall_joint_res fp ce env es sa (update_var x w s)
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es (update_var x w s)` by
    (irule stmt_state_rel_update_var >> fs[intcall_joint_res_def]) >>
  `!op. fp.jc_reserved op ==>
     eval_operand op (update_var x w s) = eval_operand op s` by
    (rpt strip_tac >> Cases_on `op` >>
     fs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `ce.ce_return_pc = fp.jc_root_ce.ce_return_pc /\
   ce.ce_return_buf = fp.jc_root_ce.ce_return_buf` by
    fs[intcall_joint_res_def, same_frame_def, compile_env_component_equality] >>
  fs[intcall_joint_res_def] >>
  fs[allocas_above_def, update_var_def] >>
  rpt conj_tac
  >- metis_tac[]
  >- (rpt strip_tac >>
      qpat_x_assum `!n p k. local_region ce _ _ _ _ _ ==> _` irule >>
      fs[local_region_def, not_local_ptr_def, lookup_var_def, FLOOKUP_UPDATE] >>
      metis_tac[])
  >- (fs[intcall_frame_ok_def] >> metis_tac[])
  >- (fs[ret_pc_ok_def, intcall_frame_ok_def, eval_operand_def,
         lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[])
  >- (Cases_on `fp.jc_rb` >> fs[return_buf_frame_def] >>
      rename1 `fp.jc_rb = SOME rb` >> PairCases_on `rb` >> fs[return_buf_frame_def] >>
      fs[intcall_frame_ok_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  metis_tac[]
QED
