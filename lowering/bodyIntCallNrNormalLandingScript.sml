(* Normal statement landings execute the actual implicit release and RET. *)
Theory bodyIntCallNrNormalLanding
Ancestors
  bodyIntCallNrEpiloguePath bodyIntCallJointContract stmtSimReturn
  loweringStateRelDefs exprLoweringProps stmtLowering compileEnv

Theorem intcall_joint_normal_unlock_ret_path:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env ee sb u /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  fp.jc_root_ce.ce_nonreentrant = (nr,key,trans,view) /\
  (if nr then compile_nonreentrant_unlock key trans view sb
   else ((),sb)) = ((),su) /\
  emit_inst RET [fp.jc_rpc] [] su = ((),sf) /\
  fn_has_code sb sf fp.jc_func ==>
  gas_path fp.jc_ctx fp.jc_func u 0
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
      (return_unlock_state fp.jc_root_ce u))
Proof
  strip_tac >>
  `compile_return_unlock fp.jc_root_ce sb = ((),su)` by
    (Cases_on `nr` >> gvs[compile_return_unlock_def, comp_return_def]) >>
  irule intcall_unlock_ret_path >>
  conj_tac
  >- fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_def,
        state_rel_def] >>
  simp[] >> qexistsl [`fp.jc_rpc`, `sb`, `sf`, `su`] >> simp[] >>
  fs[intcall_joint_res_def, intcall_expr_res_def]
QED
