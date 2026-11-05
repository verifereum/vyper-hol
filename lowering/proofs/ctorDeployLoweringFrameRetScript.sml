(* A piece of deploy_unit_execution_correct (ctorDeployLowering): the
   constructor's frame_ret_ok, from a valueless return's fragment, which is
   ADMITTED until proved.  Moved out of ctorReturnFrame, whose theorems stay
   kernel-closed. *)
Theory ctorDeployLoweringFrameRet
Ancestors
  ctorReturnFrame
  bodySim stmtSimReturn immutableDeployExecution nonreentrantSource loweringHalt
  moduleLowering stmtLowering stmtSimDefs stmtSimProps exprLoweringProps fragExec compileEnv
  vyperInterpreter vyperState vyperContext vyperStorageLayoutSafety
  venomExecSemantics venomState venomInst

(* Restated for the gas-observing stmt_frag (8e3374a7d): the source is now
   eval_stmt itself, and the post a gas_outcome.  ADMITTED (a piece): the proof
   below was written against the old stmt_frag (an explicit source result,
   a plain run); it needs the run to the exit to be a gas path with no
   readings.  Old proof kept here, commented out:

  strip_tac >>
  `body_cenv.ce_return_pc = NONE /\
   body_cenv.ce_ctor_exit_label = SOME exit_lbl` by
    gvs[same_frame_def, compile_env_component_equality] >>
  pure_rewrite_tac [stmt_frag_def] >> rpt gen_tac >> strip_tac >> disj2_tac >>
  `sb = sa with <|cs_next_id := sa.cs_next_id + 1;
     cs_current_insts := sa.cs_current_insts ++
       [mk_inst sa.cs_next_id JMP [Label exit_lbl] []]|>` by
    (qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, Once compile_stmt_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emitHelperTheory.emit_inst_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `stmt_state_rel ctx func body_cenv cx es (jump_to exit_lbl s0)` by
    simp[stmt_state_rel_jump_to] >>
  `?fuel final. run_from fuel ctx func (jump_to exit_lbl s0) = Halt final /\
     constructor_return_q func cenv cx rt cap nr nkey NoneV
       (es with scopes := []) (Halt final)` by
    (irule constructor_exit_run >> simp[jump_to_def] >> conj_tac
     >- (qexistsl [`imm`, `st_epilogue`, `st_exit`, `st_final`, `ut`] >> simp[]) >>
     qexists `body_cenv` >> gvs[jump_to_def]) >>
  `?fuel'. run_from fuel' ctx func s0 = Halt final` by
    (irule run_from_jump_end >> simp[] >>
     qexistsl [`fuel`, `mk_inst sa.cs_next_id JMP [Label exit_lbl] []`,
               `exit_lbl`, `sa`, `sb`] >>
     simp[mk_inst_def, is_terminator_def, Once step_inst_base_def]) >>
  goal_assum (drule_at Any) >> simp[exit_result_def, stmt_exit_def]
*)
Theorem constructor_return_none_frag:
  cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE /\
  cenv.ce_ctor_exit_label = SOME exit_lbl /\ same_frame cenv body_cenv /\
  st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
  (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
    st_exit = ((), st_epilogue) /\
  compile_constructor_epilogue rt cap imm st_epilogue = ((), st_final) /\
  fn_has_code st_exit st_final func /\ rt + cap < dimword(:256) /\
  (nr ==> ut /\ storage_layout_safe cx /\ cx.nonreentrant_slot = SOME nkey) /\
  (cap <> 0 ==> cenv.ce_imm_alloca = SOME imm /\
    (!x. imm = Var x ==> not_fresh_at st_epilogue x)) ==>
  stmt_frag ctx func cx lctx
    (constructor_return_q func cenv cx rt cap nr nkey) body_cenv
    (stmt_env body_cenv lctx NoneT (Return NONE))
    (eval_stmt cx (Return NONE)) es
Proof
  cheat
QED

Theorem constructor_frame_ret_ok:
  !ctx func cenv cx runtime_size immutables_len imm nr nkey ut exit_lbl
   st_exit st_epilogue st_final.
    cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE /\
    cenv.ce_ctor_exit_label = SOME exit_lbl /\
    st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
    (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
      st_exit = ((), st_epilogue) /\
    compile_constructor_epilogue runtime_size immutables_len imm
      st_epilogue = ((), st_final) /\
    fn_has_code st_exit st_final func /\
    runtime_size + immutables_len < dimword(:256) /\
    (nr ==> ut /\ storage_layout_safe cx /\
            cx.nonreentrant_slot = SOME nkey) /\
    (immutables_len <> 0 ==>
      cenv.ce_imm_alloca = SOME imm /\
      (!x. imm = Var x ==> not_fresh_at st_epilogue x)) ==>
    frame_ret_ok ctx func cx
      (constructor_return_q func cenv cx runtime_size immutables_len nr nkey)
      cenv NoneT
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac [frame_ret_ok_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `eo`
  >- (irule constructor_return_none_frag >> simp[] >>
      qexistsl [`imm`, `st_epilogue`, `st_exit`, `st_final`, `ut`] >>
      simp[]) >>
  gvs[vyperTypeSystemTheory.type_stmt_def]
QED

