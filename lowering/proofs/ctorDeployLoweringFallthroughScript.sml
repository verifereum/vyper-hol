(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   A body that falls off its end reaches the constructor's exit. *)
Theory ctorDeployLoweringFallthrough
Ancestors
  ctorDeployLoweringDefs ctorReturnFrame stmtSimDefs stmtSimProps bodySim
  exprLoweringProps compileEnv emitHelper venomExecSemantics venomState venomInst

(* A body that falls off its end at sb runs the jump to the exit block, the
   unlock and the epilogue (constructor_exit_run). *)
Theorem deploy_ctor_fallthrough:
  !tops rpolicy runtime_bc dunit
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func cx cenv' ee t.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    cenv.ce_is_ctor /\ cenv_top_ext cenv cenv' ee.scopes /\
    LENGTH runtime_bc + imm_len tops < dimword(:256) /\
    (nr ==> ut /\ storage_layout_safe cx /\ cx.nonreentrant_slot = SOME nkey) /\
    (imm_len tops <> 0 ==>
       cenv.ce_imm_alloca = SOME imm /\
       !x. imm = Var x ==> not_fresh_at st_epilogue x) /\
    stmt_state_rel dunit.cu_context func cenv' cx ee t /\ ~t.vs_halted /\
    ~block_is_terminated sb /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?fuel final.
      run_from fuel dunit.cu_context func t = Halt final /\
      constructor_return_q func cenv cx (LENGTH runtime_bc) (imm_len tops)
        nr nkey NoneV (ee with scopes := []) (Halt final)
Proof
  rpt gen_tac >> simp[deploy_ctor_code_def] >> strip_tac >>
  gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def, new_block_def] >>
  drule cenv_top_ext_same_frame >> strip_tac >>
  `?fuel final.
     run_from fuel dunit.cu_context func (jump_to exit_lbl t) = Halt final /\
     constructor_return_q func (cenv1 with ce_ctor_exit_label := SOME exit_lbl)
       cx (LENGTH runtime_bc) (imm_len tops) nr nkey NoneV
       (ee with scopes := []) (Halt final)` by
    (irule constructor_exit_run >> rpt conj_tac >|
     [gvs[], gvs[], gvs[jump_to_def], gvs[], gvs[jump_to_def],
      simp[jump_to_def] >> rpt (first_assum (irule_at Any)) >> gvs[],
      qexists_tac `cenv'` >> simp[stmt_state_rel_jump_to]]) >>
  qsuff_tac `?fuel'. run_from fuel' dunit.cu_context func t = Halt final`
  >- (strip_tac >> qexistsl_tac [`fuel'`, `final`] >> simp[]) >>
  irule run_from_jump_end >> simp[] >>
  qexistsl_tac [`fuel`, `mk_inst sb.cs_next_id JMP [Label exit_lbl] []`,
                `exit_lbl`, `sb`] >>
  rpt (first_assum (irule_at Any)) >>
  simp[mk_inst_def, is_terminator_def, step_inst_base_opcode_eqs]
QED
