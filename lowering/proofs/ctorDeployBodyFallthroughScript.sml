(* The constructor fallthrough at one joint endpoint across horizons. *)
Theory ctorDeployBodyFallthrough
Ancestors
  ctorDeployMemoryRunPtrFrameRet ctorDeployLoweringFrameRet
  ctorReturnFrame bodyFullShared fragGasEmitCtrl bodyPtrDefs
  ctorDeployLoweringDefs ctorDeployDefs e2eDeployDefs
  compileEnv emitHelper stmtSimDefs stmtSimProps fragGasOriginPtr
  loweringPosts loweringStateRelDefs bodySim exprLoweringProps
  venomExecSemantics venomState vyperInterpreter vyperState

(* A fallthrough appends the zero-mark jump and epilogue at one endpoint
   for the whole family of valid horizons. *)
Theorem deploy_ctor_fallthrough_joint:
  !P H0 tops runtime_bc am tx imm cenv cenv' cx ee ctx func sb sj
   st_exit st_final exit_lbl nkey ut t G tn explicit.
    cx = deploy_evaluation_context tops am tx /\
    cenv.ce_is_ctor /\ same_frame cenv cenv' /\
    emit_inst JMP [Label exit_lbl] [] sb = ((), sj) /\
    fn_has_code sb sj func /\
    st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
    compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm
      st_exit = ((), st_final) /\
    fn_has_code st_exit st_final func /\ fn_inst_ids_distinct func /\
    LENGTH runtime_bc + imm_len tops < dimword(:256) /\
    (imm_len tops <> 0 ==> cenv.ce_imm_alloca = SOME imm /\
       !x. imm = Var x ==> not_fresh_at st_exit x) /\
    ~ctx_has_dalloca ctx /\ P H0 /\
    (!H. P H ==>
       stmt_state_rel H ctx func cenv' cx ee t /\
       ghost_inv_at (deploy_dead H tops runtime_bc am tx) (imm_len tops)
         NONE cenv' cx ee G tn t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?final G' tn'.
      (!H. P H ==>
        gas_origin_ptr_path
          (deploy_dead H tops runtime_bc am tx, imm_len tops, explicit,
           ctx, func, []) (t, G, tn) [] (Halt final, G', tn')) /\
      !H. P H ==>
        constructor_return_q H func cenv cx (LENGTH runtime_bc)
          (imm_len tops) F nkey NoneV (ee with scopes := []) (Halt final)
Proof
  rpt gen_tac >> strip_tac >>
  `cx_tops cx = tops` by
    simp[deploy_evaluation_context_def, gasContextTheory.cx_tops_def,
         vyperContextTheory.get_module_code_def, initial_evaluation_context_def] >>
  `cenv'.ce_is_ctor /\
   (imm_len tops <> 0 ==> cenv'.ce_imm_alloca = SOME imm /\
     !x. imm = Var x ==> not_fresh_at st_exit x)` by
    gvs[same_frame_def, compile_env_component_equality] >>
  qabbrev_tac `sx = jump_to exit_lbl t` >>
  `~sx.vs_halted /\ sx.vs_current_bb = st_exit.cs_current_bb /\
   sx.vs_inst_idx = 0 /\ ~block_is_terminated st_exit` by
    simp[Abbr `sx`, jump_to_def, block_is_terminated_def] >>
  `!H. P H ==>
     stmt_state_rel H ctx func cenv' cx ee sx /\
     ghost_inv_at (deploy_dead H tops runtime_bc am tx) (imm_len tops)
       NONE cenv' cx ee G tn sx /\ allocas_from (imm_len tops) t` by
    (gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
     simp[Abbr `sx`, stmt_state_rel_jump_to, ghost_inv_at_jump] >>
     fs[ghost_inv_at_def]) >>
  qspecl_then [`P`, `H0`, `tops`, `runtime_bc`, `am`, `tx`, `imm`,
    `st_exit`, `st_final`, `ctx`, `func`, `cenv'`, `cx`, `ee`, `sx`,
    `NONE`, `G`, `tn`, `explicit`]
    mp_tac constructor_epilogue_origin_ptr_path >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`P`, `H0`, `ctx`, `func`, `cenv`, `cenv'`, `cx`, `ee`,
    `sx`, `F`, `nkey`, `ut`, `LENGTH runtime_bc`, `imm_len tops`, `imm`,
    `st_exit`, `st_exit`, `st_final`]
    mp_tac constructor_exit_gas_path_horizons >>
  impl_tac >- simp[comp_return_def] >> strip_tac >>
  `final' = final` by metis_tac[gas_path_halt_unique] >> gvs[] >>
  qexistsl_tac [`final`, `G'`, `tn'`] >> simp[] >>
  gen_tac >> strip_tac >>
  `allocas_from (imm_len tops) t` by metis_tac[] >>
  `gas_origin_ptr_path (deploy_dead H tops runtime_bc am tx,
     imm_len tops, explicit, ctx, func, [])
     (t, G, tn) [] (OK sx, G, tn)` by
    (simp[Abbr `sx`] >> irule emit_jmp_origin_ptr >>
     simp[] >> qexistsl_tac [`sb`, `sj`] >> simp[]) >>
  drule gas_origin_ptr_path_append >> simp[] >>
  disch_then irule >> metis_tac[]
QED

