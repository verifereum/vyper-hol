Theory internalReturnCopyFwdIndexCfgProbe
Ancestors
  internalReturnCopyFwdIndexProbe internalReturnCopyFwdSim
  codegenReadyCompute o1PassContract venomWf venomInst ptrDiscipline

Definition ircf_index_cfg_entry_def:
  ircf_index_cfg_entry : basic_block =
    <| bb_label := "test"; bb_instructions := [
      mk_inst 20 RETPC_PARAM [Lit 0w] ["%pc"];
      mk_inst 28 JNZ [Lit 0w; Label "dead"; Label "return"] []] |>
End

Definition ircf_index_cfg_return_def:
  ircf_index_cfg_return : basic_block =
    <| bb_label := "return"; bb_instructions := [
      mk_inst 21 NOP [] [];
      mk_inst 22 RET [Var "%pc"] []] |>
End

Definition ircf_index_cfg_fn_def:
  ircf_index_cfg_fn = mk_raw_function "test"
    [ircf_index_cfg_entry; ircf_index_cfg_return; ircf_index_changed]
End

Definition ircf_index_cfg_ctx_def:
  ircf_index_cfg_ctx : venom_context =
    <| ctx_functions := [ircf_index_main; ircf_index_cfg_fn; ircf_index_callee];
       ctx_entry := SOME "main"; ctx_global_reserved := [] |>
End

Definition ircf_index_cfg_analysis_def:
  ircf_index_cfg_analysis = icf_build_ctx ircf_index_meta
    ircf_index_cfg_ctx.ctx_functions FEMPTY ircf_index_cfg_fn
End

Definition ircf_index_cfg_target_return_def:
  ircf_index_cfg_target_return = ircf_index_cfg_return with
    bb_instructions := [mk_inst 22 RET [Var "%pc"] []]
End

Definition ircf_index_cfg_target_fn_def:
  ircf_index_cfg_target_fn = ircf_index_cfg_fn with fn_blocks :=
    [ircf_index_cfg_entry; ircf_index_cfg_target_return;
     ircf_index_target_changed]
End

Theorem ircf_index_cfg_wf:
  wf_function ircf_index_main /\ wf_function ircf_index_cfg_fn /\
  wf_function ircf_index_callee
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem ircf_index_cfg_ssa:
  EVERY wf_ssa ircf_index_cfg_ctx.ctx_functions
Proof
  EVAL_TAC
QED

Theorem ircf_index_cfg_reachable:
  reachable_fn ircf_index_main = ircf_index_main /\
  reachable_fn ircf_index_cfg_fn = ircf_index_cfg_fn /\
  reachable_fn ircf_index_callee = ircf_index_callee
Proof
  `fn_reachable ircf_index_cfg_fn "test" /\
   fn_reachable ircf_index_cfg_fn "return" /\
   fn_reachable ircf_index_cfg_fn "dead"` by
    (simp[codegenReadyComputeTheory.fn_reachable_cfg_analyze,
          ircf_index_cfg_wf] >> EVAL_TAC) >>
  conj_tac
  >- (irule unitShapeDefsTheory.reachable_fn_single_block >>
      qexists_tac `HD ircf_index_main.fn_blocks` >> EVAL_TAC) >>
  reverse conj_tac
  >- (irule unitShapeDefsTheory.reachable_fn_single_block >>
      qexists_tac `HD ircf_index_callee.fn_blocks` >> EVAL_TAC) >>
  simp[unitShapeDefsTheory.reachable_fn_def, ircf_index_cfg_fn_def,
       mk_raw_function_def] >>
  fs[ircf_index_cfg_fn_def, mk_raw_function_def] >>
  fs[ircf_index_cfg_entry_def, ircf_index_cfg_return_def,
       ircf_index_changed_def, unitShapeDefsTheory.reachable_inst_def,
       mk_inst_def]
QED

Theorem ircf_index_cfg_retpc:
  (retpc_var ircf_index_main x <=> F) /\
  (retpc_var ircf_index_cfg_fn x <=> x = "%pc") /\
  (retpc_var ircf_index_callee x <=> x = "%retpc")
Proof
  conj_tac
  >- (simp[unitShapeDefsTheory.retpc_var_def] >>
      irule unitShapeDefsTheory.copy_phi_var_no_seed >>
      simp[ircf_index_main_def, mk_raw_function_def, fn_insts_def,
           fn_insts_blocks_def, mk_inst_def, DISJ_IMP_THM]) >>
  rewrite_tac[unitShapeDefsTheory.retpc_var_def] >>
  once_rewrite_tac[unitShapeDefsTheory.copy_phi_var_cases] >>
  simp[ircf_index_main_def, ircf_index_cfg_fn_def, ircf_index_callee_def,
       ircf_index_cfg_entry_def, ircf_index_cfg_return_def,
       ircf_index_changed_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, mk_inst_def, DISJ_IMP_THM,
       FORALL_AND_THM, EXISTS_OR_THM, SF DNF_ss]
QED

Theorem ircf_index_cfg_shape:
  o1_ctx_shape ircf_index_cfg_ctx
Proof
  simp[o1_ctx_shape_def, o1_fn_shape_def, ircf_index_cfg_ctx_def,
       ircf_index_cfg_wf, unitShapeDefsTheory.fn_shape_ok_def,
       unitShapeDefsTheory.opaque_use_ok_def,
       unitShapeDefsTheory.retpc_shape_ok_def, ircf_index_cfg_reachable,
       ircf_index_cfg_retpc] >>
  simp[ircf_index_main_def, ircf_index_cfg_fn_def, ircf_index_callee_def,
       ircf_index_cfg_entry_def, ircf_index_cfg_return_def,
       ircf_index_changed_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, mk_inst_def, DISJ_IMP_THM,
       FORALL_AND_THM, EXISTS_OR_THM, GSYM AND_IMP_INTRO,
       unitShapeDefsTheory.retpc_use_ok_def] >> rpt conj_tac >> EVAL_TAC >>
  rpt strip_tac >> gvs[] >>
  Cases_on `inst = mk_inst 1 INVOKE [Label "test"] []` >>
  gvs[mk_inst_def]
QED

Theorem ircf_index_cfg_alias_steps:
  icf_aliases_step (dfg_build_function ircf_index_cfg_fn) {"%dst"} =
    (F,{"%dst"}) /\
  icf_aliases_step (dfg_build_function ircf_index_cfg_fn) {"%src"} =
    (F,{"%src"})
Proof
  conj_tac >> simp[invokeCopyFwdCommonDefsTheory.icf_aliases_step_def] >>
  EVAL_TAC >> pure_rewrite_tac[listTheory.LIST_TO_SET,
    pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY] >> simp[]
QED

Theorem ircf_index_cfg_aliases:
  icf_collect_aliases (dfg_build_function ircf_index_cfg_fn) "%dst" = {"%dst"} /\
  icf_collect_aliases (dfg_build_function ircf_index_cfg_fn) "%src" = {"%src"}
Proof
  conj_tac >> rewrite_tac[invokeCopyFwdCommonDefsTheory.icf_collect_aliases_def] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >>
  simp[ircf_index_cfg_alias_steps] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >> simp[]
QED

Theorem ircf_index_cfg_roots:
  icf_assign_root (dfg_build_function ircf_index_cfg_fn) {} "%dst" = "%dst" /\
  icf_assign_root (dfg_build_function ircf_index_cfg_fn) {} "%src" = "%src"
Proof
  conj_tac >> EVAL_TAC
QED

Theorem ircf_index_cfg_other_static:
  EVERY ircf_no_dst_write_alias ircf_index_cfg_ctx.ctx_functions /\
  ~ctx_has_dalloca ircf_index_cfg_ctx
Proof
  conj_tac
  >- (mp_tac ircf_index_cfg_aliases >> mp_tac ircf_index_cfg_roots >>
      simp[invokeCopyFwdCommonDefsTheory.ircf_no_dst_write_alias_def,
           ircf_index_cfg_ctx_def, ircf_index_main_def,
           ircf_index_cfg_fn_def, ircf_index_callee_def,
           ircf_index_cfg_entry_def, ircf_index_cfg_return_def,
           ircf_index_changed_def, mk_raw_function_def, fn_insts_def,
           fn_insts_blocks_def, mk_inst_def, GSYM AND_IMP_INTRO,
           DISJ_IMP_THM, FORALL_AND_THM] >> rpt strip_tac >> gvs[] >>
      EVAL_TAC) >>
  EVAL_TAC
QED

Theorem ircf_index_cfg_static:
  o1_ctx_shape ircf_index_cfg_ctx /\
  EVERY wf_ssa ircf_index_cfg_ctx.ctx_functions /\
  EVERY ircf_no_dst_write_alias ircf_index_cfg_ctx.ctx_functions /\
  ~ctx_has_dalloca ircf_index_cfg_ctx
Proof
  simp[ircf_index_cfg_shape, ircf_index_cfg_ssa, ircf_index_cfg_other_static]
QED

Theorem ircf_index_cfg_dfg:
  dfg_get_def (dfg_build_function ircf_index_cfg_fn) "%dst" =
    SOME (mk_inst 24 ALLOCA [Lit 32w] ["%dst"]) /\
  dfg_get_def (dfg_build_function ircf_index_cfg_fn) "%src" =
    SOME (mk_inst 23 ALLOCA [Lit 32w] ["%src"]) /\
  icf_use_positions (dfg_build_function ircf_index_cfg_fn) "%src" =
    [(mk_inst 25 INVOKE [Label "callee"; Var "%src"] [],1);
     (mk_inst 26 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [],1)] /\
  icf_use_positions (dfg_build_function ircf_index_cfg_fn) "%dst" =
    [(mk_inst 26 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [],0)] /\
  icf_invoke_has_ret_buf ircf_index_meta ircf_index_cfg_ctx.ctx_functions
    (mk_inst 25 INVOKE [Label "callee"; Var "%src"] [])
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem ircf_index_cfg_ret_source:
  ircf_is_ret_buf_source ircf_index_cfg_analysis
    ircf_index_changed.bb_instructions "%src" 26 3
Proof
  simp[internalReturnCopyFwdDefsTheory.ircf_is_ret_buf_source_def,
       ircf_index_cfg_analysis_def,
       invokeCopyFwdCommonDefsTheory.icf_build_ctx_def, ircf_index_cfg_aliases,
       invokeCopyFwdCommonDefsTheory.icf_alias_use_positions_def,
       ircf_index_cfg_dfg] >> EVAL_TAC
QED

Theorem ircf_index_cfg_try_forward:
  ircf_try_forward ircf_index_cfg_analysis ircf_index_changed 3 =
    SOME ircf_index_raw_changed.bb_instructions
Proof
  mp_tac ircf_index_cfg_ret_source >>
  simp[ircf_index_changed_def, mk_inst_def, ircf_index_cfg_analysis_def,
       invokeCopyFwdCommonDefsTheory.icf_build_ctx_def] >> strip_tac >>
  simp[internalReturnCopyFwdDefsTheory.ircf_try_forward_def,
       ircf_index_changed_def, mk_inst_def,
       ircf_index_cfg_analysis_def, invokeCopyFwdCommonDefsTheory.icf_build_ctx_def,
       ircf_index_cfg_roots, ircf_index_cfg_dfg, ircf_index_cfg_aliases,
       invokeCopyFwdCommonDefsTheory.icf_is_alloca_def,
       invokeCopyFwdCommonDefsTheory.icf_matches_alloca_size_def,
       invokeCopyFwdCommonDefsTheory.icf_alias_use_positions_def,
       invokeCopyFwdCommonDefsTheory.icf_is_assign_output_use_def,
       ircf_index_raw_changed_def, passSharedDefsTheory.mk_nop_inst_def] >>
  EVAL_TAC
QED

Theorem ircf_index_cfg_changed_transform:
  ircf_transform_block ircf_index_cfg_analysis ircf_index_changed =
    (T,ircf_index_raw_changed)
Proof
  mp_tac ircf_index_cfg_try_forward >>
  simp[ircf_index_changed_def, ircf_index_raw_changed_def, mk_inst_def,
       passSharedDefsTheory.mk_nop_inst_def] >> strip_tac >>
  simp[internalReturnCopyFwdDefsTheory.ircf_transform_block_def,
       ircf_index_changed_def, rich_listTheory.COUNT_LIST_GENLIST,
       listTheory.GENLIST, listTheory.FOLDL, mk_inst_def,
       ircf_index_raw_changed_def, passSharedDefsTheory.mk_nop_inst_def]
QED

Theorem ircf_index_cfg_unchanged_blocks:
  ircf_transform_block a ircf_index_cfg_entry = (F,ircf_index_cfg_entry) /\
  ircf_transform_block a ircf_index_cfg_return = (F,ircf_index_cfg_return)
Proof
  simp[internalReturnCopyFwdDefsTheory.ircf_transform_block_def,
       ircf_index_cfg_entry_def, ircf_index_cfg_return_def,
       rich_listTheory.COUNT_LIST_GENLIST, listTheory.GENLIST,
       listTheory.FOLDL, mk_inst_def]
QED

Theorem ircf_index_cfg_fn_transform:
  ircf_transform_function ircf_index_meta ircf_index_cfg_ctx.ctx_functions
    FEMPTY ircf_index_cfg_fn = ircf_index_cfg_target_fn
Proof
  simp[internalReturnCopyFwdDefsTheory.ircf_transform_function_def,
       GSYM ircf_index_cfg_analysis_def] >>
  simp[ircf_index_cfg_fn_def, mk_raw_function_def,
       ircf_index_cfg_unchanged_blocks, ircf_index_cfg_changed_transform] >>
  simp[passSharedDefsTheory.clear_nops_function_def,
       passSharedDefsTheory.clear_nops_block_def,
       ircf_index_raw_changed_def, ircf_index_target_changed_def,
       ircf_index_cfg_target_return_def, ircf_index_cfg_target_fn_def,
       ircf_index_cfg_fn_def, mk_raw_function_def, ircf_index_changed_def,
       ircf_index_cfg_entry_def, ircf_index_cfg_return_def,
       passSharedDefsTheory.mk_nop_inst_def, mk_inst_def]
QED

Theorem ircf_index_cfg_ctx_transform:
  ircf_transform_ctx ircf_index_meta FEMPTY ircf_index_cfg_ctx =
    ircf_index_cfg_ctx with ctx_functions :=
      [ircf_index_main; ircf_index_cfg_target_fn; ircf_index_callee]
Proof
  mp_tac ircf_index_cfg_fn_transform >>
  simp[internalReturnCopyFwdDefsTheory.ircf_transform_ctx_def,
       ircf_index_cfg_ctx_def, ircf_index_main_transform,
       ircf_index_callee_transform]
QED

Theorem ircf_index_cfg_lookup_function:
  lookup_function "test"
    (ircf_transform_ctx ircf_index_meta FEMPTY ircf_index_cfg_ctx).ctx_functions =
    SOME ircf_index_cfg_target_fn
Proof
  simp[ircf_index_cfg_ctx_transform, lookup_function_def,
       ircf_index_main_def, ircf_index_cfg_target_fn_def,
       ircf_index_cfg_fn_def, mk_raw_function_def, listTheory.FIND_thm]
QED

Definition ircf_index_cfg_return_state_def:
  ircf_index_cfg_return_state s = (ircf_index_state s) with
    <| vs_vars := FEMPTY |+ ("%pc",s.vs_return_pc_token);
       vs_prev_bb := SOME "test"; vs_current_bb := "return";
       vs_inst_idx := 0 |>
End

Theorem ircf_index_cfg_entry_run:
  run_block k C ircf_index_cfg_entry (ircf_index_state s) =
    OK (ircf_index_cfg_return_state s)
Proof
  EVAL_TAC
QED

Theorem ircf_index_cfg_source_run:
  run_block k C ircf_index_cfg_return (ircf_index_cfg_return_state s) =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      ((ircf_index_cfg_return_state s) with vs_inst_idx := 1)
Proof
  EVAL_TAC
QED

Theorem ircf_index_cfg_target_run:
  run_block k C ircf_index_cfg_target_return (ircf_index_cfg_return_state s) =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      (ircf_index_cfg_return_state s)
Proof
  EVAL_TAC
QED

Theorem ircf_index_cfg_lookup_blocks:
  lookup_block (ircf_index_cfg_return_state s).vs_current_bb
    ircf_index_cfg_fn.fn_blocks = SOME ircf_index_cfg_return /\
  lookup_block (ircf_index_cfg_return_state s).vs_current_bb
    ircf_index_cfg_target_fn.fn_blocks = SOME ircf_index_cfg_target_return
Proof
  simp[ircf_index_cfg_return_state_def, ircf_index_cfg_fn_def,
       ircf_index_cfg_target_fn_def, mk_raw_function_def, lookup_block_def,
       ircf_index_cfg_entry_def, ircf_index_cfg_return_def,
       ircf_index_cfg_target_return_def, listTheory.FIND_thm]
QED

Theorem ircf_index_cfg_return_indices:
  !k m C C' s.
    ?r se te.
      run_block k C ircf_index_cfg_return (ircf_index_cfg_return_state s) =
        IntRet r se /\
      run_block m C' ircf_index_cfg_target_return (ircf_index_cfg_return_state s) =
        IntRet r te /\
      se.vs_inst_idx = 1 /\ te.vs_inst_idx = 0 /\
      se.vs_inst_idx <> te.vs_inst_idx
Proof
  rpt gen_tac >> simp[ircf_index_cfg_source_run, ircf_index_cfg_target_run] >>
  simp[ircf_index_cfg_return_state_def]
QED

Theorem ircf_index_cfg_return_no_taint_agree:
  run_block k C ircf_index_cfg_return (ircf_index_cfg_return_state s) =
    IntRet r se /\
  run_block m C' ircf_index_cfg_target_return (ircf_index_cfg_return_state s) =
    IntRet r' te ==>
  ~taint_agree D X tn se te
Proof
  simp[ircf_index_cfg_source_run, ircf_index_cfg_target_run] >>
  rpt strip_tac >> gvs[] >> drule taintAgreeTheory.taint_agree_frame >>
  simp[venomStateTheory.venom_state_component_equality,
       ircf_index_cfg_return_state_def]
QED
