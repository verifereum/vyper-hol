Theory internalReturnCopyFwdIndexProbe
Ancestors
  internalReturnCopyFwdPlan internalReturnCopyFwdDefs reachableFnSim venomExecSemantics venomState
  venomInst ptrDiscipline passSimulationDefs finite_map words list
  invokeCopyFwdCommonDefs callLayoutDefs taintAgree

Definition ircf_index_entry_def:
  ircf_index_entry : basic_block =
    <| bb_label := "test"; bb_instructions := [
      mk_inst 20 RETPC_PARAM [Lit 0w] ["%pc"];
      mk_inst 21 NOP [] [];
      mk_inst 22 RET [Var "%pc"] []] |>
End

Definition ircf_index_changed_def:
  ircf_index_changed : basic_block =
    <| bb_label := "dead"; bb_instructions := [
      mk_inst 23 ALLOCA [Lit 32w] ["%src"];
      mk_inst 24 ALLOCA [Lit 32w] ["%dst"];
      mk_inst 25 INVOKE [Label "callee"; Var "%src"] [];
      mk_inst 26 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [];
      mk_inst 27 REVERT [Lit 0w; Lit 0w] []] |>
End

Definition ircf_index_fn_def:
  ircf_index_fn = mk_raw_function "test"
    [ircf_index_entry; ircf_index_changed]
End

Definition ircf_index_callee_def:
  ircf_index_callee : ir_function =
    (mk_raw_function "callee" [
      <| bb_label := "callee"; bb_instructions := [
        mk_inst 30 PARAM [Lit 0w] ["%buf"];
        mk_inst 31 RETPC_PARAM [Lit 1w] ["%retpc"];
        mk_inst 32 MSTORE [Var "%buf"; Lit 42w] [];
        mk_inst 33 RET [Var "%retpc"] []] |>]) with fn_call_abi :=
      <| ica_has_memory_return_buffer := SOME T;
         ica_user_return_count := SOME 0 |>
End

Definition ircf_index_main_def:
  ircf_index_main = mk_raw_function "main" [
    <| bb_label := "main"; bb_instructions := [
      mk_inst 1 INVOKE [Label "test"] [];
      mk_inst 2 STOP [] []] |>]
End

Definition ircf_index_ctx_def:
  ircf_index_ctx : venom_context =
    <| ctx_functions := [ircf_index_main; ircf_index_fn; ircf_index_callee];
       ctx_entry := SOME "main"; ctx_global_reserved := [] |>
End

Definition ircf_index_meta_def:
  ircf_index_meta = FEMPTY |+ ("callee",
    <| ifm_invoke_param_count := 1; ifm_has_memory_return_buffer := T |>)
End

Definition ircf_index_analysis_def:
  ircf_index_analysis = icf_build_ctx ircf_index_meta
    ircf_index_ctx.ctx_functions FEMPTY ircf_index_fn
End

Definition ircf_index_target_entry_def:
  ircf_index_target_entry = ircf_index_entry with bb_instructions := [
    mk_inst 20 RETPC_PARAM [Lit 0w] ["%pc"];
    mk_inst 22 RET [Var "%pc"] []]
End

Definition ircf_index_raw_changed_def:
  ircf_index_raw_changed = ircf_index_changed with bb_instructions := [
    mk_inst 23 ALLOCA [Lit 32w] ["%src"];
    mk_inst 24 ALLOCA [Lit 32w] ["%dst"];
    mk_inst 25 INVOKE [Label "callee"; Var "%src"] [];
    mk_nop_inst (mk_inst 26 MCOPY [Var "%dst"; Var "%src"; Lit 32w] []);
    mk_inst 27 REVERT [Lit 0w; Lit 0w] []]
End

Definition ircf_index_target_changed_def:
  ircf_index_target_changed = ircf_index_changed with bb_instructions := [
    mk_inst 23 ALLOCA [Lit 32w] ["%src"];
    mk_inst 24 ALLOCA [Lit 32w] ["%dst"];
    mk_inst 25 INVOKE [Label "callee"; Var "%src"] [];
    mk_inst 27 REVERT [Lit 0w; Lit 0w] []]
End

Definition ircf_index_target_fn_def:
  ircf_index_target_fn = ircf_index_fn with fn_blocks :=
    [ircf_index_target_entry; ircf_index_target_changed]
End

Definition ircf_index_state_def:
  ircf_index_state s = s with
    <| vs_vars := FEMPTY; vs_allocas := FEMPTY; vs_params := [];
       vs_prev_bb := NONE; vs_current_bb := "test";
       vs_inst_idx := 0; vs_halted := F |>
End

Theorem ircf_index_source_run:
  run_block k C ircf_index_entry (ircf_index_state s) =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      ((ircf_index_state s) with
        <| vs_vars := FEMPTY |+ ("%pc",s.vs_return_pc_token); vs_inst_idx := 2 |> )
Proof
  EVAL_TAC
QED

Theorem ircf_index_target_run:
  run_block k C ircf_index_target_entry (ircf_index_state s) =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      ((ircf_index_state s) with
        <| vs_vars := FEMPTY |+ ("%pc",s.vs_return_pc_token); vs_inst_idx := 1 |> )
Proof
  EVAL_TAC
QED

Theorem ircf_index_dfg:
  icf_assign_root (dfg_build_function ircf_index_fn) {} "%dst" = "%dst" /\
  icf_assign_root (dfg_build_function ircf_index_fn) {} "%src" = "%src" /\
  dfg_get_def (dfg_build_function ircf_index_fn) "%dst" =
    SOME (mk_inst 24 ALLOCA [Lit 32w] ["%dst"]) /\
  dfg_get_def (dfg_build_function ircf_index_fn) "%src" =
    SOME (mk_inst 23 ALLOCA [Lit 32w] ["%src"]) /\
  icf_use_positions (dfg_build_function ircf_index_fn) "%src" =
    [(mk_inst 25 INVOKE [Label "callee"; Var "%src"] [],1);
     (mk_inst 26 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [],1)] /\
  icf_use_positions (dfg_build_function ircf_index_fn) "%dst" =
    [(mk_inst 26 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [],0)] /\
  icf_invoke_has_ret_buf ircf_index_meta ircf_index_ctx.ctx_functions
    (mk_inst 25 INVOKE [Label "callee"; Var "%src"] [])
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem ircf_index_alias_steps:
  icf_aliases_step (dfg_build_function ircf_index_fn) {"%src"} =
    (F,{"%src"}) /\
  icf_aliases_step (dfg_build_function ircf_index_fn) {"%dst"} =
    (F,{"%dst"})
Proof
  conj_tac >> simp[icf_aliases_step_def] >> EVAL_TAC >>
  pure_rewrite_tac[listTheory.LIST_TO_SET, pred_setTheory.IMAGE_INSERT,
                   pred_setTheory.IMAGE_EMPTY] >> simp[]
QED

Theorem ircf_index_aliases:
  icf_collect_aliases (dfg_build_function ircf_index_fn) "%src" = {"%src"} /\
  icf_collect_aliases (dfg_build_function ircf_index_fn) "%dst" = {"%dst"}
Proof
  conj_tac >> rewrite_tac[icf_collect_aliases_def] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >>
  simp[ircf_index_alias_steps] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >> simp[]
QED

Theorem ircf_index_ret_source:
  ircf_is_ret_buf_source ircf_index_analysis
    ircf_index_changed.bb_instructions "%src" 26 3
Proof
  simp[ircf_is_ret_buf_source_def, ircf_index_analysis_def,
       icf_build_ctx_def, ircf_index_aliases,
       icf_alias_use_positions_def, ircf_index_dfg] >>
  EVAL_TAC
QED

Theorem ircf_index_try_forward:
  ircf_try_forward ircf_index_analysis ircf_index_changed 3 =
    SOME ircf_index_raw_changed.bb_instructions
Proof
  mp_tac ircf_index_ret_source >>
  simp[ircf_index_changed_def, mk_inst_def, ircf_index_analysis_def,
       icf_build_ctx_def] >> strip_tac >>
  simp[ircf_try_forward_def, ircf_index_changed_def, mk_inst_def,
       ircf_index_analysis_def, icf_build_ctx_def,
       ircf_index_dfg, ircf_index_aliases,
       icf_is_alloca_def, icf_matches_alloca_size_def,
       icf_alias_use_positions_def, icf_is_assign_output_use_def,
       ircf_index_raw_changed_def, passSharedDefsTheory.mk_nop_inst_def] >>
  EVAL_TAC
QED

Theorem ircf_index_changed_transform:
  ircf_transform_block ircf_index_analysis ircf_index_changed =
    (T,ircf_index_raw_changed)
Proof
  mp_tac ircf_index_try_forward >>
  simp[ircf_index_changed_def, ircf_index_raw_changed_def, mk_inst_def,
       passSharedDefsTheory.mk_nop_inst_def] >> strip_tac >>
  simp[ircf_transform_block_def, ircf_index_changed_def,
       rich_listTheory.COUNT_LIST_GENLIST, listTheory.GENLIST,
       listTheory.FOLDL, mk_inst_def, ircf_index_raw_changed_def,
       passSharedDefsTheory.mk_nop_inst_def]
QED

Theorem ircf_index_entry_transform:
  ircf_transform_block a ircf_index_entry = (F,ircf_index_entry)
Proof
  simp[ircf_transform_block_def, ircf_index_entry_def,
       rich_listTheory.COUNT_LIST_GENLIST, listTheory.GENLIST,
       listTheory.FOLDL, mk_inst_def]
QED

Theorem ircf_index_fn_transform:
  ircf_transform_function ircf_index_meta ircf_index_ctx.ctx_functions
    FEMPTY ircf_index_fn = ircf_index_target_fn
Proof
  simp[ircf_transform_function_def, GSYM ircf_index_analysis_def] >>
  simp[ircf_index_fn_def, mk_raw_function_def, ircf_index_entry_transform,
       ircf_index_changed_transform] >>
  simp[passSharedDefsTheory.clear_nops_function_def,
       passSharedDefsTheory.clear_nops_block_def,
       ircf_index_raw_changed_def, ircf_index_target_changed_def,
       ircf_index_target_entry_def, ircf_index_target_fn_def,
       ircf_index_fn_def, mk_raw_function_def, ircf_index_changed_def,
       ircf_index_entry_def, passSharedDefsTheory.mk_nop_inst_def, mk_inst_def]
QED

Theorem ircf_index_main_transform:
  ircf_transform_function meta fns rma ircf_index_main = ircf_index_main
Proof
  simp[ircf_transform_function_def, ircf_index_main_def,
       mk_raw_function_def, ircf_transform_block_def,
       rich_listTheory.COUNT_LIST_GENLIST, listTheory.GENLIST,
       listTheory.FOLDL, mk_inst_def]
QED

Theorem ircf_index_callee_transform:
  ircf_transform_function meta fns rma ircf_index_callee = ircf_index_callee
Proof
  simp[ircf_transform_function_def, ircf_index_callee_def,
       mk_raw_function_def, ircf_transform_block_def,
       rich_listTheory.COUNT_LIST_GENLIST, listTheory.GENLIST,
       listTheory.FOLDL, mk_inst_def]
QED

Theorem ircf_index_ctx_transform:
  ircf_transform_ctx ircf_index_meta FEMPTY ircf_index_ctx =
    ircf_index_ctx with ctx_functions :=
      [ircf_index_main; ircf_index_target_fn; ircf_index_callee]
Proof
  mp_tac ircf_index_fn_transform >>
  simp[ircf_transform_ctx_def, ircf_index_ctx_def,
       ircf_index_main_transform, ircf_index_callee_transform]
QED

Theorem ircf_index_lookup_function:
  lookup_function "test"
    (ircf_transform_ctx ircf_index_meta FEMPTY ircf_index_ctx).ctx_functions =
    SOME ircf_index_target_fn
Proof
  simp[ircf_index_ctx_transform, lookup_function_def,
       ircf_index_main_def, ircf_index_target_fn_def,
       ircf_index_fn_def, mk_raw_function_def, listTheory.FIND_thm]
QED

Theorem ircf_index_lookup_blocks:
  lookup_block (ircf_index_state s).vs_current_bb ircf_index_fn.fn_blocks =
    SOME ircf_index_entry /\
  lookup_block (ircf_index_state s).vs_current_bb ircf_index_target_fn.fn_blocks =
    SOME ircf_index_target_entry
Proof
  simp[ircf_index_state_def, ircf_index_fn_def, ircf_index_target_fn_def,
       mk_raw_function_def, lookup_block_def, ircf_index_entry_def,
       ircf_index_target_entry_def, listTheory.FIND_thm]
QED

(* This is an execution obstruction only; the remaining frozen premises
   are certified separately before any task-level falsehood conclusion. *)
Theorem ircf_index_return_indices:
  !k m C C' s.
    ?r se te.
      run_block k C ircf_index_entry (ircf_index_state s) = IntRet r se /\
      run_block m C' ircf_index_target_entry (ircf_index_state s) = IntRet r te /\
      se.vs_inst_idx = 2 /\ te.vs_inst_idx = 1 /\
      se.vs_inst_idx <> te.vs_inst_idx
Proof
  rpt gen_tac >> simp[ircf_index_source_run, ircf_index_target_run] >>
  simp[ircf_index_state_def]
QED

Theorem ircf_index_return_no_taint_agree:
  run_block k C ircf_index_entry (ircf_index_state s) = IntRet r se /\
  run_block m C' ircf_index_target_entry (ircf_index_state s) = IntRet r' te ==>
  ~taint_agree D X tn se te
Proof
  simp[ircf_index_source_run, ircf_index_target_run] >>
  rpt strip_tac >> gvs[] >> drule taint_agree_frame >>
  simp[venom_state_component_equality]
QED
