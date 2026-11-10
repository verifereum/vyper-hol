Theory internalReturnCopyFwdLogProbe
Ancestors
  internalReturnCopyFwdPlan internalReturnCopyFwdDefs
  invokeCopyFwdCommonDefs venomInst callLayoutDefs basePtrDefs memLocDefs venomEffects

Definition ircf_log_probe_callee_def:
  ircf_log_probe_callee : ir_function =
    (mk_raw_function "callee" [
      <| bb_label := "callee";
         bb_instructions := [
           mk_inst 10 PARAM [Lit 0w] ["%buf"];
           mk_inst 11 RETPC_PARAM [Lit 1w] ["%retpc"];
           mk_inst 12 MSTORE [Var "%buf"; Lit 42w] [];
           mk_inst 13 RET [Var "%retpc"] [] ] |> ]) with fn_call_abi :=
      <| ica_has_memory_return_buffer := SOME T;
         ica_user_return_count := SOME 0 |>
End

(* Actual-pass diagnostic: LOG's first topic is classified as an address. *)
Definition ircf_log_probe_bb_def:
  ircf_log_probe_bb : basic_block =
    <| bb_label := "main";
       bb_instructions := [
         mk_inst 1 ALLOCA [Lit 32w] ["%src"];
         mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
         mk_inst 3 INVOKE [Label "callee"; Var "%src"] [];
         mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [];
         mk_inst 5 LOG [Lit 1w; Var "%dst"; Lit 0w; Lit 0w] [];
         mk_inst 6 STOP [] []
       ] |>
End

Definition ircf_log_probe_main_def:
  ircf_log_probe_main = mk_raw_function "main" [ircf_log_probe_bb]
End

Definition ircf_log_probe_ctx_def:
  ircf_log_probe_ctx : venom_context =
    <| ctx_functions := [ircf_log_probe_callee; ircf_log_probe_main];
       ctx_entry := SOME "main"; ctx_global_reserved := [] |>
End

Theorem ircf_log_probe_dfg:
  icf_assign_root (dfg_build_function ircf_log_probe_main) {} "%dst" = "%dst" /\
  icf_assign_root (dfg_build_function ircf_log_probe_main) {} "%src" = "%src" /\
  dfg_get_def (dfg_build_function ircf_log_probe_main) "%dst" =
    SOME (mk_inst 2 ALLOCA [Lit 32w] ["%dst"]) /\
  dfg_get_def (dfg_build_function ircf_log_probe_main) "%src" =
    SOME (mk_inst 1 ALLOCA [Lit 32w] ["%src"]) /\
  icf_use_positions (dfg_build_function ircf_log_probe_main) "%src" =
    [(mk_inst 3 INVOKE [Label "callee"; Var "%src"] [], 1);
     (mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [], 1)] /\
  icf_use_positions (dfg_build_function ircf_log_probe_main) "%dst" =
    [(mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] [], 0);
     (mk_inst 5 LOG [Lit 1w; Var "%dst"; Lit 0w; Lit 0w] [], 1)] /\
  icf_invoke_has_ret_buf (FEMPTY |+ ("callee", <| ifm_invoke_param_count := 1;
       ifm_has_memory_return_buffer := T |>))
    ircf_log_probe_ctx.ctx_functions
    (mk_inst 3 INVOKE [Label "callee"; Var "%src"] [])
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem ircf_log_probe_alias_steps:
  icf_aliases_step (dfg_build_function ircf_log_probe_main) {"%src"} =
    (F, {"%src"}) /\
  icf_aliases_step (dfg_build_function ircf_log_probe_main) {"%dst"} =
    (F, {"%dst"})
Proof
  conj_tac >> simp[icf_aliases_step_def] >> EVAL_TAC >>
  pure_rewrite_tac[listTheory.LIST_TO_SET, pred_setTheory.IMAGE_INSERT,
                   pred_setTheory.IMAGE_EMPTY] >> simp[]
QED

Theorem ircf_log_probe_aliases:
  icf_collect_aliases (dfg_build_function ircf_log_probe_main) "%src" = {"%src"} /\
  icf_collect_aliases (dfg_build_function ircf_log_probe_main) "%dst" = {"%dst"}
Proof
  conj_tac >> rewrite_tac[icf_collect_aliases_def] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >>
  simp[ircf_log_probe_alias_steps] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >> simp[]
QED

Definition ircf_log_probe_meta_def:
  ircf_log_probe_meta = FEMPTY |+ ("callee",
    <| ifm_invoke_param_count := 1; ifm_has_memory_return_buffer := T |>)
End

Definition ircf_log_probe_analysis_def:
  ircf_log_probe_analysis = icf_build_ctx ircf_log_probe_meta
    ircf_log_probe_ctx.ctx_functions FEMPTY ircf_log_probe_main
End

Theorem ircf_log_probe_ret_source:
  ircf_is_ret_buf_source ircf_log_probe_analysis
    ircf_log_probe_bb.bb_instructions "%src" 4 3
Proof
  simp[ircf_is_ret_buf_source_def, ircf_log_probe_analysis_def,
       icf_build_ctx_def, ircf_log_probe_aliases,
       icf_alias_use_positions_def, ircf_log_probe_dfg,
       ircf_log_probe_meta_def] >>
  EVAL_TAC
QED

Definition ircf_log_probe_raw_bb_def:
  ircf_log_probe_raw_bb = ircf_log_probe_bb with bb_instructions := [
    mk_inst 1 ALLOCA [Lit 32w] ["%src"];
    mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
    mk_inst 3 INVOKE [Label "callee"; Var "%src"] [];
    mk_nop_inst (mk_inst 4 MCOPY [Var "%dst"; Var "%src"; Lit 32w] []);
    mk_inst 5 LOG [Lit 1w; Var "%src"; Lit 0w; Lit 0w] [];
    mk_inst 6 STOP [] []]
End

Theorem ircf_log_probe_try_forward:
  ircf_try_forward ircf_log_probe_analysis ircf_log_probe_bb 3 =
    SOME ircf_log_probe_raw_bb.bb_instructions
Proof
  mp_tac ircf_log_probe_ret_source >>
  simp[ircf_log_probe_bb_def, mk_inst_def, ircf_log_probe_analysis_def,
       icf_build_ctx_def] >> strip_tac >>
  simp[ircf_try_forward_def, ircf_log_probe_bb_def, mk_inst_def,
       ircf_log_probe_analysis_def, icf_build_ctx_def,
       ircf_log_probe_dfg, ircf_log_probe_aliases,
       icf_is_alloca_def, icf_matches_alloca_size_def,
       icf_alias_use_positions_def, icf_is_assign_output_use_def] >>
  simp[is_mem_addr_position_def, findi_def, listTheory.INDEX_FIND_def,
       ircf_log_probe_raw_bb_def, ircf_log_probe_bb_def, mk_inst_def] >>
  simp[rich_listTheory.COUNT_LIST_def, bp_get_read_location_def,
       is_raw_fmp_opcode_def, read_effects_def, mem_read_ops_def,
       bp_segment_from_ops_def] >>
  Cases_on `bp_ptr_from_op
    (bp_analyze (cfg_analyze ircf_log_probe_main) ircf_log_probe_main)
    (Var "%src")`
  >- (simp[wordsTheory.dimword_def] >>
      CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC) >>
  rename1 `SOME p` >> Cases_on `p` >> simp[wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC
QED
