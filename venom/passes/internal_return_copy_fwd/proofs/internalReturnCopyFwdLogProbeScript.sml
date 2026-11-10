Theory internalReturnCopyFwdLogProbe
Ancestors
  internalReturnCopyFwdPlan internalReturnCopyFwdDefs
  invokeCopyFwdCommonDefs venomInst callLayoutDefs basePtrDefs memLocDefs venomEffects
  ptrDiscipline

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

Theorem ircf_log_probe_block_transform:
  ircf_transform_block ircf_log_probe_analysis ircf_log_probe_bb =
    (T, ircf_log_probe_raw_bb)
Proof
  mp_tac ircf_log_probe_try_forward >>
  simp[ircf_log_probe_bb_def, ircf_log_probe_raw_bb_def, mk_inst_def,
       passSharedDefsTheory.mk_nop_inst_def] >> strip_tac >>
  simp[ircf_transform_block_def, ircf_log_probe_bb_def,
       rich_listTheory.COUNT_LIST_GENLIST, listTheory.GENLIST, listTheory.FOLDL, mk_inst_def,
       ircf_log_probe_raw_bb_def, passSharedDefsTheory.mk_nop_inst_def]
QED

Definition ircf_log_probe_target_bb_def:
  ircf_log_probe_target_bb = ircf_log_probe_bb with bb_instructions := [
    mk_inst 1 ALLOCA [Lit 32w] ["%src"];
    mk_inst 2 ALLOCA [Lit 32w] ["%dst"];
    mk_inst 3 INVOKE [Label "callee"; Var "%src"] [];
    mk_inst 5 LOG [Lit 1w; Var "%src"; Lit 0w; Lit 0w] [];
    mk_inst 6 STOP [] []]
End

Theorem ircf_log_probe_main_transform:
  ircf_transform_function ircf_log_probe_meta
    ircf_log_probe_ctx.ctx_functions FEMPTY ircf_log_probe_main =
    ircf_log_probe_main with fn_blocks := [ircf_log_probe_target_bb]
Proof
  simp[ircf_transform_function_def, GSYM ircf_log_probe_analysis_def] >>
  simp[ircf_log_probe_main_def, mk_raw_function_def,
       ircf_log_probe_block_transform] >>
  simp[passSharedDefsTheory.clear_nops_function_def,
       passSharedDefsTheory.clear_nops_block_def,
       ircf_log_probe_raw_bb_def, ircf_log_probe_target_bb_def,
       ircf_log_probe_bb_def, passSharedDefsTheory.mk_nop_inst_def,
       mk_inst_def]
QED

Theorem ircf_log_probe_callee_transform:
  !a. ircf_transform_block a (HD ircf_log_probe_callee.fn_blocks) =
    (F, HD ircf_log_probe_callee.fn_blocks)
Proof
  gen_tac >> simp[ircf_transform_block_def, ircf_log_probe_callee_def,
    mk_raw_function_def, rich_listTheory.COUNT_LIST_GENLIST,
    listTheory.GENLIST, listTheory.FOLDL, mk_inst_def]
QED

Theorem ircf_log_probe_callee_function_transform:
  !meta fns rma.
    ircf_transform_function meta fns rma ircf_log_probe_callee =
    ircf_log_probe_callee
Proof
  rpt gen_tac >>
  mp_tac (Q.SPEC `icf_build_ctx meta fns rma ircf_log_probe_callee`
    ircf_log_probe_callee_transform) >>
  simp[ircf_transform_function_def, ircf_log_probe_callee_def,
       mk_raw_function_def] >> strip_tac >> simp[]
QED

Theorem ircf_log_probe_context_transform:
  ircf_transform_ctx ircf_log_probe_meta FEMPTY ircf_log_probe_ctx =
    ircf_log_probe_ctx with ctx_functions := [ircf_log_probe_callee;
      ircf_log_probe_main with fn_blocks := [ircf_log_probe_target_bb]]
Proof
  mp_tac ircf_log_probe_main_transform >>
  simp[ircf_transform_ctx_def, ircf_log_probe_ctx_def,
       ircf_log_probe_callee_function_transform]
QED

Theorem ircf_log_probe_no_dst_write_alias:
  EVERY ircf_no_dst_write_alias ircf_log_probe_ctx.ctx_functions
Proof
  simp[ircf_log_probe_ctx_def] >> conj_tac
  >- (simp[ircf_no_dst_write_alias_def, ircf_log_probe_callee_def,
           mk_raw_function_def, mk_inst_def] >>
      rpt gen_tac >> strip_tac >> gvs[]) >>
  mp_tac ircf_log_probe_dfg >> mp_tac ircf_log_probe_aliases >>
  simp[ircf_log_probe_main_def, mk_raw_function_def, ircf_log_probe_bb_def] >>
  ntac 2 strip_tac >>
  simp[ircf_no_dst_write_alias_def, ircf_log_probe_main_def,
       mk_raw_function_def, ircf_log_probe_bb_def] >>
  rpt gen_tac >> strip_tac >> gvs[mk_inst_def] >>
  simp[ircf_log_probe_dfg, ircf_log_probe_aliases] >>
  rpt gen_tac >> strip_tac >> gvs[mk_inst_def, mem_write_ops_def]
QED

Theorem ircf_log_probe_ptr_roots:
  !P. ptr_roots P ircf_log_probe_main = {"%src"; "%dst"}
Proof
  gen_tac >> simp[ptr_roots_def, ircf_log_probe_main_def,
    ircf_log_probe_bb_def, mk_raw_function_def,
    pointerConfinedDefsTheory.alloca_roots_def, fn_insts_def, fn_insts_blocks_def,
    inst_output_def, mk_inst_def] >>
  simp[pred_setTheory.EXTENSION] >> dsimp[]
QED

Theorem ircf_log_probe_pointer_step:
  !vars. pointer_use_step_step ircf_log_probe_main vars = NONE
Proof
  gen_tac >> simp[pointerConfinedDefsTheory.pointer_use_step_step_def,
    pointerConfinedDefsTheory.pointer_use_step_def,
    ircf_log_probe_main_def, ircf_log_probe_bb_def,
    mk_raw_function_def, mk_inst_def,
    pointerConfinedDefsTheory.is_pointer_preserving_op_def]
QED

Theorem ircf_log_probe_pointer_vars:
  !P. fn_pv P ircf_log_probe_main = {"%src"; "%dst"}
Proof
  gen_tac >> rewrite_tac[fn_pv_def, ircf_log_probe_ptr_roots,
    pointerConfinedDefsTheory.pointer_derived_vars_def,
    pointerConfinedDefsTheory.pointer_use_vars_def] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >>
  simp[ircf_log_probe_pointer_step] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >> simp[listTheory.SET_TO_LIST_INV]
QED

Theorem ircf_log_probe_topic_not_ptr_use:
  !P. ~ptr_use_ok P {"%src"; "%dst"}
    (mk_inst 5 LOG [Lit 1w; Var "%dst"; Lit 0w; Lit 0w] [])
Proof
  gen_tac >> simp[ptr_use_ok_def, mk_inst_def,
    pointerConfinedDefsTheory.is_pointer_preserving_op_def,
    mem_read_ops_def, mem_write_ops_def] >> EVAL_TAC
QED

Theorem ircf_log_probe_not_fn_ptr_ok:
  !P. ~fn_ptr_ok P ircf_log_probe_main
Proof
  gen_tac >> strip_tac >>
  fs[fn_ptr_ok_def] >>
  qpat_x_assum `!inst. MEM inst (fn_insts _) ==> _` (qspec_then
    `mk_inst 5 LOG [Lit 1w; Var "%dst"; Lit 0w; Lit 0w] []` mp_tac) >>
  simp[ircf_log_probe_pointer_vars, ircf_log_probe_topic_not_ptr_use,
       ircf_log_probe_main_def, ircf_log_probe_bb_def,
       mk_raw_function_def, fn_insts_def, fn_insts_blocks_def]
QED

Theorem ircf_log_probe_not_ptr_discipline:
  !lo vs. ~ptr_discipline lo ircf_log_probe_ctx vs
Proof
  simp[ptr_discipline_def, ircf_log_probe_ctx_def,
       ircf_log_probe_not_fn_ptr_ok]
QED
