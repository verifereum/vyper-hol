Theory concretizePtrSingletonOriginProbe
Ancestors concretizeMemLocDefs frameOriginReachable venomWf cfgWf words
Libs wordsLib

Definition sop_callee_def:
  sop_callee = mk_raw_function "leaf"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 100 PARAM [Lit 0w] ["p"];
       mk_inst 101 ALLOCA [Lit 32w] ["b"];
       mk_inst 102 MSTORE [Var "p"; Lit 7w] [];
       mk_inst 103 MSTORE [Var "b"; Lit 9w] [];
       mk_inst 104 RET [Lit 0w] []] |>]
End

Definition sop_caller_def:
  sop_caller = mk_raw_function "main"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 1 ALLOCA [Lit 32w] ["a"];
       mk_inst 2 MSTORE [Var "a"; Lit 1w] [];
       mk_inst 3 INVOKE [Label "leaf"; Var "a"] [];
       mk_inst 4 INVOKE [Label "leaf"; Var "a"] [];
       mk_inst 5 MLOAD [Var "a"] ["r"];
       mk_inst 6 STOP [] []] |>]
End

Definition sop_ctx_def:
  sop_ctx = mk_venom_context [sop_callee; sop_caller] (SOME "main")
End

Definition sop_bp_def:
  sop_bp fn = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn
End

Theorem sop_production_bp:
  bp_get_ptrs (sop_bp sop_callee) "b" = [Ptr (Allocation 101) (SOME 0)] /\
  bp_get_ptrs (sop_bp sop_callee) "p" = [] /\
  SND (bp_one_pass sop_callee (cfg_analyze sop_callee).cfg_dfs_pre
    (sop_bp sop_callee)) = sop_bp sop_callee
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Definition sop_initial_def:
  sop_initial = (init_venom_state "entry") with vs_alloca_next := 256
End

Theorem sop_decode_call:
  decode_invoke (EL 2 (HD sop_caller.fn_blocks).bb_instructions) =
    SOME ("leaf", [Var "a"])
Proof
  EVAL_TAC
QED

Theorem sop_shape_checks:
  ssa_form sop_caller /\ ssa_form sop_callee /\
  all_reachable sop_caller /\ all_reachable sop_callee
Proof
  EVAL_TAC >> simp[relationTheory.RTC_REFL]
QED

Theorem sop_entry:
  origin_frame_reachable sop_initial sop_ctx [] [] FEMPTY entry_taint
    sop_caller (HD (HD sop_caller.fn_blocks).bb_instructions)
    sop_initial [] FEMPTY
Proof
  irule origin_frame_reachable_entry >>
  conj_tac >- (qexists `"main"` >> EVAL_TAC) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  qexists `"entry"` >> EVAL_TAC >>
  simp[venomExecSemanticsTheory.eval_phis_def,
       venomExecSemanticsTheory.phi_prefix_length_def]
QED

Definition sop_s1_def:
  sop_s1 = (update_var "a" 256w
    (sop_initial with <|vs_allocas := FEMPTY |+ (1,(256,32));
                         vs_alloca_next := 288|>)) with vs_inst_idx := 1
End

Definition sop_g1_def:
  sop_g1 = FEMPTY |+ ("a",(256:num,32:num))
End

Definition sop_o1_def:
  sop_o1 = FEMPTY |+ ("a",(OriginLocal 1,(256:num,32:num)))
End

Definition sop_t1_def:
  sop_t1 = step_taint (HD (HD sop_caller.fn_blocks).bb_instructions)
    sop_initial (sop_s1 with vs_inst_idx := 0) entry_taint
End

Theorem sop_after_alloca:
  origin_frame_reachable sop_initial sop_ctx [] [] sop_g1 sop_t1
    sop_caller (EL 1 (HD sop_caller.fn_blocks).bb_instructions)
    sop_s1 [] sop_o1
Proof
  assume_tac sop_entry >>
  drule origin_frame_reachable_next >>
  disch_then (qspecl_then
    [`EL 1 (HD sop_caller.fn_blocks).bb_instructions`,
     `sop_s1 with vs_inst_idx := 0`, `0`] mp_tac) >>
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Definition sop_s2_def:
  sop_s2 = (mstore 256 1w sop_s1) with vs_inst_idx := 2
End

Definition sop_t2_def:
  sop_t2 = step_taint (EL 1 (HD sop_caller.fn_blocks).bb_instructions)
    sop_s1 (sop_s2 with vs_inst_idx := 1) sop_t1
End

Theorem sop_at_call:
  origin_frame_reachable sop_initial sop_ctx [] [] sop_g1 sop_t2
    sop_caller (EL 2 (HD sop_caller.fn_blocks).bb_instructions)
    sop_s2 [] sop_o1
Proof
  assume_tac sop_after_alloca >>
  drule origin_frame_reachable_next >>
  disch_then (qspecl_then
    [`EL 2 (HD sop_caller.fn_blocks).bb_instructions`,
     `sop_s2 with vs_inst_idx := 1`, `0`] mp_tac) >>
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Definition sop_cs_def:
  sop_cs = THE (setup_callee sop_callee [256w] sop_s2)
End

Definition sop_frame_def:
  sop_frame = <| cf_fn := sop_caller;
    cf_inst := EL 2 (HD sop_caller.fn_blocks).bb_instructions;
    cf_state := sop_s2; cf_params := []; cf_prov := sop_g1;
    cf_tvar := sop_t2.t_var |>
End

Theorem sop_in_callee:
  origin_frame_reachable sop_initial sop_ctx [sop_frame] [SOME (256,32)]
    FEMPTY (sop_t2 with t_var := FEMPTY) sop_callee
    (HD (HD sop_callee.fn_blocks).bb_instructions) sop_cs [sop_o1] FEMPTY
Proof
  assume_tac sop_at_call >> drule origin_frame_reachable_call >>
  disch_then (qspec_then `"leaf"` mp_tac) >>
  simp[sop_decode_call] >>
  disch_then (qspecl_then [`sop_callee`, `[256w]`, `sop_cs`] mp_tac) >>
  disch_then (qspecl_then [`sop_cs`,
    `HD (HD sop_callee.fn_blocks).bb_instructions`] mp_tac) >>
  EVAL_TAC >> simp[venomExecSemanticsTheory.eval_phis_def,
    venomExecSemanticsTheory.phi_prefix_length_def]
QED

Definition sop_cp_def:
  sop_cp = (update_var "p" 256w sop_cs) with vs_inst_idx := 1
End
Definition sop_pg_def:
  sop_pg = [SOME (256:num,32:num)]
End
Definition sop_gp_def:
  sop_gp = FEMPTY |+ ("p",(256:num,32:num))
End
Definition sop_op_def:
  sop_op = FEMPTY |+ ("p",(OriginParameter 0,(256:num,32:num)))
End
Definition sop_tp_def:
  sop_tp = step_taint (HD (HD sop_callee.fn_blocks).bb_instructions)
    sop_cs (sop_cp with vs_inst_idx := 0) (sop_t2 with t_var := FEMPTY)
End

Theorem sop_after_param:
  origin_frame_reachable sop_initial sop_ctx [sop_frame] sop_pg sop_gp
    sop_tp sop_callee (EL 1 (HD sop_callee.fn_blocks).bb_instructions)
    sop_cp [sop_o1] sop_op
Proof
  assume_tac sop_in_callee >> drule origin_frame_reachable_next >>
  disch_then (qspecl_then
    [`EL 1 (HD sop_callee.fn_blocks).bb_instructions`,
     `sop_cp with vs_inst_idx := 0`, `0`] mp_tac) >>
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Definition sop_cb_def:
  sop_cb = (update_var "b" 288w
    (sop_cp with <|vs_allocas := FEMPTY |+ (101,(288,32));
                         vs_alloca_next := 320|>)) with vs_inst_idx := 2
End
Definition sop_gb_def:
  sop_gb = sop_gp |+ ("b",(288:num,32:num))
End
Definition sop_ob_def:
  sop_ob = sop_op |+ ("b",(OriginLocal 101,(288:num,32:num)))
End
Definition sop_tb_def:
  sop_tb = step_taint (EL 1 (HD sop_callee.fn_blocks).bb_instructions)
    sop_cp (sop_cb with vs_inst_idx := 1) sop_tp
End

Theorem sop_at_imported_write:
  origin_frame_reachable sop_initial sop_ctx [sop_frame] sop_pg sop_gb
    sop_tb sop_callee (EL 2 (HD sop_callee.fn_blocks).bb_instructions)
    sop_cb [sop_o1] sop_ob
Proof
  assume_tac sop_after_param >> drule origin_frame_reachable_next >>
  disch_then (qspecl_then
    [`EL 2 (HD sop_callee.fn_blocks).bb_instructions`,
     `sop_cb with vs_inst_idx := 1`, `0`] mp_tac) >>
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Definition sop_cw_def:
  sop_cw = (mstore 256 7w sop_cb) with vs_inst_idx := 3
End
Definition sop_tw_def:
  sop_tw = step_taint (EL 2 (HD sop_callee.fn_blocks).bb_instructions)
    sop_cb (sop_cw with vs_inst_idx := 2) sop_tb
End

Theorem sop_at_local_write:
  origin_frame_reachable sop_initial sop_ctx [sop_frame] sop_pg sop_gb
    sop_tw sop_callee (EL 3 (HD sop_callee.fn_blocks).bb_instructions)
    sop_cw [sop_o1] sop_ob
Proof
  assume_tac sop_at_imported_write >> drule origin_frame_reachable_next >>
  disch_then (qspecl_then
    [`EL 3 (HD sop_callee.fn_blocks).bb_instructions`,
     `sop_cw with vs_inst_idx := 2`, `0`] mp_tac) >>
  simp[sop_tw_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_tb``, ``sop_ctx``, ``sop_frame``]) >>
  simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem sop_first_origin_lookups:
  FLOOKUP sop_ob "b" = SOME (OriginLocal 101,(288,32)) /\
  FLOOKUP sop_ob "p" = SOME (OriginParameter 0,(256,32)) /\
  FLOOKUP sop_cw.vs_allocas 101 = SOME (288,32) /\
  FLOOKUP sop_o1 "a" = SOME (OriginLocal 1,(256,32)) /\
  FLOOKUP sop_frame.cf_state.vs_allocas 1 = SOME (256,32)
Proof
  EVAL_TAC
QED

Definition sop_cr_def:
  sop_cr = (mstore 288 9w sop_cw) with vs_inst_idx := 4
End
Definition sop_tr_def:
  sop_tr = step_taint (EL 3 (HD sop_callee.fn_blocks).bb_instructions)
    sop_cw (sop_cr with vs_inst_idx := 3) sop_tw
End

Theorem sop_at_return:
  origin_frame_reachable sop_initial sop_ctx [sop_frame] sop_pg sop_gb
    sop_tr sop_callee (EL 4 (HD sop_callee.fn_blocks).bb_instructions)
    sop_cr [sop_o1] sop_ob
Proof
  assume_tac sop_at_local_write >> drule origin_frame_reachable_next >>
  disch_then (qspecl_then
    [`EL 4 (HD sop_callee.fn_blocks).bb_instructions`,
     `sop_cr with vs_inst_idx := 3`, `0`] mp_tac) >>
  simp[sop_tr_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``sop_tw``, ``sop_ctx``, ``sop_frame``]) >>
  simp[finite_mapTheory.FUPDATE_EQ]
QED

Definition sop_s3_def:
  sop_s3 = (merge_callee_state sop_s2 sop_cr) with vs_inst_idx := 3
End
Definition sop_t3_def:
  sop_t3 = sop_tr with t_var := sop_t2.t_var
End

Theorem sop_second_call:
  origin_frame_reachable sop_initial sop_ctx [] [] sop_g1 sop_t3
    sop_caller (EL 3 (HD sop_caller.fn_blocks).bb_instructions)
    sop_s3 [] sop_o1
Proof
  assume_tac sop_at_return >> drule origin_frame_reachable_ret >>
  disch_then (qspecl_then
    [`<|iret_values := []; iret_adopt_fmp := NONE|>`, `sop_cr`,
     `sop_s3 with vs_inst_idx := 2`] mp_tac) >>
  disch_then (qspecl_then
    [`EL 3 (HD sop_caller.fn_blocks).bb_instructions`, `0`] mp_tac) >>
  simp[sop_frame_def, sop_t3_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_tr``, ``sop_ctx``]) >>
  simp[finite_mapTheory.FUPDATE_EQ]
QED

Definition sop_cs2_def:
  sop_cs2 = THE (setup_callee sop_callee [256w] sop_s3)
End
Definition sop_frame2_def:
  sop_frame2 = <|cf_fn := sop_caller;
    cf_inst := EL 3 (HD sop_caller.fn_blocks).bb_instructions;
    cf_state := sop_s3; cf_params := []; cf_prov := sop_g1;
    cf_tvar := sop_t3.t_var|>
End

Theorem sop_s3_control:
  sop_s3.vs_inst_idx = 3 /\ sop_s3.vs_current_bb = "entry" /\
  sop_s3.vs_vars = FEMPTY |+ ("a",256w)
Proof
  simp[sop_s3_def, venomExecSemanticsTheory.merge_callee_state_def,
    sop_s2_def, venomStateTheory.mstore_def, sop_s1_def,
    venomStateTheory.update_var_def, sop_initial_def,
    venomStateTheory.init_venom_state_def]
QED

Theorem sop_cs2_projections:
  sop_cs2.vs_inst_idx = 0 /\ sop_cs2.vs_current_bb = "entry" /\
  sop_cs2.vs_prev_bb = NONE /\ sop_cs2.vs_params = [256w] /\
  sop_cs2.vs_vars = FEMPTY /\ sop_cs2.vs_allocas = FEMPTY
Proof
  simp[sop_cs2_def, venomExecSemanticsTheory.setup_callee_def,
       sop_callee_def, venomInstTheory.mk_raw_function_def]
QED

Theorem sop_second_call_cert:
  active_inst sop_caller (EL 3 (HD sop_caller.fn_blocks).bb_instructions) sop_s3 /\
  setup_callee sop_callee [256w] sop_s3 = SOME sop_cs2 /\
  enters_block sop_callee sop_cs2 sop_cs2 /\
  active_inst sop_callee (HD (HD sop_callee.fn_blocks).bb_instructions) sop_cs2 /\
  eval_operands [Var "a"] sop_s3 = SOME [256w]
Proof
  conj_tac >- simp[contextCodegenRelTheory.active_inst_def, sop_s3_control,
    sop_caller_def, venomInstTheory.mk_raw_function_def] >>
  conj_tac >- simp[sop_cs2_def, venomExecSemanticsTheory.setup_callee_def,
    sop_callee_def, venomInstTheory.mk_raw_function_def] >>
  conj_tac >- (
    simp[contextCodegenRelTheory.enters_block_def, sop_cs2_projections,
      sop_callee_def, venomInstTheory.mk_raw_function_def,
      venomInstTheory.lookup_block_def, listTheory.FIND_def, listTheory.INDEX_FIND_def,
      venomExecSemanticsTheory.eval_phis_def, venomExecSemanticsTheory.phi_prefix_length_def,
      venomInstTheory.mk_inst_def] >>
    simp[sop_cs2_def, venomExecSemanticsTheory.setup_callee_def,
      sop_callee_def, venomInstTheory.mk_raw_function_def]) >>
  conj_tac >- simp[contextCodegenRelTheory.active_inst_def, sop_cs2_projections,
    sop_callee_def, venomInstTheory.mk_raw_function_def] >>
  simp[venomStateTheory.eval_operands_def, venomStateTheory.eval_operand_def,
    venomStateTheory.lookup_var_def, sop_s3_control, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem sop_in_second_callee:
  origin_frame_reachable sop_initial sop_ctx [sop_frame2] sop_pg
    FEMPTY (sop_t3 with t_var := FEMPTY) sop_callee
    (HD (HD sop_callee.fn_blocks).bb_instructions) sop_cs2 [sop_o1] FEMPTY
Proof
  assume_tac sop_second_call >> drule origin_frame_reachable_call >>
  disch_then (qspecl_then [`"leaf"`, `[Var "a"]`, `sop_callee`] mp_tac) >>
  disch_then (qspecl_then [`[256w]`, `sop_cs2`, `sop_cs2`,
    `HD (HD sop_callee.fn_blocks).bb_instructions`] mp_tac) >>
  `lookup_function "leaf" sop_ctx.ctx_functions = SOME sop_callee /\
    decode_invoke (EL 3 (HD sop_caller.fn_blocks).bb_instructions) =
      SOME ("leaf",[Var "a"]) /\
    (EL 3 (HD sop_caller.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
    op_prov sop_g1 (Var "a") = SOME (256,32)` by EVAL_TAC >>
  simp[sop_frame2_def, sop_second_call_cert, sop_pg_def]
QED



Definition sop_cp2_def:
  sop_cp2 = (update_var "p" 256w sop_cs2) with vs_inst_idx := 1
End
Definition sop_tp2_def:
  sop_tp2 = step_taint (HD (HD sop_callee.fn_blocks).bb_instructions)
    sop_cs2 (sop_cp2 with vs_inst_idx := 0) (sop_t3 with t_var := FEMPTY)
End

Theorem sop_second_param_step:
  step_inst 0 sop_ctx (HD (HD sop_callee.fn_blocks).bb_instructions) sop_cs2 =
    OK (sop_cp2 with vs_inst_idx := 0)
Proof
  simp[sop_callee_def, venomInstTheory.mk_raw_function_def,
    venomInstTheory.mk_inst_def, venomExecSemanticsTheory.step_inst_def,
    venomExecSemanticsTheory.step_inst_base_def, sop_cs2_projections,
    sop_cp2_def, venomStateTheory.update_var_def] >>
  metis_tac[venomStateTheory.venom_state_component_equality]
QED

Theorem sop_second_param_control:
  active_inst sop_callee (HD (HD sop_callee.fn_blocks).bb_instructions) sop_cs2 /\
  active_inst sop_callee (EL 1 (HD sop_callee.fn_blocks).bb_instructions)
    (sop_cp2 with vs_inst_idx := SUC sop_cs2.vs_inst_idx)
Proof
  simp[contextCodegenRelTheory.active_inst_def, sop_cs2_projections,
    sop_cp2_def, venomStateTheory.update_var_def, sop_callee_def,
    venomInstTheory.mk_raw_function_def]
QED

Theorem sop_second_param_origins:
  step_prov sop_pg FEMPTY (HD (HD sop_callee.fn_blocks).bb_instructions)
    (sop_cp2 with vs_inst_idx := 0) = sop_gp /\
  origin_step sop_pg FEMPTY (HD (HD sop_callee.fn_blocks).bb_instructions)
    (sop_cp2 with vs_inst_idx := 0) = sop_op
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_cp2``])
QED

Theorem sop_second_param:
  origin_frame_reachable sop_initial sop_ctx [sop_frame2] sop_pg sop_gp
    sop_tp2 sop_callee (EL 1 (HD sop_callee.fn_blocks).bb_instructions)
    sop_cp2 [sop_o1] sop_op
Proof
  assume_tac sop_in_second_callee >> drule origin_frame_reachable_next >>
  disch_then (qspecl_then
    [`EL 1 (HD sop_callee.fn_blocks).bb_instructions`,
     `sop_cp2 with vs_inst_idx := 0`, `0`] mp_tac) >>
  simp[sop_second_param_control, sop_second_param_step,
    sop_second_param_origins, sop_tp2_def] >>
  `sop_cp2 with vs_inst_idx := SUC sop_cs2.vs_inst_idx = sop_cp2` by
    simp[sop_cp2_def, sop_cs2_projections] >>
  `~is_terminator (HD (HD sop_callee.fn_blocks).bb_instructions).inst_opcode /\
    (HD (HD sop_callee.fn_blocks).bb_instructions).inst_opcode <> INVOKE`
    by EVAL_TAC >>
  gvs[sop_pg_def]
QED

Theorem sop_second_allocator:
  sop_cs2.vs_alloca_next = 288 /\ sop_cb.vs_alloca_next = 320
Proof
  `sop_s1.vs_alloca_next = 288` by
    simp[sop_s1_def, venomStateTheory.update_var_def] >>
  `sop_s2.vs_alloca_next = 288` by
    simp[sop_s2_def, venomStateTheory.mstore_def] >>
  `sop_s3.vs_alloca_next = 288` by
    simp[sop_s3_def, venomExecSemanticsTheory.merge_callee_state_def] >>
  simp[sop_cs2_def, venomExecSemanticsTheory.setup_callee_def,
    sop_callee_def, venomInstTheory.mk_raw_function_def,
    sop_cb_def, venomStateTheory.update_var_def]
QED

Definition sop_cb2_def:
  sop_cb2 = (update_var "b" 288w
    (sop_cp2 with <|vs_allocas := FEMPTY |+ (101,(288,32));
                         vs_alloca_next := 320|>)) with vs_inst_idx := 2
End
Definition sop_tb2_def:
  sop_tb2 = step_taint (EL 1 (HD sop_callee.fn_blocks).bb_instructions)
    sop_cp2 (sop_cb2 with vs_inst_idx := 1) sop_tp2
End

Theorem sop_cp2_projections:
  sop_cp2.vs_inst_idx = 1 /\ sop_cp2.vs_current_bb = "entry" /\
  sop_cp2.vs_alloca_next = 288 /\ sop_cp2.vs_allocas = FEMPTY /\
  sop_cp2.vs_vars = FEMPTY |+ ("p",256w)
Proof
  simp[sop_cp2_def, venomStateTheory.update_var_def,
    sop_cs2_projections, sop_second_allocator]
QED

Theorem sop_second_alloca_step:
  step_inst 0 sop_ctx (EL 1 (HD sop_callee.fn_blocks).bb_instructions) sop_cp2 =
    OK (sop_cb2 with vs_inst_idx := 1)
Proof
  simp[sop_callee_def, venomInstTheory.mk_raw_function_def,
    venomInstTheory.mk_inst_def, venomExecSemanticsTheory.step_inst_def,
    venomExecSemanticsTheory.step_inst_base_def,
    venomExecSemanticsTheory.exec_alloca_def, sop_cp2_projections,
    sop_cb2_def, venomStateTheory.update_var_def] >>
  simp[venomStateTheory.venom_state_component_equality, sop_cp2_projections]
QED

Theorem sop_second_alloca_control:
  active_inst sop_callee (EL 1 (HD sop_callee.fn_blocks).bb_instructions) sop_cp2 /\
  active_inst sop_callee (EL 2 (HD sop_callee.fn_blocks).bb_instructions)
    (sop_cb2 with vs_inst_idx := SUC sop_cp2.vs_inst_idx)
Proof
  simp[contextCodegenRelTheory.active_inst_def, sop_cp2_projections,
    sop_cb2_def, venomStateTheory.update_var_def, sop_callee_def,
    venomInstTheory.mk_raw_function_def]
QED

Theorem sop_cb2_projections:
  sop_cb2.vs_inst_idx = 2 /\ sop_cb2.vs_current_bb = "entry" /\
  sop_cb2.vs_allocas = FEMPTY |+ (101,(288,32)) /\
  sop_cb2.vs_vars = (FEMPTY |+ ("p",256w)) |+ ("b",288w)
Proof
  simp[sop_cb2_def, venomStateTheory.update_var_def, sop_cp2_projections]
QED

Theorem sop_second_alloca_origins:
  step_prov sop_pg sop_gp (EL 1 (HD sop_callee.fn_blocks).bb_instructions)
    (sop_cb2 with vs_inst_idx := 1) = sop_gb /\
  origin_step sop_pg sop_op (EL 1 (HD sop_callee.fn_blocks).bb_instructions)
    (sop_cb2 with vs_inst_idx := 1) = sop_ob
Proof
  simp[ptrDisciplineTheory.step_prov_def, frameOriginUpdatesTheory.origin_step_def,
    ptrDisciplineTheory.set_prov_def, ptrDisciplineTheory.out_prov_def,
    frameOriginUpdatesTheory.origin_set_def, frameOriginUpdatesTheory.origin_out_def,
    finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_EMPTY,
    sop_cb2_projections, sop_gb_def, sop_ob_def, sop_callee_def,
    venomInstTheory.mk_raw_function_def, venomInstTheory.mk_inst_def]
QED

Theorem sop_second_imported_write:
  origin_frame_reachable sop_initial sop_ctx [sop_frame2] sop_pg sop_gb
    sop_tb2 sop_callee (EL 2 (HD sop_callee.fn_blocks).bb_instructions)
    sop_cb2 [sop_o1] sop_ob
Proof
  assume_tac sop_second_param >> drule origin_frame_reachable_next >>
  disch_then (qspecl_then
    [`EL 2 (HD sop_callee.fn_blocks).bb_instructions`,
     `sop_cb2 with vs_inst_idx := 1`, `0`] mp_tac) >>
  simp[sop_second_alloca_control, sop_second_alloca_step,
    sop_second_alloca_origins, sop_tb2_def, sop_cp2_projections] >>
  `~is_terminator (EL 1 (HD sop_callee.fn_blocks).bb_instructions).inst_opcode /\
    (EL 1 (HD sop_callee.fn_blocks).bb_instructions).inst_opcode <> INVOKE`
    by EVAL_TAC >>
  `sop_cb2 with vs_inst_idx := 2 = sop_cb2` by simp[sop_cb2_def] >>
  simp[contextCodegenRelTheory.active_inst_def, sop_cb2_projections,
    sop_callee_def, venomInstTheory.mk_raw_function_def]
QED

Definition sop_cw2_def:
  sop_cw2 = (mstore 256 7w sop_cb2) with vs_inst_idx := 3
End
Definition sop_tw2_def:
  sop_tw2 = step_taint (EL 2 (HD sop_callee.fn_blocks).bb_instructions)
    sop_cb2 (sop_cw2 with vs_inst_idx := 2) sop_tb2
End

Theorem sop_second_imported_store_step:
  step_inst 0 sop_ctx (EL 2 (HD sop_callee.fn_blocks).bb_instructions) sop_cb2 =
    OK (sop_cw2 with vs_inst_idx := 2)
Proof
  simp[sop_callee_def, venomInstTheory.mk_raw_function_def,
    venomInstTheory.mk_inst_def, venomExecSemanticsTheory.step_inst_def,
    venomExecSemanticsTheory.step_inst_base_def,
    venomExecSemanticsTheory.exec_write2_def,
    venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
    sop_cb2_projections, finite_mapTheory.FLOOKUP_UPDATE,
    finite_mapTheory.FLOOKUP_EMPTY, sop_cw2_def] >>
  simp[venomStateTheory.mstore_def,
    venomStateTheory.venom_state_component_equality, sop_cb2_projections]
QED

Theorem sop_cw2_projections:
  sop_cw2.vs_inst_idx = 3 /\ sop_cw2.vs_current_bb = "entry" /\
  sop_cw2.vs_allocas = FEMPTY |+ (101,(288,32)) /\
  sop_cw2.vs_vars = (FEMPTY |+ ("p",256w)) |+ ("b",288w)
Proof
  simp[sop_cw2_def, venomStateTheory.mstore_def, sop_cb2_projections]
QED

Theorem sop_second_store_origins:
  step_prov sop_pg sop_gb (EL 2 (HD sop_callee.fn_blocks).bb_instructions)
    (sop_cw2 with vs_inst_idx := 2) = sop_gb /\
  origin_step sop_pg sop_ob (EL 2 (HD sop_callee.fn_blocks).bb_instructions)
    (sop_cw2 with vs_inst_idx := 2) = sop_ob
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_cw2``, ``sop_gb``, ``sop_ob``]) >>
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem sop_second_local_write:
  origin_frame_reachable sop_initial sop_ctx [sop_frame2] sop_pg sop_gb
    sop_tw2 sop_callee (EL 3 (HD sop_callee.fn_blocks).bb_instructions)
    sop_cw2 [sop_o1] sop_ob
Proof
  assume_tac sop_second_imported_write >> drule origin_frame_reachable_next >>
  disch_then (qspecl_then
    [`EL 3 (HD sop_callee.fn_blocks).bb_instructions`,
     `sop_cw2 with vs_inst_idx := 2`, `0`] mp_tac) >>
  simp[sop_second_imported_store_step, sop_second_store_origins,
    sop_tw2_def, sop_cb2_projections] >>
  `sop_cw2 with vs_inst_idx := 3 = sop_cw2` by simp[sop_cw2_def] >>
  simp[contextCodegenRelTheory.active_inst_def, sop_cb2_projections,
    sop_cw2_projections, sop_callee_def, venomInstTheory.mk_raw_function_def,
    venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Definition sop_cr2_def:
  sop_cr2 = (mstore 288 9w sop_cw2) with vs_inst_idx := 4
End
Definition sop_tr2_def:
  sop_tr2 = step_taint (EL 3 (HD sop_callee.fn_blocks).bb_instructions)
    sop_cw2 (sop_cr2 with vs_inst_idx := 3) sop_tw2
End

Theorem sop_second_local_store_step:
  step_inst 0 sop_ctx (EL 3 (HD sop_callee.fn_blocks).bb_instructions) sop_cw2 =
    OK (sop_cr2 with vs_inst_idx := 3)
Proof
  simp[sop_callee_def, venomInstTheory.mk_raw_function_def,
    venomInstTheory.mk_inst_def, venomExecSemanticsTheory.step_inst_def,
    venomExecSemanticsTheory.step_inst_base_def,
    venomExecSemanticsTheory.exec_write2_def,
    venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
    sop_cw2_projections, finite_mapTheory.FLOOKUP_UPDATE,
    finite_mapTheory.FLOOKUP_EMPTY, sop_cr2_def] >>
  simp[venomStateTheory.mstore_def,
    venomStateTheory.venom_state_component_equality, sop_cw2_projections]
QED

Theorem sop_cr2_projections:
  sop_cr2.vs_inst_idx = 4 /\ sop_cr2.vs_current_bb = "entry" /\
  sop_cr2.vs_allocas = FEMPTY |+ (101,(288,32)) /\
  sop_cr2.vs_vars = (FEMPTY |+ ("p",256w)) |+ ("b",288w)
Proof
  simp[sop_cr2_def, venomStateTheory.mstore_def, sop_cw2_projections]
QED

Theorem sop_second_local_store_origins:
  step_prov sop_pg sop_gb (EL 3 (HD sop_callee.fn_blocks).bb_instructions)
    (sop_cr2 with vs_inst_idx := 3) = sop_gb /\
  origin_step sop_pg sop_ob (EL 3 (HD sop_callee.fn_blocks).bb_instructions)
    (sop_cr2 with vs_inst_idx := 3) = sop_ob
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_cr2``, ``sop_gb``, ``sop_ob``]) >>
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem sop_second_return:
  origin_frame_reachable sop_initial sop_ctx [sop_frame2] sop_pg sop_gb
    sop_tr2 sop_callee (EL 4 (HD sop_callee.fn_blocks).bb_instructions)
    sop_cr2 [sop_o1] sop_ob
Proof
  assume_tac sop_second_local_write >> drule origin_frame_reachable_next >>
  disch_then (qspecl_then
    [`EL 4 (HD sop_callee.fn_blocks).bb_instructions`,
     `sop_cr2 with vs_inst_idx := 3`, `0`] mp_tac) >>
  simp[sop_second_local_store_step, sop_second_local_store_origins,
    sop_tr2_def, sop_cw2_projections] >>
  `sop_cr2 with vs_inst_idx := 4 = sop_cr2` by simp[sop_cr2_def] >>
  simp[contextCodegenRelTheory.active_inst_def, sop_cw2_projections,
    sop_cr2_projections, sop_callee_def, venomInstTheory.mk_raw_function_def,
    venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem sop_second_origin_lookups:
  FLOOKUP sop_ob "b" = SOME (OriginLocal 101,(288,32)) /\
  FLOOKUP sop_ob "p" = SOME (OriginParameter 0,(256,32)) /\
  FLOOKUP sop_cr2.vs_allocas 101 = SOME (288,32)
Proof
  simp[sop_cr2_projections] >> EVAL_TAC
QED

Definition sop_s4_def:
  sop_s4 = (merge_callee_state sop_s3 sop_cr2) with vs_inst_idx := 4
End
Definition sop_t4_def:
  sop_t4 = sop_tr2 with t_var := sop_t3.t_var
End

Theorem sop_second_ret_step:
  step_inst 0 sop_ctx (EL 4 (HD sop_callee.fn_blocks).bb_instructions) sop_cr2 =
    IntRet <|iret_values := []; iret_adopt_fmp := NONE|> sop_cr2
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_cr2``, ``sop_ctx``])
QED

Theorem sop_second_ret_control:
  active_inst sop_callee (EL 4 (HD sop_callee.fn_blocks).bb_instructions) sop_cr2 /\
  active_inst sop_caller (EL 4 (HD sop_caller.fn_blocks).bb_instructions)
    (sop_s4 with vs_inst_idx := SUC sop_s3.vs_inst_idx)
Proof
  simp[contextCodegenRelTheory.active_inst_def, sop_cr2_projections,
    sop_s4_def, venomExecSemanticsTheory.merge_callee_state_def,
    sop_s3_control, sop_caller_def, sop_callee_def,
    venomInstTheory.mk_raw_function_def]
QED

Theorem sop_after_second_return:
  origin_frame_reachable sop_initial sop_ctx [] [] sop_g1 sop_t4
    sop_caller (EL 4 (HD sop_caller.fn_blocks).bb_instructions)
    sop_s4 [] sop_o1
Proof
  assume_tac sop_second_return >> drule origin_frame_reachable_ret >>
  disch_then (qspecl_then
    [`<|iret_values := []; iret_adopt_fmp := NONE|>`, `sop_cr2`,
     `sop_s4 with vs_inst_idx := 3`] mp_tac) >>
  disch_then (qspecl_then
    [`EL 4 (HD sop_caller.fn_blocks).bb_instructions`, `0`] mp_tac) >>
  simp[sop_second_ret_step, sop_frame2_def, sop_t4_def,
    sop_second_ret_control, sop_s3_control] >>
  `!m:string |-> (num # num). DRESTRICT m UNIV = m` by
    simp[finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_DRESTRICT] >>
  `!m:string |-> (frame_origin # num # num). DRESTRICT m UNIV = m` by
    simp[finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_DRESTRICT] >>
  `!m:string |-> (num set). DRESTRICT m UNIV = m` by
    simp[finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_DRESTRICT] >>
  `sop_s4 with vs_inst_idx := 4 = sop_s4` by simp[sop_s4_def] >>
  `sop_s4 with vs_inst_idx := 3 = merge_callee_state sop_s3 sop_cr2` by
    simp[sop_s4_def, venomStateTheory.venom_state_component_equality,
      venomExecSemanticsTheory.merge_callee_state_def, sop_s3_control] >>
  simp[contextCodegenRelTheory.active_inst_def, sop_s4_def,
    venomExecSemanticsTheory.merge_callee_state_def, sop_s3_control,
    sop_caller_def, venomInstTheory.mk_raw_function_def, venomInstTheory.mk_inst_def,
    venomExecSemanticsTheory.bind_outputs_def]
QED

Theorem sop_defs_reach_checks:
  fn_defs_reach_uses sop_caller /\ fn_defs_reach_uses sop_callee /\
  ctx_inst_ids_distinct sop_ctx
Proof
  conj_tac >- (
    rw[venomWfTheory.fn_defs_reach_uses_def, sop_caller_def,
      venomInstTheory.mk_raw_function_def, venomInstTheory.mk_inst_def] >>
    simp[venomWfTheory.def_on_all_paths_def] >> rpt strip_tac >>
    disj2_tac >> qexists `0` >> simp[] >>
    FIRST_PROVE (map (fn n => qexists n >> simp[]) [`1`, `2`, `3`, `4`])) >>
  conj_tac >- (
    rw[venomWfTheory.fn_defs_reach_uses_def, sop_callee_def,
      venomInstTheory.mk_raw_function_def, venomInstTheory.mk_inst_def] >>
    simp[venomWfTheory.def_on_all_paths_def] >> rpt strip_tac >>
    disj2_tac >>
    FIRST_PROVE (map (fn n => qexists n >> simp[] >>
      FIRST_PROVE (map (fn j => qexists j >> simp[]) [`2`, `3`])) [`0`, `1`])) >>
  EVAL_TAC
QED

Theorem sop_no_derived:
  FINITE roots ==>
  pointer_derived_vars sop_callee roots = roots /\
  pointer_derived_vars sop_caller roots = roots
Proof
  strip_tac >>
  `!xs. pointer_use_step_step sop_callee xs = NONE /\
         pointer_use_step_step sop_caller xs = NONE` by
    simp[pointerConfinedDefsTheory.pointer_use_step_step_def,
      pointerConfinedDefsTheory.pointer_use_step_def,
      pointerConfinedDefsTheory.is_pointer_preserving_op_def,
      sop_caller_def, sop_callee_def, venomInstTheory.mk_raw_function_def,
      venomInstTheory.mk_inst_def] >>
  simp[pointerConfinedDefsTheory.pointer_derived_vars_def,
    pointerConfinedDefsTheory.pointer_use_vars_def] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >> simp[] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >> simp[listTheory.SET_TO_LIST_INV]
QED

Definition sop_P_def:
  sop_P nm = if nm = "leaf" then {0:num} else {}
End

Theorem sop_roots:
  ptr_roots sop_P sop_callee = {"p"; "b"} /\
  ptr_roots sop_P sop_caller = {"a"} /\
  alloca_roots sop_callee = {"b"} /\ alloca_roots sop_caller = {"a"}
Proof
  simp[ptrDisciplineTheory.ptr_roots_def, pointerConfinedDefsTheory.alloca_roots_def,
    sop_P_def, sop_callee_def, sop_caller_def, venomInstTheory.mk_raw_function_def,
    venomInstTheory.fn_insts_def, venomInstTheory.mk_inst_def,
    venomInstTheory.inst_output_def, pred_setTheory.EXTENSION,
    LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  EVAL_TAC >> simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  metis_tac[]
QED

Theorem sop_ptr_classification:
  fn_pv sop_P sop_callee = {"p"; "b"} /\
  fn_pv sop_P sop_caller = {"a"} /\
  pointer_derived_vars sop_callee (alloca_roots sop_callee) = {"b"} /\
  pointer_derived_vars sop_caller (alloca_roots sop_caller) = {"a"} /\
  pointer_derived_vars sop_callee
    (ptr_roots sop_P sop_callee DIFF alloca_roots sop_callee) = {"p"} /\
  pointer_derived_vars sop_caller
    (ptr_roots sop_P sop_caller DIFF alloca_roots sop_caller) = {}
Proof
  simp[ptrDisciplineTheory.fn_pv_def, sop_roots, sop_no_derived,
    pred_setTheory.INSERT_DIFF, pred_setTheory.EMPTY_DIFF]
QED

Theorem sop_ptr_checks:
  fn_ptr_ok sop_P sop_caller /\ fn_ptr_ok sop_P sop_callee
Proof
  simp[ptrDisciplineTheory.fn_ptr_ok_def, sop_ptr_classification,
    pointerConfinedDefsTheory.affine_pointer_ops_def,
    pointerConfinedDefsTheory.phi_pv_all_var_def, sop_roots, sop_no_derived] >>
  simp[sop_caller_def, sop_callee_def, venomInstTheory.mk_raw_function_def,
    venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def,
    venomInstTheory.mk_inst_def, DISJ_IMP_THM, FORALL_AND_THM,
    ptrDisciplineTheory.ptr_use_ok_def,
    pointerConfinedDefsTheory.is_pointer_preserving_op_def,
    memLocDefsTheory.mem_write_ops_def, memLocDefsTheory.mem_read_ops_def,
    venomExecSemanticsTheory.decode_invoke_def, sop_P_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> gvs[]
QED

Definition sop_leaf_out_def:
  sop_leaf_out = THE (concretize_function_fuel_in_context
    (concretize_memloc_fuel sop_callee) sop_ctx [] sop_callee)
End
Definition sop_ctx1_def:
  sop_ctx1 = mk_venom_context [sop_leaf_out; sop_caller] (SOME "main")
End

Theorem sop_leaf_metadata:
  sop_leaf_out.fn_mems_used = [(Allocation 101,0,32)] /\
  sop_leaf_out.fn_eom = SOME 32 /\
  imported_mems_used sop_ctx1 sop_caller = [(Allocation 101,0,32)]
Proof
  EVAL_TAC
QED

Definition sop_caller_lives_def:
  sop_caller_lives = context_mem_livesets (concretize_memloc_fuel sop_caller)
    sop_ctx1 sop_caller (sop_bp sop_caller) (cfg_analyze sop_caller)
End

Theorem sop_caller_lives_probe:
  IS_SOME (FLOOKUP sop_caller_lives (Allocation 1)) /\
  IS_SOME (FLOOKUP sop_caller_lives (Allocation 101))
Proof
  EVAL_TAC
QED

Theorem sop_lives_overlap:
  MEM ("entry",2) (THE (FLOOKUP sop_caller_lives (Allocation 1))) /\
  MEM ("entry",2) (THE (FLOOKUP sop_caller_lives (Allocation 101))) /\
  MEM ("entry",3) (THE (FLOOKUP sop_caller_lives (Allocation 1))) /\
  MEM ("entry",3) (THE (FLOOKUP sop_caller_lives (Allocation 101)))
Proof
  EVAL_TAC
QED

Definition sop_caller_layout_def:
  sop_caller_layout = THE (compute_function_layout_fuel_in_context
    (concretize_memloc_fuel sop_caller) sop_ctx1 [] sop_caller)
End

Theorem sop_caller_layout_probe:
  FLOOKUP sop_caller_layout.cl_positions (Allocation 1) = SOME 32 /\
  sop_caller_layout.cl_eom = 64
Proof
  EVAL_TAC
QED

