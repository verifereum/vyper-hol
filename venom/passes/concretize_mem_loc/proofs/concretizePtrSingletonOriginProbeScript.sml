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

Theorem sop_in_second_callee:
  origin_frame_reachable sop_initial sop_ctx [sop_frame2] sop_pg
    FEMPTY (sop_t3 with t_var := FEMPTY) sop_callee
    (HD (HD sop_callee.fn_blocks).bb_instructions) sop_cs2 [sop_o1] FEMPTY
Proof
  assume_tac sop_second_call >> drule origin_frame_reachable_call >>
  disch_then (qspecl_then [`"leaf"`, `[Var "a"]`, `sop_callee`] mp_tac) >>
  disch_then (qspecl_then [`[256w]`, `sop_cs2`, `sop_cs2`,
    `HD (HD sop_callee.fn_blocks).bb_instructions`] mp_tac) >>
  simp[sop_frame2_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``sop_t3``]) >>
  simp[venomExecSemanticsTheory.eval_phis_def,
    venomExecSemanticsTheory.phi_prefix_length_def]
QED


Theorem sop_cs2_projections:
  sop_cs2.vs_inst_idx = 0 /\ sop_cs2.vs_current_bb = "entry" /\
  sop_cs2.vs_prev_bb = NONE /\ sop_cs2.vs_params = [256w] /\
  sop_cs2.vs_vars = FEMPTY /\ sop_cs2.vs_allocas = FEMPTY
Proof
  simp[sop_cs2_def, venomExecSemanticsTheory.setup_callee_def,
       sop_callee_def, venomInstTheory.mk_raw_function_def]
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
