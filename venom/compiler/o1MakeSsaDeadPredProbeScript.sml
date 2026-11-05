Theory o1MakeSsaDeadPredProbe
Ancestors o1MakeSsaPhiInputSearch o1MakeSsaFrontierAncestry
  o1MakeSsaCfg o1PassContract unitShapeDefs
  makeSsaCurrentDefs dominatorDefs cfgDefs venomInst list

Definition deadpred_fn_def:
  deadpred_fn = mk_raw_function "entry" [
    <|bb_label := "entry"; bb_instructions := [mk_inst 0 JMP [Label "a"] []]|>;
    <|bb_label := "a"; bb_instructions := [mk_inst 1 RETPC_PARAM [Lit 0w] ["r"];
      mk_inst 2 JMP [Label "join"] []]|>;
    <|bb_label := "join"; bb_instructions := [mk_inst 3 JMP [Label "exit"] []]|>;
    <|bb_label := "exit"; bb_instructions := [mk_inst 4 RET [Var "r"] []]|>;
    <|bb_label := "dead"; bb_instructions := [mk_inst 5 JMP [Label "join"] []]|>]
End

Theorem deadpred_walk_probe:
  ((cfg_analyze deadpred_fn).cfg_dfs_post,
    idom_of (dom_analyze (cfg_analyze deadpred_fn) deadpred_fn) "dead",
    current_frontier_map deadpred_fn) =
  (["exit";"join";"a";"entry"], SOME "exit",
   [("entry",[]);("a",[]);("join",["join"]);("exit",["join"]);("dead",["join"])])
Proof
  EVAL_TAC
QED

(* Place the seed at the spurious reachable frontier source, and add a
   return branch from the join before that seed. *)
Definition deadpred_branch_def:
  deadpred_branch = mk_raw_function "entry" [
    <|bb_label := "entry"; bb_instructions := [mk_inst 0 JMP [Label "a"] []]|>;
    <|bb_label := "a"; bb_instructions := [mk_inst 1 JMP [Label "join"] []]|>;
    <|bb_label := "join"; bb_instructions := [mk_inst 2 JNZ [Lit 1w;Label "exit";Label "ret"] []]|>;
    <|bb_label := "exit"; bb_instructions := [mk_inst 4 RET [Var "r"] []]|>;
    <|bb_label := "ret"; bb_instructions := [mk_inst 3 RETPC_PARAM [Lit 0w] ["r"];
      mk_inst 5 RET [Var "r"] []]|>;
    <|bb_label := "dead"; bb_instructions := [mk_inst 6 JMP [Label "join"] []]|>]
End

Definition deadpred_unit_def:
  deadpred_unit = <|cu_context := phi_search_context deadpred_branch;
                    cu_data_segment := []|>
End

Definition deadpred_supply_def:
  deadpred_supply = init_ir_supply deadpred_unit
End

Definition deadpred_out_def:
  deadpred_out = mk_raw_function "entry" [
    <|bb_label := "entry"; bb_instructions := [mk_inst 0 JMP [Label "a"] []]|>;
    <|bb_label := "a"; bb_instructions := [mk_inst 1 JMP [Label "join"] []]|>;
    <|bb_label := "join"; bb_instructions := [
      mk_inst 100 PHI [Label "a";Var "r";Label "dead";Var "formal_var_0"] ["r"];
      mk_inst 2 JNZ [Lit 1w;Label "exit";Label "ret"] []]|>;
    <|bb_label := "exit"; bb_instructions := [mk_inst 4 RET [Var "r"] []]|>;
    <|bb_label := "ret"; bb_instructions := [mk_inst 3 RETPC_PARAM [Lit 0w] ["formal_var_0"];
      mk_inst 5 RET [Var "formal_var_0"] []]|>;
    <|bb_label := "dead"; bb_instructions := [mk_inst 6 JMP [Label "join"] []]|>]
End

Theorem deadpred_branch_probe:
  current_frontier_map deadpred_branch =
    [("entry",[]);("a",[]);("join",["join"]);("exit",[]);("ret",["join"]);("dead",["join"])] /\
  FST (make_ssa_current_fn deadpred_supply deadpred_branch) = deadpred_out
Proof
  EVAL_TAC
QED

Theorem deadpred_input_check:
  phi_search_exec_check deadpred_branch /\ ir_supply_inst_ok deadpred_supply
Proof
  EVAL_TAC
QED

Theorem deadpred_branch_reach:
  fn_reachable deadpred_branch l <=> MEM l ["entry";"a";"join";"exit";"ret"]
Proof
  `fn_entry_label deadpred_branch = SOME "entry"` by EVAL_TAC >>
  simp[venomWfTheory.fn_reachable_def] >> eq_tac
  >- (strip_tac >>
      `!x y. RTC (fn_cfg_edge deadpred_branch) x y ==>
        MEM x ["entry";"a";"join";"exit";"ret"] ==>
        MEM y ["entry";"a";"join";"exit";"ret"]` suffices_by
        (disch_then (qspecl_then [`"entry"`,`l`] mp_tac) >> simp[]) >>
      ho_match_mp_tac relationTheory.RTC_INDUCT >> simp[] >> rpt strip_tac >>
      qpat_x_assum `fn_cfg_edge _ _ _` mp_tac >>
      simp[NoAsms, venomWfTheory.fn_cfg_edge_def, deadpred_branch_def,
        mk_raw_function_def, GSYM AND_IMP_INTRO, DISJ_IMP_THM,
        LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC >> metis_tac[]) >>
  `fn_cfg_edge deadpred_branch "entry" "a" /\
   fn_cfg_edge deadpred_branch "a" "join" /\
   fn_cfg_edge deadpred_branch "join" "exit" /\
   fn_cfg_edge deadpred_branch "join" "ret"` by
    (simp[venomWfTheory.fn_cfg_edge_def, deadpred_branch_def, mk_raw_function_def,
      GSYM AND_IMP_INTRO, DISJ_IMP_THM, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
      EXISTS_OR_THM] >> EVAL_TAC >> simp[]) >>
  `RTC (fn_cfg_edge deadpred_branch) "entry" "join"` by
    (irule relationTheory.RTC_TRANS >> qexists_tac `"a"` >>
     conj_tac >> irule relationTheory.RTC_SINGLE >> simp[]) >>
  `RTC (fn_cfg_edge deadpred_branch) "entry" "exit" /\
   RTC (fn_cfg_edge deadpred_branch) "entry" "ret"` by
    (conj_tac >>
     (irule relationTheory.RTC_TRANS >> qexists_tac `"join"` >>
      conj_tac >- simp[] >> irule relationTheory.RTC_SINGLE >> simp[])) >>
  simp[] >> metis_tac[relationTheory.RTC_REFL, relationTheory.RTC_SINGLE]
QED

Theorem deadpred_input_slice:
  reachable_fn deadpred_branch = phi_search_slice
    ["entry";"a";"join";"exit";"ret"] deadpred_branch
Proof
  irule phi_search_slice_sound >> simp[deadpred_branch_reach]
QED

Theorem deadpred_reachable_input_check:
  phi_search_exec_check (phi_search_slice
    ["entry";"a";"join";"exit";"ret"] deadpred_branch)
Proof
  EVAL_TAC
QED

Theorem deadpred_input_retpc:
  retpc_shape_ok deadpred_branch
Proof
  irule phi_search_full_reachable_check_sound >>
  simp[deadpred_input_slice, deadpred_input_check, deadpred_reachable_input_check]
QED

Theorem deadpred_input_shape:
  o1_fn_shape (mk_venom_context [deadpred_branch] NONE) deadpred_branch
Proof
  rewrite_tac[o1_fn_shape_def, fn_shape_ok_def] >>
  simp[deadpred_input_retpc] >> EVAL_TAC >>
  simp[GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS]
QED

Theorem deadpred_context_shape:
  o1_ctx_shape (phi_search_context deadpred_branch)
Proof
  irule phi_search_context_shape >> simp[deadpred_input_shape] >> EVAL_TAC
QED

Theorem deadpred_output_slice:
  reachable_fn (FST (make_ssa_current_fn deadpred_supply deadpred_branch)) =
  phi_search_slice ["entry";"a";"join";"exit";"ret"]
    (FST (make_ssa_current_fn deadpred_supply deadpred_branch))
Proof
  Cases_on `make_ssa_current_fn deadpred_supply deadpred_branch` >> simp[] >>
  `ALL_DISTINCT (MAP basic_block_bb_label deadpred_branch.fn_blocks)` by EVAL_TAC >>
  drule_all make_ssa_current_fn_reachable >> strip_tac >>
  irule phi_search_slice_sound >> simp[deadpred_branch_reach]
QED

Theorem deadpred_output_unseeded:
  ~retpc_var (phi_search_slice ["entry";"a";"join";"exit";"ret"] deadpred_out) "r"
Proof
  `copy_phi_closed RETPC_PARAM
    (phi_search_slice ["entry";"a";"join";"exit";"ret"] deadpred_out)
    (copy_phi_vars RETPC_PARAM
      (phi_search_slice ["entry";"a";"join";"exit";"ret"] deadpred_out))` by EVAL_TAC >>
  drule phi_search_vars_exact >> disch_then (qspec_then `"r"` assume_tac) >>
  gvs[retpc_var_def] >> EVAL_TAC
QED

Theorem deadpred_output_bad_retpc:
  ~retpc_shape_ok (FST (make_ssa_current_fn deadpred_supply deadpred_branch))
Proof
  rewrite_tac[retpc_shape_ok_def, deadpred_output_slice, CONJUNCT2 deadpred_branch_probe] >>
  strip_tac >>
  qpat_x_assum `!inst. _ /\ _ ==> ?front x. _` (qspec_then `mk_inst 4 RET [Var "r"] []` mp_tac) >>
  `MEM (mk_inst 4 RET [Var "r"] [])
    (fn_insts (phi_search_slice ["entry";"a";"join";"exit";"ret"] deadpred_out))` by EVAL_TAC >>
  simp[mk_inst_def] >> strip_tac >>
  gvs[deadpred_output_unseeded]
QED

Definition deadpred_pass_out_def:
  deadpred_pass_out = <|fpo_function := deadpred_out; fpo_label_map := [];
    fpo_supply := SND (make_ssa_current_fn deadpred_supply deadpred_branch)|>
End

Theorem deadpred_runner:
  fn_pass_step rpolicy (CFP_Simple VP_MakeSSA)
    deadpred_unit deadpred_supply deadpred_branch deadpred_pass_out
Proof
  rewrite_tac[fn_pass_step_def] >> EVAL_TAC >>
  simp[GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem deadpred_contract_premises:
  fn_pass_step rpolicy (CFP_Simple VP_MakeSSA)
    deadpred_unit deadpred_supply deadpred_branch deadpred_pass_out /\
  o1_ctx_shape deadpred_unit.cu_context /\ ir_supply_inst_ok deadpred_supply /\
  o1_fn_row 0 deadpred_branch
Proof
  simp[deadpred_runner, deadpred_unit_def, deadpred_context_shape,
       deadpred_input_check, o1_fn_row_def]
QED

Theorem deadpred_contract_output_failure:
  ~o1_fn_shape deadpred_unit.cu_context deadpred_pass_out.fpo_function
Proof
  mp_tac deadpred_output_bad_retpc >>
  simp[CONJUNCT2 deadpred_branch_probe, deadpred_pass_out_def,
       o1_fn_shape_def, fn_shape_ok_def] >> metis_tac[]
QED

Theorem deadpred_frozen_contract_false:
  ~o1_step_contract_at 0 rpolicy (CFP_Simple VP_MakeSSA)
Proof
  rewrite_tac[o1_step_contract_at_def] >> strip_tac >>
  first_x_assum (qspecl_then
    [`deadpred_unit`,`deadpred_supply`,`deadpred_branch`,`deadpred_pass_out`] mp_tac) >>
  simp[deadpred_contract_premises, deadpred_contract_output_failure]
QED
