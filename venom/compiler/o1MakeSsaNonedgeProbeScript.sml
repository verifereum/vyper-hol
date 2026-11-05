Theory o1MakeSsaNonedgeProbe
Ancestors
  o1MakeSsaPhiInputSearch o1MakeSsaConnectivityProbe o1MakeSsaCfg
  o1PassContract unitShapeDefs makeSsaCurrentDefs venomInst list

(* Both original PHIs have a nonpredecessor source label. The reachable
   consumer also has its real predecessor; the dead consumer has none. *)
Definition nonedge_fn_def:
  nonedge_fn = mk_raw_function "entry" [
    <|bb_label := "entry"; bb_instructions := [
      mk_inst 7 RETPC_PARAM [Lit 0w] ["s"]; mk_inst 0 JMP [Label "header"] []] |>;
    <|bb_label := "header"; bb_instructions := [
      mk_inst 1 JNZ [Lit 1w;Label "inner";Label "exit"] []] |>;
    <|bb_label := "inner"; bb_instructions := [
      mk_inst 2 JNZ [Lit 1w;Label "body";Label "merge"] []] |>;
    <|bb_label := "body"; bb_instructions := [
      mk_inst 3 RETPC_PARAM [Lit 0w] ["r"]; mk_inst 4 JMP [Label "merge"] []] |>;
    <|bb_label := "merge"; bb_instructions := [mk_inst 5 JMP [Label "header"] []] |>;
    <|bb_label := "exit"; bb_instructions := [
      mk_inst 8 PHI [Label "header";Var "s";Label "body";Var "r"] ["q"];
      mk_inst 6 RET [Var "q"] []] |>;
    <|bb_label := "dead"; bb_instructions := [
      mk_inst 9 PHI [Label "entry";Var "s";Label "body";Var "r"] ["d"];
      mk_inst 10 RET [Var "d"] []] |>]
End

Definition nonedge_supply_def:
  nonedge_supply = phi_search_supply with <| irs_next_inst := 11;
    irs_used_inst_ids := [0;1;2;3;4;5;6;7;8;9;10];
    irs_used_vars := ["r";"s";"q";"d"];
    irs_used_labels := ["entry";"header";"inner";"body";"merge";"exit";"dead"] |>
End

Theorem nonedge_admissible_formats:
  wf_function nonedge_fn /\ fn_inst_wf nonedge_fn /\ fn_label_refs_ok nonedge_fn /\
  ~fn_cfg_edge nonedge_fn "body" "exit" /\
  ~fn_cfg_edge nonedge_fn "body" "dead" /\ ir_supply_inst_ok nonedge_supply
Proof
  simp[venomWfTheory.fn_cfg_edge_def, nonedge_fn_def, mk_raw_function_def,
    GSYM AND_IMP_INTRO, DISJ_IMP_THM, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
    EXISTS_OR_THM, FORALL_AND_THM] >> EVAL_TAC >>
  simp[GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem nonedge_full_checks:
  phi_search_exec_check nonedge_fn /\
  phi_search_exec_check (FST (make_ssa_current_fn nonedge_supply nonedge_fn))
Proof
  EVAL_TAC
QED

Theorem nonedge_cfg:
  fn_cfg_edge nonedge_fn = fn_cfg_edge connectivity_nested
Proof
  simp[FUN_EQ_THM, venomWfTheory.fn_cfg_edge_def, nonedge_fn_def,
       connectivity_nested_def, mk_raw_function_def, GSYM AND_IMP_INTRO,
       DISJ_IMP_THM, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC >> simp[]
QED

Theorem nonedge_reach:
  fn_reachable nonedge_fn l <=>
  MEM l ["entry";"header";"inner";"body";"merge";"exit"]
Proof
  `fn_entry_label nonedge_fn = SOME "entry"` by EVAL_TAC >> eq_tac
  >- (simp[venomWfTheory.fn_reachable_def] >> strip_tac >>
      `!x y. RTC (fn_cfg_edge nonedge_fn) x y ==>
        MEM x ["entry";"header";"inner";"body";"merge";"exit"] ==>
        MEM y ["entry";"header";"inner";"body";"merge";"exit"]` suffices_by
        (disch_then (qspecl_then [`"entry"`,`l`] mp_tac) >> simp[]) >>
      ho_match_mp_tac relationTheory.RTC_INDUCT >> simp[] >> rpt strip_tac >>
      qpat_x_assum `fn_cfg_edge _ _ _` mp_tac >>
      pure_rewrite_tac[nonedge_cfg] >>
      simp[NoAsms, venomWfTheory.fn_cfg_edge_def, connectivity_nested_def,
           mk_raw_function_def, GSYM AND_IMP_INTRO, DISJ_IMP_THM,
           LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC >> metis_tac[]) >>
  strip_tac >>
  `fn_reachable connectivity_nested l` by
    metis_tac[connectivity_nested_reachability] >>
  `fn_entry_label connectivity_nested = SOME "entry"` by EVAL_TAC >>
  gvs[venomWfTheory.fn_reachable_def, nonedge_cfg]
QED

Theorem nonedge_slice:
  reachable_fn nonedge_fn = phi_search_slice
    ["entry";"header";"inner";"body";"merge";"exit"] nonedge_fn
Proof
  irule phi_search_slice_sound >> simp[nonedge_reach]
QED

Theorem nonedge_reachable_checks:
  phi_search_exec_check (phi_search_slice
    ["entry";"header";"inner";"body";"merge";"exit"] nonedge_fn) /\
  phi_search_exec_check (phi_search_slice
    ["entry";"header";"inner";"body";"merge";"exit"]
      (FST (make_ssa_current_fn nonedge_supply nonedge_fn)))
Proof
  EVAL_TAC
QED

Theorem nonedge_input_retpc:
  retpc_shape_ok nonedge_fn
Proof
  irule phi_search_full_reachable_check_sound >>
  simp[nonedge_slice, nonedge_full_checks, nonedge_reachable_checks]
QED

Theorem nonedge_input_shape:
  o1_fn_shape (mk_venom_context [nonedge_fn] NONE) nonedge_fn
Proof
  rewrite_tac[o1_fn_shape_def, fn_shape_ok_def] >>
  simp[nonedge_input_retpc] >> EVAL_TAC >>
  simp[GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS]
QED

Theorem nonedge_context_shape:
  o1_ctx_shape (phi_search_context nonedge_fn)
Proof
  irule phi_search_context_shape >> simp[nonedge_input_shape] >> EVAL_TAC
QED

Theorem nonedge_output_slice:
  reachable_fn (FST (make_ssa_current_fn nonedge_supply nonedge_fn)) =
  phi_search_slice ["entry";"header";"inner";"body";"merge";"exit"]
    (FST (make_ssa_current_fn nonedge_supply nonedge_fn))
Proof
  Cases_on `make_ssa_current_fn nonedge_supply nonedge_fn` >> simp[] >>
  `ALL_DISTINCT (MAP basic_block_bb_label nonedge_fn.fn_blocks)` by EVAL_TAC >>
  drule_all make_ssa_current_fn_reachable >> strip_tac >>
  irule phi_search_slice_sound >> simp[nonedge_reach]
QED

Theorem nonedge_output_retpc:
  retpc_shape_ok (FST (make_ssa_current_fn nonedge_supply nonedge_fn))
Proof
  irule phi_search_full_reachable_check_sound >>
  simp[nonedge_output_slice, nonedge_full_checks, nonedge_reachable_checks]
QED
