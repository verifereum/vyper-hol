(* Static-demand design probe. The bounded checks below are not closure. *)
Theory makeSsaCurrentStaticDemandProbe
Ancestors makeSsaCurrentHistoryProbe makeSsaCurrentSimDefs makeSsaCurrentDefs
  makeSsaCurrentCleanupRuntime venomExecSemantics venomState venomWf cfgWf
  unitShapeDefs o1PassContract list finite_map

Theorem current_static_probe_admissible:
  !fn. fn = current_probe_loop \/ fn = history_probe_backedges ==>
    fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
    fn_phis_cover_preds fn /\ fn_phi_outputs_single_def fn /\
    fn_phis_non_degenerate fn /\ all_reachable fn /\ fn_inst_wf fn /\
    wf_function fn /\ first_block_no_preds fn /\ first_block_no_phi fn /\
    ir_supply_covers_fn history_probe_supply fn /\ ir_supply_inst_ok history_probe_supply
Proof
  metis_tac[history_probe_admissible, MEM]
QED

(* This re-placed PHI selects its own output on first arrival. Cleanup
   replaces it by a read of the retained original PHI's renamed output.
   Thus backwards demand transport must pass through the retained batch,
   not require the selected pre-cleanup self-name on the first arrival. *)
Theorem current_static_probe_selected_self:
  resolve_phi "E" [Label "E";Var "v";Label "D";Var "formal_var_0"] = SOME (Var "v") /\
  simplify_current_phi_prefix
    [current_probe_inst 10 PHI
       [Label "E";Var "v";Label "D";Var "formal_var_0"] ["v"];
     current_probe_inst 2 PHI
       [Label "E";Var "a";Label "D";Var "b"] ["formal_var_0"]] =
    [current_probe_inst 10 PHI
       [Label "E";Var "a";Label "D";Var "b"] ["formal_var_0"];
     current_probe_inst 2 ASSIGN [Var "formal_var_0"] ["v"]] /\
  (EL 1 (FST (make_ssa_current_fn current_probe_supply current_probe_loop)).fn_blocks).bb_instructions =
    [current_probe_inst 10 PHI [Label "E";Var "a";Label "D";Var "b"] ["formal_var_0"];
     current_probe_inst 2 ASSIGN [Var "formal_var_0"] ["v"];
     current_probe_inst 3 ASSIGN [Lit 2w] ["b"];
     current_probe_inst 4 JNZ [Var "formal_var_0";Label "D";Label "X"] []]
Proof
  EVAL_TAC
QED

Theorem current_static_probe_first_and_return:
  !prev. prev = "E" \/ prev = "D" ==>
  ?post ready.
    eval_phis (history_probe_state [("a",1w);("b",2w)] prev "D")
      (EL 1 (FST (make_ssa_current_fn current_probe_supply current_probe_loop)).fn_blocks).bb_instructions = OK post /\
    current_copies_run
      [EL 1 (EL 1 (FST (make_ssa_current_fn current_probe_supply current_probe_loop)).fn_blocks).bb_instructions]
      post = OK ready /\ lookup_var "v" ready = SOME (if prev = "E" then 1w else 2w)
Proof
  rpt strip_tac >> gvs[] >> EVAL_TAC >> simp[FLOOKUP_UPDATE] >> EVAL_TAC >> simp[]
QED

Theorem current_static_probe_surviving_insertion:
  !prev. prev = "E" \/ prev = "D" \/ prev = "S" ==>
  ?post. eval_phis
    (history_probe_state [("a",1w);("b",2w);("x",3w);
       ("formal_var_0",5w);("formal_var_2",4w)] prev "H")
    (EL 1 (FST (make_ssa_current_fn history_probe_supply history_probe_backedges)).fn_blocks).bb_instructions = OK post /\
    lookup_var "formal_var_0" post = SOME
      (if prev = "E" then 3w else if prev = "D" then 4w else 5w)
Proof
  rpt strip_tac >> gvs[] >> EVAL_TAC >> simp[FLOOKUP_UPDATE] >> EVAL_TAC >> simp[]
QED
