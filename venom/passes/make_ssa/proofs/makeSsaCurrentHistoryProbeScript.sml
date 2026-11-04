(* Bounded real-pass probes; these are not universal exclusion lemmas. *)
Theory makeSsaCurrentHistoryProbe
Ancestors
  makeSsaCurrentDefs makeSsaCurrentSimDefs makeSsaCurrentReinsertionSlots venomWf cfgWf
  unitShapeDefs o1PassContract venomExecSemantics

Definition history_probe_bb_def:
  history_probe_bb l xs = <|bb_label := l; bb_instructions := xs|>
End

(* E branches through two ordinary definitions; H has a real original PHI
   and a loop-carried ordinary owner x. *)
Definition history_probe_diamond_def:
  history_probe_diamond = mk_raw_function "diamond"
  [history_probe_bb "E"
    [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
     current_probe_inst 1 ASSIGN [Lit 2w] ["b"];
     current_probe_inst 2 JNZ [Var "a"; Label "L"; Label "R"] []];
   history_probe_bb "L"
    [current_probe_inst 3 ASSIGN [Lit 3w] ["x"];
     current_probe_inst 4 JMP [Label "H"] []];
   history_probe_bb "R"
    [current_probe_inst 5 ASSIGN [Lit 4w] ["x"];
     current_probe_inst 6 JMP [Label "H"] []];
   history_probe_bb "H"
    [current_probe_inst 7 PHI
       [Label "L"; Var "a"; Label "R"; Var "b"; Label "H"; Var "a"] ["v"];
     current_probe_inst 8 ADD [Var "x"; Var "v"] ["z"];
     current_probe_inst 9 JNZ [Var "z"; Label "H"; Label "X"] []];
   history_probe_bb "X" [current_probe_inst 10 STOP [] []]]
End

Definition history_probe_backedges_def:
  history_probe_backedges = mk_raw_function "backedges"
  [history_probe_bb "E"
    [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
     current_probe_inst 1 ASSIGN [Lit 2w] ["b"];
     current_probe_inst 2 ASSIGN [Lit 3w] ["x"];
     current_probe_inst 3 JMP [Label "H"] []];
   history_probe_bb "H"
    [current_probe_inst 4 PHI
       [Label "E"; Var "a"; Label "D"; Var "b"; Label "S"; Var "a"] ["v"];
     current_probe_inst 5 ADD [Var "x"; Var "v"] ["z"];
     current_probe_inst 6 JNZ [Var "z"; Label "D"; Label "S"] []];
   history_probe_bb "D"
    [current_probe_inst 7 ASSIGN [Lit 4w] ["x"];
     current_probe_inst 8 JMP [Label "H"] []];
   history_probe_bb "S" [current_probe_inst 9 JMP [Label "H"] []]]
End

Definition history_probe_nested_def:
  history_probe_nested = mk_raw_function "nested"
  [history_probe_bb "E"
    [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
     current_probe_inst 1 ASSIGN [Lit 2w] ["b"];
     current_probe_inst 2 ASSIGN [Lit 3w] ["x"];
     current_probe_inst 3 JMP [Label "H"] []];
   history_probe_bb "H"
    [current_probe_inst 4 PHI [Label "E"; Var "a"; Label "J"; Var "b"] ["v"];
     current_probe_inst 5 ADD [Var "x"; Var "v"] ["z"];
     current_probe_inst 6 JMP [Label "I"] []];
   history_probe_bb "I"
    [current_probe_inst 7 ADD [Var "x"; Var "a"] ["w"];
     current_probe_inst 8 JNZ [Var "w"; Label "D"; Label "J"] []];
   history_probe_bb "D"
    [current_probe_inst 9 ASSIGN [Lit 4w] ["x"];
     current_probe_inst 10 JMP [Label "I"] []];
   history_probe_bb "J" [current_probe_inst 11 JMP [Label "H"] []]]
End

Definition history_probe_irreducible_def:
  history_probe_irreducible = mk_raw_function "irreducible"
  [history_probe_bb "E"
    [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
     current_probe_inst 1 ASSIGN [Lit 2w] ["b"];
     current_probe_inst 2 ASSIGN [Lit 3w] ["x"];
     current_probe_inst 3 JNZ [Var "a"; Label "H"; Label "I"] []];
   history_probe_bb "H"
    [current_probe_inst 4 PHI [Label "E"; Var "a"; Label "I"; Var "b"] ["v"];
     current_probe_inst 5 ADD [Var "x"; Var "v"] ["z"];
     current_probe_inst 6 ASSIGN [Lit 4w] ["x"];
     current_probe_inst 7 JMP [Label "I"] []];
   history_probe_bb "I"
    [current_probe_inst 8 ADD [Var "x"; Var "a"] ["w"];
     current_probe_inst 9 JMP [Label "H"] []]]
End

Definition history_probe_supply_def:
  history_probe_supply =
    <|irs_next_inst := 100; irs_next_var := 0; irs_next_label := 0;
      irs_used_inst_ids := GENLIST I 20;
      irs_used_vars := ["a";"b";"x";"v";"z";"w"];
      irs_used_labels := ["E";"L";"R";"H";"X";"D";"S";"I";"J";
        "diamond";"backedges";"nested";"irreducible";"probe"]|>
End

Definition history_probe_shape_def:
  history_probe_shape fn = MAP (\bb. (bb.bb_label,
    MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs)) bb.bb_instructions))
    (FST (make_ssa_current_fn history_probe_supply fn)).fn_blocks
End

Definition history_probe_insert_def:
  history_probe_insert fn = add_phi_nodes_supply history_probe_supply
    (current_frontier_map fn) (current_pred_map fn)
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) fn.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))))
End

Definition history_probe_rename_def:
  history_probe_rename fn = SND (SND (rename_current_blocks
    (SND (history_probe_insert fn))
    (init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn))))))
    (FST (history_probe_insert fn)) (current_succ_map fn) (current_dom_tree fn)))
End

(* Positions are BEFORE cleanup reordering/id reassignment. Every insertion
   is inspected with its actual owner and replayed operands. *)
Definition history_probe_inserted_def:
  history_probe_inserted fn =
    let ins = FST (history_probe_insert fn) in
    let renamed = history_probe_rename fn in
    FLAT (GENLIST (\j.
      MAP (\k. ((EL j fn.fn_blocks).bb_label,
        (EL k (EL j ins).bb_instructions).inst_outputs,
        EL k (EL j renamed).bb_instructions))
      (GENLIST I (LENGTH (EL j ins).bb_instructions -
                  LENGTH (EL j fn.fn_blocks).bb_instructions))) (LENGTH fn.fn_blocks))
End

Theorem history_probe_actual_rename:
  fn_entry_label fn = SOME entry ==>
    (FST (make_ssa_current_fn history_probe_supply fn)).fn_blocks =
      simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks)
        (history_probe_rename fn)
Proof
  strip_tac >>
  simp[history_probe_rename_def, history_probe_insert_def,
    make_ssa_current_fn_def, current_frontier_map_def, current_pred_map_def,
    current_succ_map_def, current_dom_postorder_def, current_dom_tree_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem history_probe_diamond_insert:
  MAP (\(l,owner,i). (l,owner,i.inst_operands,i.inst_outputs,
      (simplify_current_phi i).inst_opcode))
    (history_probe_inserted history_probe_diamond) =
  [("H",["x"],[Label "L"; Var "formal_var_2"; Label "R"; Var "formal_var_1";
      Label "H"; Var "x"],["x"],PHI);
   ("H",["v"],[Label "L"; Var "v"; Label "R"; Var "v";
      Label "H"; Var "formal_var_0"],["v"],ASSIGN)]
Proof
  EVAL_TAC
QED

Theorem history_probe_backedges_insert:
  MAP (\(l,owner,i). (l,owner,i.inst_operands,i.inst_outputs,
      (simplify_current_phi i).inst_opcode))
    (history_probe_inserted history_probe_backedges) =
  [("H",["v"],[Label "E"; Var "v"; Label "D"; Var "formal_var_1";
      Label "S"; Var "formal_var_1"],["v"],ASSIGN);
   ("H",["x"],[Label "E"; Var "x"; Label "D"; Var "formal_var_2";
      Label "S"; Var "formal_var_0"],["formal_var_0"],PHI)]
Proof
  EVAL_TAC
QED

Theorem history_probe_nested_insert:
  MAP (\(l,owner,i). (l,owner,i.inst_operands,i.inst_outputs,
      (simplify_current_phi i).inst_opcode))
    (history_probe_inserted history_probe_nested) =
  [("H",["v"],[Label "E"; Var "v"; Label "J"; Var "formal_var_1"],["v"],ASSIGN);
   ("H",["x"],[Label "E"; Var "x"; Label "J"; Var "formal_var_2"],["formal_var_0"],PHI);
   ("I",["x"],[Label "H"; Var "formal_var_0"; Label "D"; Var "formal_var_3"],
      ["formal_var_2"],PHI)]
Proof
  EVAL_TAC
QED

Theorem history_probe_irreducible_insert:
  MAP (\(l,owner,i). (l,owner,i.inst_operands,i.inst_outputs,
      (simplify_current_phi i).inst_opcode))
    (history_probe_inserted history_probe_irreducible) =
  [("H",["x"],[Label "E"; Var "x"; Label "I"; Var "formal_var_0"],["formal_var_1"],PHI);
   ("I",["x"],[Label "E"; Var "x"; Label "H"; Var "formal_var_2"],["formal_var_0"],PHI)]
Proof
  EVAL_TAC
QED

Theorem history_probe_control_insert:
  MAP (\(l,owner,i). (l,owner,i.inst_operands,i.inst_outputs,
      (simplify_current_phi i).inst_opcode))
    (history_probe_inserted current_probe_loop) =
  [("D",["v"],[Label "E"; Var "v"; Label "D"; Var "formal_var_0"],["v"],ASSIGN)]
Proof
  EVAL_TAC
QED

Theorem history_probe_static_premises:
  !fn. MEM fn [history_probe_diamond; history_probe_backedges;
      history_probe_nested; history_probe_irreducible; current_probe_loop] ==>
    fn_phi_operands_single_def fn /\ fn_phi_outputs_single_def fn /\
    fn_phis_non_degenerate fn /\ fn_phis_cover_preds fn /\
    fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
    first_block_no_phi fn /\ ir_supply_covers_fn history_probe_supply fn /\
    ir_supply_inst_ok history_probe_supply
Proof
  gen_tac >> pure_rewrite_tac[listTheory.MEM] >> strip_tac >> gvs[]
  >- suspend "diamond"
  >- suspend "backedges"
  >- suspend "nested"
  >- suspend "irreducible"
  >> suspend "control"
QED

Resume history_probe_static_premises[diamond]:
  rw[fn_phi_operands_single_def_def, fn_phi_outputs_single_def_def,
    fn_phis_non_degenerate_def, fn_phis_cover_preds_def, fn_inst_wf_def,
    history_probe_diamond_def, history_probe_bb_def, current_probe_inst_def,
    venomInstTheory.mk_raw_function_def, venomInstTheory.phi_pairs_def,
    venomInstTheory.fn_insts_def] >>
  gvs[venomInstTheory.phi_pairs_def] >> EVAL_TAC >>
  gvs[venomInstTheory.fn_insts_blocks_def, venomInstTheory.phi_pairs_def,
    fn_cfg_edge_def, venomInstTheory.bb_succs_def] >> EVAL_TAC >>
  gvs[venomInstTheory.get_successors_def, venomInstTheory.is_terminator_def,
    venomStateTheory.get_label_def] >> dsimp[]
QED

Resume history_probe_static_premises[backedges]:
  rw[fn_phi_operands_single_def_def, fn_phi_outputs_single_def_def,
    fn_phis_non_degenerate_def, fn_phis_cover_preds_def, fn_inst_wf_def,
    history_probe_backedges_def, history_probe_bb_def, current_probe_inst_def,
    venomInstTheory.mk_raw_function_def, venomInstTheory.phi_pairs_def,
    venomInstTheory.fn_insts_def] >>
  gvs[venomInstTheory.phi_pairs_def] >> EVAL_TAC >>
  gvs[venomInstTheory.fn_insts_blocks_def, venomInstTheory.phi_pairs_def,
    fn_cfg_edge_def, venomInstTheory.bb_succs_def] >> EVAL_TAC >>
  gvs[venomInstTheory.get_successors_def, venomInstTheory.is_terminator_def,
    venomStateTheory.get_label_def] >> dsimp[]
QED

Resume history_probe_static_premises[nested]:
  rw[fn_phi_operands_single_def_def, fn_phi_outputs_single_def_def,
    fn_phis_non_degenerate_def, fn_phis_cover_preds_def, fn_inst_wf_def,
    history_probe_nested_def, history_probe_bb_def, current_probe_inst_def,
    venomInstTheory.mk_raw_function_def, venomInstTheory.phi_pairs_def,
    venomInstTheory.fn_insts_def] >>
  gvs[venomInstTheory.phi_pairs_def] >> EVAL_TAC >>
  gvs[venomInstTheory.fn_insts_blocks_def, venomInstTheory.phi_pairs_def,
    fn_cfg_edge_def, venomInstTheory.bb_succs_def] >> EVAL_TAC >>
  gvs[venomInstTheory.get_successors_def, venomInstTheory.is_terminator_def,
    venomStateTheory.get_label_def] >> dsimp[]
QED

Resume history_probe_static_premises[irreducible]:
  rw[fn_phi_operands_single_def_def, fn_phi_outputs_single_def_def,
    fn_phis_non_degenerate_def, fn_phis_cover_preds_def, fn_inst_wf_def,
    history_probe_irreducible_def, history_probe_bb_def, current_probe_inst_def,
    venomInstTheory.mk_raw_function_def, venomInstTheory.phi_pairs_def,
    venomInstTheory.fn_insts_def] >>
  gvs[venomInstTheory.phi_pairs_def] >> EVAL_TAC >>
  gvs[venomInstTheory.fn_insts_blocks_def, venomInstTheory.phi_pairs_def,
    fn_cfg_edge_def, venomInstTheory.bb_succs_def] >> EVAL_TAC >>
  gvs[venomInstTheory.get_successors_def, venomInstTheory.is_terminator_def,
    venomStateTheory.get_label_def] >> dsimp[]
QED

Resume history_probe_static_premises[control]:
  rw[fn_phi_operands_single_def_def, fn_phi_outputs_single_def_def,
    fn_phis_non_degenerate_def, fn_phis_cover_preds_def, fn_inst_wf_def,
    current_probe_loop_def, current_probe_inst_def,
    venomInstTheory.mk_raw_function_def, venomInstTheory.phi_pairs_def,
    venomInstTheory.fn_insts_def] >>
  gvs[venomInstTheory.phi_pairs_def] >> EVAL_TAC >>
  gvs[venomInstTheory.fn_insts_blocks_def, venomInstTheory.phi_pairs_def,
    fn_cfg_edge_def, venomInstTheory.bb_succs_def] >> EVAL_TAC >>
  gvs[venomInstTheory.get_successors_def, venomInstTheory.is_terminator_def,
    venomStateTheory.get_label_def] >> dsimp[]
QED

Finalise history_probe_static_premises


Theorem history_probe_cfg_table[local]:
  fn_cfg_edge fn a b <=>
    ?succs. MEM (a,succs) (MAP (\bb. (bb.bb_label,bb_succs bb)) fn.fn_blocks) /\
      MEM b succs
Proof
  simp[fn_cfg_edge_def, listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem history_probe_successors:
  MAP (\bb. (bb.bb_label, bb_succs bb)) history_probe_diamond.fn_blocks =
    [("E",["R";"L"]);("L",["H"]);("R",["H"]);("H",["X";"H"]);("X",[])] /\
  MAP (\bb. (bb.bb_label, bb_succs bb)) history_probe_backedges.fn_blocks =
    [("E",["H"]);("H",["S";"D"]);("D",["H"]);("S",["H"])] /\
  MAP (\bb. (bb.bb_label, bb_succs bb)) history_probe_nested.fn_blocks =
    [("E",["H"]);("H",["I"]);("I",["J";"D"]);("D",["I"]);("J",["H"])] /\
  MAP (\bb. (bb.bb_label, bb_succs bb)) history_probe_irreducible.fn_blocks =
    [("E",["I";"H"]);("H",["I"]);("I",["H"])] /\
  MAP (\bb. (bb.bb_label, bb_succs bb)) current_probe_loop.fn_blocks =
    [("E",["D"]);("D",["X";"D"]);("X",[])]
Proof
  EVAL_TAC
QED

Theorem history_probe_edges:
  (!a b. fn_cfg_edge history_probe_diamond a b <=>
    (a = "E" /\ (b = "L" \/ b = "R")) \/
    ((a = "L" \/ a = "R") /\ b = "H") \/
    (a = "H" /\ (b = "H" \/ b = "X"))) /\
  (!a b. fn_cfg_edge history_probe_backedges a b <=>
    (a = "E" /\ b = "H") \/ (a = "H" /\ (b = "D" \/ b = "S")) \/
    ((a = "D" \/ a = "S") /\ b = "H")) /\
  (!a b. fn_cfg_edge history_probe_nested a b <=>
    (a = "E" /\ b = "H") \/ (a = "H" /\ b = "I") \/
    (a = "I" /\ (b = "D" \/ b = "J")) \/ (a = "D" /\ b = "I") \/
    (a = "J" /\ b = "H")) /\
  (!a b. fn_cfg_edge history_probe_irreducible a b <=>
    (a = "E" /\ (b = "H" \/ b = "I")) \/
    (a = "H" /\ b = "I") \/ (a = "I" /\ b = "H")) /\
  (!a b. fn_cfg_edge current_probe_loop a b <=>
    (a = "E" /\ b = "D") \/ (a = "D" /\ (b = "D" \/ b = "X")))
Proof
  simp[history_probe_cfg_table, history_probe_successors] >> dsimp[] >> metis_tac[]
QED

Theorem history_probe_all_reachable:
  !fn. MEM fn [history_probe_diamond; history_probe_backedges;
      history_probe_nested; history_probe_irreducible; current_probe_loop] ==>
    all_reachable fn
Proof
  gen_tac >> pure_rewrite_tac[listTheory.MEM] >> strip_tac >> gvs[]
  >- suspend "diamond_reach"
  >- suspend "backedges_reach"
  >- suspend "nested_reach"
  >- suspend "irreducible_reach"
  >> suspend "control_reach"
QED

Resume history_probe_all_reachable[diamond_reach]:
  assume_tac (SRULE [history_probe_diamond_def, history_probe_bb_def,
    venomInstTheory.mk_raw_function_def] (cj 1 history_probe_edges)) >>
  rw[all_reachable_def, history_probe_diamond_def, history_probe_bb_def,
    venomInstTheory.mk_raw_function_def] >>
  simp[fn_reachable_def, venomInstTheory.fn_entry_label_def,
    venomInstTheory.entry_block_def] >>
  gvs[GSYM history_probe_diamond_def] >>
  simp[Once relationTheory.RTC_CASES1] >> dsimp[] >>
  simp[Once relationTheory.RTC_CASES1] >> dsimp[] >>
  simp[Once relationTheory.RTC_CASES1] >> dsimp[]
QED

Resume history_probe_all_reachable[backedges_reach]:
  assume_tac (SRULE [history_probe_backedges_def, history_probe_bb_def,
    venomInstTheory.mk_raw_function_def] (cj 2 history_probe_edges)) >>
  rw[all_reachable_def, history_probe_backedges_def, history_probe_bb_def,
    venomInstTheory.mk_raw_function_def] >>
  simp[fn_reachable_def, venomInstTheory.fn_entry_label_def,
    venomInstTheory.entry_block_def] >>
  simp[Once relationTheory.RTC_CASES1] >> dsimp[] >>
  simp[Once relationTheory.RTC_CASES1] >> dsimp[]
QED

Resume history_probe_all_reachable[nested_reach]:
  assume_tac (SRULE [history_probe_nested_def, history_probe_bb_def,
    venomInstTheory.mk_raw_function_def] (cj 3 history_probe_edges)) >>
  rw[all_reachable_def, history_probe_nested_def, history_probe_bb_def,
    venomInstTheory.mk_raw_function_def] >>
  simp[fn_reachable_def, venomInstTheory.fn_entry_label_def,
    venomInstTheory.entry_block_def] >>
  simp[Once relationTheory.RTC_CASES1] >> dsimp[] >>
  simp[Once relationTheory.RTC_CASES1] >> dsimp[] >>
  simp[Once relationTheory.RTC_CASES1] >> dsimp[]
QED

Resume history_probe_all_reachable[irreducible_reach]:
  assume_tac (SRULE [history_probe_irreducible_def, history_probe_bb_def,
    venomInstTheory.mk_raw_function_def] (cj 4 history_probe_edges)) >>
  rw[all_reachable_def, history_probe_irreducible_def, history_probe_bb_def,
    venomInstTheory.mk_raw_function_def] >>
  simp[fn_reachable_def, venomInstTheory.fn_entry_label_def,
    venomInstTheory.entry_block_def] >>
  simp[Once relationTheory.RTC_CASES1] >> dsimp[]
QED

Resume history_probe_all_reachable[control_reach]:
  assume_tac (SRULE [current_probe_loop_def,
    venomInstTheory.mk_raw_function_def] (cj 5 history_probe_edges)) >>
  rw[all_reachable_def, current_probe_loop_def,
    venomInstTheory.mk_raw_function_def] >>
  simp[fn_reachable_def, venomInstTheory.fn_entry_label_def,
    venomInstTheory.entry_block_def] >>
  simp[Once relationTheory.RTC_CASES1] >> dsimp[] >>
  simp[Once relationTheory.RTC_CASES1] >> dsimp[]
QED

Finalise history_probe_all_reachable


Theorem history_probe_def_entry[local]:
  fn_entry_label fn = SOME entry /\ MEM ebb fn.fn_blocks /\
  ebb.bb_label = entry /\ entry <> bb.bb_label /\
  MEM d ebb.bb_instructions /\ MEM v d.inst_outputs ==>
  def_on_all_paths fn bb cut v
Proof
  rw[def_on_all_paths_def] >> disj1_tac >>
  qexistsl [`0`,`ebb`,`d`] >>
  Cases_on `path` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

Theorem history_probe_def_local[local]:
  i < LENGTH bb.bb_instructions /\
  MEM v (EL i bb.bb_instructions).inst_outputs /\
  (cut = NONE \/ ?use j. cut = SOME use /\ i < j /\
    j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = use) ==>
  def_on_all_paths fn bb cut v
Proof
  rw[def_on_all_paths_def] >> disj2_tac >> qexists `i` >> simp[] >>
  qexists `j` >> simp[]
QED

Theorem history_probe_entry_defs[local]:
  MEM (fn,v) [(history_probe_diamond,"a");(history_probe_diamond,"b");
    (history_probe_backedges,"a");(history_probe_backedges,"b");
    (history_probe_backedges,"x");(history_probe_nested,"a");
    (history_probe_nested,"b");(history_probe_nested,"x");
    (history_probe_irreducible,"a");(history_probe_irreducible,"b");
    (history_probe_irreducible,"x");(current_probe_loop,"a")] /\
  bb.bb_label <> "E" ==> def_on_all_paths fn bb cut v
Proof
  strip_tac >> irule history_probe_def_entry >>
  qexistsl [`current_probe_inst (if v = "a" then 0 else if v = "b" then 1 else 2)
    ASSIGN [Lit (if v = "a" then 1w else if v = "b" then 2w else 3w)] [v]`,
    `HD fn.fn_blocks`, `"E"`] >>
  gvs[] >>
  simp[history_probe_diamond_def, history_probe_backedges_def,
    history_probe_nested_def, history_probe_irreducible_def, current_probe_loop_def,
    history_probe_bb_def, venomInstTheory.mk_raw_function_def,
    venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def,
    current_probe_inst_def]
QED

Theorem history_probe_defs_reach_uses:
  !fn. MEM fn [history_probe_diamond; history_probe_backedges;
      history_probe_nested; history_probe_irreducible; current_probe_loop] ==>
    fn_defs_reach_uses fn
Proof
  gen_tac >> pure_rewrite_tac[listTheory.MEM] >> strip_tac >> gvs[]
  >- suspend "diamond_defs"
  >- suspend "backedges_defs"
  >- suspend "nested_defs"
  >- suspend "irreducible_defs"
  >> suspend "control_defs"
QED

Resume history_probe_defs_reach_uses[backedges_defs]:
  rw[fn_defs_reach_uses_def, history_probe_backedges_def, history_probe_bb_def,
    venomInstTheory.mk_raw_function_def] >>
  gvs[current_probe_inst_def, venomInstTheory.phi_pairs_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[GSYM (SRULE [history_probe_bb_def, current_probe_inst_def,
    venomInstTheory.mk_raw_function_def] history_probe_backedges_def)]
  >- (irule history_probe_def_local >> qexists `0` >> simp[])
  >~ [`def_on_all_paths _ _ _ "v"`]
  >- (irule history_probe_def_local >> qexists `0` >> simp[] >>
      qexists `1` >> simp[])
  >~ [`def_on_all_paths _ _ _ "z"`]
  >- (irule history_probe_def_local >> qexists `1` >> simp[] >>
      qexists `2` >> simp[]) >>
  irule history_probe_entry_defs >> simp[]
QED

Resume history_probe_defs_reach_uses[nested_defs]:
  rw[fn_defs_reach_uses_def, history_probe_nested_def, history_probe_bb_def,
    venomInstTheory.mk_raw_function_def] >>
  gvs[current_probe_inst_def, venomInstTheory.phi_pairs_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[GSYM (SRULE [history_probe_bb_def, current_probe_inst_def,
    venomInstTheory.mk_raw_function_def] history_probe_nested_def)]
  >- (irule history_probe_def_local >> qexists `0` >> simp[])
  >~ [`def_on_all_paths _ _ _ "v"`]
  >- (irule history_probe_def_local >> qexists `0` >> simp[] >>
      qexists `1` >> simp[])
  >~ [`def_on_all_paths _ _ _ "w"`]
  >- (irule history_probe_def_local >> qexists `0` >> simp[] >>
      qexists `1` >> simp[]) >>
  irule history_probe_entry_defs >> simp[]
QED

Resume history_probe_defs_reach_uses[irreducible_defs]:
  rw[fn_defs_reach_uses_def, history_probe_irreducible_def, history_probe_bb_def,
    venomInstTheory.mk_raw_function_def] >>
  gvs[current_probe_inst_def, venomInstTheory.phi_pairs_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[GSYM (SRULE [history_probe_bb_def, current_probe_inst_def,
    venomInstTheory.mk_raw_function_def] history_probe_irreducible_def)]
  >- (irule history_probe_def_local >> qexists `0` >> simp[] >>
      qexists `3` >> simp[])
  >- (irule history_probe_def_local >> qexists `0` >> simp[])
  >~ [`def_on_all_paths _ _ _ "v"`]
  >- (irule history_probe_def_local >> qexists `0` >> simp[] >>
      qexists `1` >> simp[]) >>
  irule history_probe_entry_defs >> simp[]
QED

Resume history_probe_defs_reach_uses[control_defs]:
  rw[fn_defs_reach_uses_def, current_probe_loop_def,
    venomInstTheory.mk_raw_function_def] >>
  gvs[current_probe_inst_def, venomInstTheory.phi_pairs_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[GSYM (SRULE [current_probe_inst_def,
    venomInstTheory.mk_raw_function_def] current_probe_loop_def)]
  >- (irule history_probe_def_local >> qexists `0` >> simp[])
  >- (irule history_probe_def_local >> qexists `1` >> simp[]) >>
  irule history_probe_def_local >> qexists `0` >> simp[] >>
  qexists `2` >> simp[]
QED

Theorem history_probe_diamond_x[local]:
  bb.bb_label = "H" ==> def_on_all_paths history_probe_diamond bb cut "x"
Proof
  strip_tac >>
  `fn_entry_label history_probe_diamond = SOME "E"` by EVAL_TAC >>
  rw[def_on_all_paths_def] >> disj1_tac >>
  Cases_on `path` >> gvs[] >> Cases_on `t` >> gvs[] >>
  gvs[Once is_fn_path_def, history_probe_edges] >>
  Cases_on `t'` >> gvs[] >>
  qexists `1`
  >- (qexistsl [`EL 1 history_probe_diamond.fn_blocks`,
        `current_probe_inst 3 ASSIGN [Lit 3w] ["x"]`] >>
      simp[history_probe_diamond_def, history_probe_bb_def, current_probe_inst_def,
        venomInstTheory.mk_raw_function_def]) >>
  qexistsl [`EL 2 history_probe_diamond.fn_blocks`,
    `current_probe_inst 5 ASSIGN [Lit 4w] ["x"]`] >>
  simp[history_probe_diamond_def, history_probe_bb_def, current_probe_inst_def,
    venomInstTheory.mk_raw_function_def]
QED

Resume history_probe_defs_reach_uses[diamond_defs]:
  rw[fn_defs_reach_uses_def, history_probe_diamond_def, history_probe_bb_def,
    venomInstTheory.mk_raw_function_def] >>
  gvs[current_probe_inst_def, venomInstTheory.phi_pairs_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[GSYM (SRULE [history_probe_bb_def, current_probe_inst_def,
    venomInstTheory.mk_raw_function_def] history_probe_diamond_def)]
  >- (irule history_probe_def_local >> qexists `0` >> simp[] >>
      qexists `2` >> simp[])
  >~ [`def_on_all_paths _ _ _ "x"`]
  >- (irule history_probe_diamond_x >> simp[])
  >~ [`def_on_all_paths _ _ _ "v"`]
  >- (irule history_probe_def_local >> qexists `0` >> simp[] >>
      qexists `1` >> simp[])
  >~ [`def_on_all_paths _ _ _ "z"`]
  >- (irule history_probe_def_local >> qexists `1` >> simp[] >>
      qexists `2` >> simp[]) >>
  irule history_probe_entry_defs >> simp[]
QED

Finalise history_probe_defs_reach_uses

Theorem history_probe_admissible:
  !fn. MEM fn [history_probe_diamond; history_probe_backedges;
      history_probe_nested; history_probe_irreducible; current_probe_loop] ==>
    fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
    fn_phis_cover_preds fn /\ fn_phi_outputs_single_def fn /\
    fn_phis_non_degenerate fn /\ all_reachable fn /\ fn_inst_wf fn /\
    wf_function fn /\ first_block_no_preds fn /\ first_block_no_phi fn /\
    ir_supply_covers_fn history_probe_supply fn /\
    ir_supply_inst_ok history_probe_supply
Proof
  metis_tac[history_probe_static_premises, history_probe_all_reachable,
    history_probe_defs_reach_uses]
QED

(* A bounded prefix of actual source/target block executions, not a runtime
   invariant or a same-fuel bisimulation claim. *)
Definition history_probe_walk_def:
  (history_probe_walk 0 ctx fn s = SOME s) /\
  (history_probe_walk (SUC n) ctx fn s =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => NONE
    | SOME bb =>
        case run_block 1 ctx bb s of
          OK s' => history_probe_walk n ctx fn s'
        | _ => NONE)
End

Definition history_probe_observe_def:
  history_probe_observe n ctx fn =
    OPTION_MAP (\s. (s.vs_current_bb, s.vs_prev_bb,
      MAP (FLOOKUP s.vs_vars) ["v";"z";"w"]))
      (history_probe_walk n ctx fn (init_venom_state "E"))
End

Definition history_probe_revisits_def:
  history_probe_revisits ctx fn n =
    let target = FST (make_ssa_current_fn history_probe_supply fn) in
      (history_probe_observe (n - 1) ctx fn,
       history_probe_observe n ctx fn,
       history_probe_observe (n - 1) ctx target,
       history_probe_observe n ctx target)
End


Definition history_probe_diamond_target_def:
  history_probe_diamond_target =
  [history_probe_bb "E"
    [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
     current_probe_inst 1 ASSIGN [Lit 2w] ["b"];
     current_probe_inst 2 JNZ [Var "a"; Label "L"; Label "R"] []];
   history_probe_bb "L"
    [current_probe_inst 3 ASSIGN [Lit 3w] ["formal_var_2"];
     current_probe_inst 4 JMP [Label "H"] []];
   history_probe_bb "R"
    [current_probe_inst 5 ASSIGN [Lit 4w] ["formal_var_1"];
     current_probe_inst 6 JMP [Label "H"] []];
   history_probe_bb "H"
    [current_probe_inst 101 PHI [Label "L"; Var "formal_var_2";
        Label "R"; Var "formal_var_1"; Label "H"; Var "x"] ["x"];
     current_probe_inst 100 PHI [Label "L"; Var "a"; Label "R"; Var "b";
        Label "H"; Var "a"] ["formal_var_0"];
     current_probe_inst 7 ASSIGN [Var "formal_var_0"] ["v"];
     current_probe_inst 8 ADD [Var "x"; Var "formal_var_0"] ["z"];
     current_probe_inst 9 JNZ [Var "z"; Label "H"; Label "X"] []];
   history_probe_bb "X" [current_probe_inst 10 STOP [] []]]
End

Theorem history_probe_diamond_target_blocks:
  (FST (make_ssa_current_fn history_probe_supply history_probe_diamond)).fn_blocks =
    history_probe_diamond_target
Proof
  EVAL_TAC
QED

Theorem history_probe_dimindex[local,simp]:
  dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Definition history_probe_diamond_s1_def:
  history_probe_diamond_s1 = (init_venom_state "E") with
    <|vs_vars := FEMPTY |++ [("a",1w);("b",2w)];
      vs_current_bb := "L"; vs_prev_bb := SOME "E"; vs_inst_idx := 0|>
End

Theorem history_probe_diamond_entry_step:
  run_block 1 ctx (HD history_probe_diamond.fn_blocks)
    (init_venom_state "E") = OK history_probe_diamond_s1
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    history_probe_dimindex, finite_mapTheory.FLOOKUP_EXT,
    FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED

Definition history_probe_diamond_s2_def:
  history_probe_diamond_s2 = history_probe_diamond_s1 with
    <|vs_vars := FEMPTY |++ [("a",1w);("b",2w);("x",3w)];
      vs_current_bb := "H"; vs_prev_bb := SOME "L"|>
End
Definition history_probe_diamond_s3_def:
  history_probe_diamond_s3 = history_probe_diamond_s2 with
    <|vs_vars := FEMPTY |++ [("a",1w);("b",2w);("x",3w);("v",1w);("z",4w)];
      vs_prev_bb := SOME "H"|>
End
Definition history_probe_diamond_t2_def:
  history_probe_diamond_t2 = history_probe_diamond_s1 with
    <|vs_vars := FEMPTY |++ [("a",1w);("b",2w);("formal_var_2",3w)];
      vs_current_bb := "H"; vs_prev_bb := SOME "L"|>
End
Definition history_probe_diamond_t3_def:
  history_probe_diamond_t3 = history_probe_diamond_t2 with
    <|vs_vars := FEMPTY |++ [("a",1w);("b",2w);("formal_var_2",3w);
        ("x",3w);("formal_var_0",1w);("v",1w);("z",4w)];
      vs_prev_bb := SOME "H"|>
End

Theorem history_probe_diamond_source_L:
  run_block 1 ctx (EL 1 history_probe_diamond.fn_blocks)
    history_probe_diamond_s1 = OK history_probe_diamond_s2
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    history_probe_dimindex, finite_mapTheory.FLOOKUP_EXT,
    FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_diamond_source_H:
  run_block 1 ctx (EL 3 history_probe_diamond.fn_blocks)
    history_probe_diamond_s2 = OK history_probe_diamond_s3
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    history_probe_dimindex, finite_mapTheory.FLOOKUP_EXT,
    FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_diamond_source_revisit:
  run_block 1 ctx (EL 3 history_probe_diamond.fn_blocks)
    history_probe_diamond_s3 = OK history_probe_diamond_s3
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    history_probe_dimindex, finite_mapTheory.FLOOKUP_EXT,
    FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_diamond_target_E:
  run_block 1 ctx (HD history_probe_diamond_target)
    (init_venom_state "E") = OK history_probe_diamond_s1
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    history_probe_dimindex, finite_mapTheory.FLOOKUP_EXT,
    FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_diamond_target_L:
  run_block 1 ctx (EL 1 history_probe_diamond_target)
    history_probe_diamond_s1 = OK history_probe_diamond_t2
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    history_probe_dimindex, finite_mapTheory.FLOOKUP_EXT,
    FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_diamond_target_H:
  run_block 1 ctx (EL 3 history_probe_diamond_target)
    history_probe_diamond_t2 = OK history_probe_diamond_t3
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    history_probe_dimindex, finite_mapTheory.FLOOKUP_EXT,
    FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_diamond_target_revisit:
  run_block 1 ctx (EL 3 history_probe_diamond_target)
    history_probe_diamond_t3 = OK history_probe_diamond_t3
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    history_probe_dimindex, finite_mapTheory.FLOOKUP_EXT,
    FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem history_probe_diamond_source_lookups:
  lookup_block (init_venom_state "E").vs_current_bb history_probe_diamond.fn_blocks =
    SOME (HD history_probe_diamond.fn_blocks) /\
  lookup_block history_probe_diamond_s1.vs_current_bb history_probe_diamond.fn_blocks =
    SOME (EL 1 history_probe_diamond.fn_blocks) /\
  lookup_block history_probe_diamond_s2.vs_current_bb history_probe_diamond.fn_blocks =
    SOME (EL 3 history_probe_diamond.fn_blocks) /\
  lookup_block history_probe_diamond_s3.vs_current_bb history_probe_diamond.fn_blocks =
    SOME (EL 3 history_probe_diamond.fn_blocks)
Proof
  EVAL_TAC
QED
Theorem history_probe_diamond_target_lookups:
  lookup_block (init_venom_state "E").vs_current_bb history_probe_diamond_target =
    SOME (HD history_probe_diamond_target) /\
  lookup_block history_probe_diamond_s1.vs_current_bb history_probe_diamond_target =
    SOME (EL 1 history_probe_diamond_target) /\
  lookup_block history_probe_diamond_t2.vs_current_bb history_probe_diamond_target =
    SOME (EL 3 history_probe_diamond_target) /\
  lookup_block history_probe_diamond_t3.vs_current_bb history_probe_diamond_target =
    SOME (EL 3 history_probe_diamond_target)
Proof
  EVAL_TAC
QED

Theorem history_probe_walk_positive[local]:
  0 < n ==>
  history_probe_walk n ctx fn s =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => NONE
    | SOME bb =>
        case run_block 1 ctx bb s of
          OK s' => history_probe_walk (n - 1) ctx fn s'
        | _ => NONE
Proof
  Cases_on `n` >> simp[history_probe_walk_def]
QED

Theorem history_probe_diamond_walks:
  (history_probe_walk 3 ctx history_probe_diamond (init_venom_state "E") =
    SOME history_probe_diamond_s3) /\
  (history_probe_walk 4 ctx history_probe_diamond (init_venom_state "E") =
    SOME history_probe_diamond_s3) /\
  (history_probe_walk 3 ctx
      (FST (make_ssa_current_fn history_probe_supply history_probe_diamond))
      (init_venom_state "E") = SOME history_probe_diamond_t3) /\
  (history_probe_walk 4 ctx
      (FST (make_ssa_current_fn history_probe_supply history_probe_diamond))
      (init_venom_state "E") = SOME history_probe_diamond_t3)
Proof
  simp[history_probe_walk_positive, history_probe_walk_def,
    history_probe_diamond_target_blocks,
    history_probe_diamond_source_lookups, history_probe_diamond_target_lookups,
    history_probe_diamond_entry_step, history_probe_diamond_source_L,
    history_probe_diamond_source_H, history_probe_diamond_source_revisit,
    history_probe_diamond_target_E, history_probe_diamond_target_L,
    history_probe_diamond_target_H, history_probe_diamond_target_revisit]
QED

Theorem history_probe_diamond_revisit_agreement:
  (\(s0,s1,t0,t1). IS_SOME s0 /\ IS_SOME s1 /\ s0 = t0 /\ s1 = t1)
    (history_probe_revisits ctx history_probe_diamond 4)
Proof
  simp[history_probe_revisits_def, history_probe_observe_def,
    history_probe_diamond_walks] >> EVAL_TAC
QED

Definition history_probe_backedges_target_def:
  history_probe_backedges_target =
  [history_probe_bb "E"
    [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
     current_probe_inst 1 ASSIGN [Lit 2w] ["b"];
     current_probe_inst 2 ASSIGN [Lit 3w] ["x"];
     current_probe_inst 3 JMP [Label "H"] []];
   history_probe_bb "H"
    [current_probe_inst 101 PHI [Label "E"; Var "x"; Label "D";
        Var "formal_var_2"; Label "S"; Var "formal_var_0"] ["formal_var_0"];
     current_probe_inst 100 PHI [Label "E"; Var "a"; Label "D"; Var "b";
        Label "S"; Var "a"] ["formal_var_1"];
     current_probe_inst 4 ASSIGN [Var "formal_var_1"] ["v"];
     current_probe_inst 5 ADD [Var "formal_var_0"; Var "formal_var_1"] ["z"];
     current_probe_inst 6 JNZ [Var "z"; Label "D"; Label "S"] []];
   history_probe_bb "D"
    [current_probe_inst 7 ASSIGN [Lit 4w] ["formal_var_2"];
     current_probe_inst 8 JMP [Label "H"] []];
   history_probe_bb "S" [current_probe_inst 9 JMP [Label "H"] []]]
End

Theorem history_probe_backedges_target_blocks:
  (FST (make_ssa_current_fn history_probe_supply history_probe_backedges)).fn_blocks =
    history_probe_backedges_target
Proof
  EVAL_TAC
QED

Definition history_probe_state_def:
  history_probe_state xs prev cur = (init_venom_state "E") with
    <|vs_vars := FEMPTY |++ xs; vs_prev_bb := SOME prev; vs_current_bb := cur|>
End
Definition history_probe_backedges_s1_def:
  history_probe_backedges_s1 = history_probe_state [("a",1w);("b",2w);("x",3w)] "E" "H"
End
Definition history_probe_backedges_s2_def:
  history_probe_backedges_s2 = history_probe_state
    [("a",1w);("b",2w);("x",3w);("v",1w);("z",4w)] "H" "D"
End
Definition history_probe_backedges_s3_def:
  history_probe_backedges_s3 = history_probe_state
    [("a",1w);("b",2w);("x",4w);("v",1w);("z",4w)] "D" "H"
End
Definition history_probe_backedges_s4_def:
  history_probe_backedges_s4 = history_probe_state
    [("a",1w);("b",2w);("x",4w);("v",2w);("z",6w)] "H" "D"
End
Definition history_probe_backedges_t2_def:
  history_probe_backedges_t2 = history_probe_state
    [("a",1w);("b",2w);("x",3w);("formal_var_0",3w);
     ("formal_var_1",1w);("v",1w);("z",4w)] "H" "D"
End
Definition history_probe_backedges_t3_def:
  history_probe_backedges_t3 = history_probe_state
    [("a",1w);("b",2w);("x",3w);("formal_var_0",3w);
     ("formal_var_1",1w);("v",1w);("z",4w);("formal_var_2",4w)] "D" "H"
End
Definition history_probe_backedges_t4_def:
  history_probe_backedges_t4 = history_probe_state
    [("a",1w);("b",2w);("x",3w);("formal_var_0",4w);
     ("formal_var_1",2w);("v",2w);("z",6w);("formal_var_2",4w)] "H" "D"
End

Theorem history_probe_backedges_source_E:
  run_block 1 ctx (HD history_probe_backedges.fn_blocks)
    (init_venom_state "E") = OK history_probe_backedges_s1
Proof
  EVAL_TAC >> simp[]
QED
Theorem history_probe_backedges_source_H:
  run_block 1 ctx (EL 1 history_probe_backedges.fn_blocks)
    history_probe_backedges_s1 = OK history_probe_backedges_s2
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def]
QED
Theorem history_probe_backedges_source_D:
  run_block 1 ctx (EL 2 history_probe_backedges.fn_blocks)
    history_probe_backedges_s2 = OK history_probe_backedges_s3
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM,
    finite_mapTheory.FLOOKUP_UPDATE] >> gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_backedges_source_revisit:
  run_block 1 ctx (EL 1 history_probe_backedges.fn_blocks)
    history_probe_backedges_s3 = OK history_probe_backedges_s4
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_backedges_target_E:
  run_block 1 ctx (HD history_probe_backedges_target)
    (init_venom_state "E") = OK history_probe_backedges_s1
Proof
  EVAL_TAC >> simp[]
QED
Theorem history_probe_backedges_target_H:
  run_block 1 ctx (EL 1 history_probe_backedges_target)
    history_probe_backedges_s1 = OK history_probe_backedges_t2
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_backedges_target_D:
  run_block 1 ctx (EL 2 history_probe_backedges_target)
    history_probe_backedges_t2 = OK history_probe_backedges_t3
Proof
  EVAL_TAC >> simp[]
QED
Theorem history_probe_backedges_target_revisit:
  run_block 1 ctx (EL 1 history_probe_backedges_target)
    history_probe_backedges_t3 = OK history_probe_backedges_t4
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem history_probe_backedges_source_lookups:
  lookup_block (init_venom_state "E").vs_current_bb history_probe_backedges.fn_blocks =
    SOME (HD history_probe_backedges.fn_blocks) /\
  lookup_block history_probe_backedges_s1.vs_current_bb history_probe_backedges.fn_blocks =
    SOME (EL 1 history_probe_backedges.fn_blocks) /\
  lookup_block history_probe_backedges_s2.vs_current_bb history_probe_backedges.fn_blocks =
    SOME (EL 2 history_probe_backedges.fn_blocks) /\
  lookup_block history_probe_backedges_s3.vs_current_bb history_probe_backedges.fn_blocks =
    SOME (EL 1 history_probe_backedges.fn_blocks)
Proof
  EVAL_TAC
QED
Theorem history_probe_backedges_target_lookups:
  lookup_block (init_venom_state "E").vs_current_bb history_probe_backedges_target =
    SOME (HD history_probe_backedges_target) /\
  lookup_block history_probe_backedges_s1.vs_current_bb history_probe_backedges_target =
    SOME (EL 1 history_probe_backedges_target) /\
  lookup_block history_probe_backedges_t2.vs_current_bb history_probe_backedges_target =
    SOME (EL 2 history_probe_backedges_target) /\
  lookup_block history_probe_backedges_t3.vs_current_bb history_probe_backedges_target =
    SOME (EL 1 history_probe_backedges_target)
Proof
  EVAL_TAC
QED
Theorem history_probe_backedges_walks:
  (history_probe_walk 3 ctx history_probe_backedges (init_venom_state "E") =
    SOME history_probe_backedges_s3) /\
  (history_probe_walk 4 ctx history_probe_backedges (init_venom_state "E") =
    SOME history_probe_backedges_s4) /\
  (history_probe_walk 3 ctx
      (FST (make_ssa_current_fn history_probe_supply history_probe_backedges))
      (init_venom_state "E") = SOME history_probe_backedges_t3) /\
  (history_probe_walk 4 ctx
      (FST (make_ssa_current_fn history_probe_supply history_probe_backedges))
      (init_venom_state "E") = SOME history_probe_backedges_t4)
Proof
  simp[history_probe_walk_positive, history_probe_walk_def,
    history_probe_backedges_target_blocks,
    history_probe_backedges_source_lookups, history_probe_backedges_target_lookups,
    history_probe_backedges_source_E, history_probe_backedges_source_H,
    history_probe_backedges_source_D, history_probe_backedges_source_revisit,
    history_probe_backedges_target_E, history_probe_backedges_target_H,
    history_probe_backedges_target_D, history_probe_backedges_target_revisit]
QED
Theorem history_probe_backedges_revisit_agreement:
  (\(s0,s1,t0,t1). IS_SOME s0 /\ IS_SOME s1 /\ s0 = t0 /\ s1 = t1)
    (history_probe_revisits ctx history_probe_backedges 4)
Proof
  simp[history_probe_revisits_def, history_probe_observe_def,
    history_probe_backedges_walks] >> EVAL_TAC
QED

Definition history_probe_control_target_def:
  history_probe_control_target =
  [history_probe_bb "E"
    [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
     current_probe_inst 1 JMP [Label "D"] []];
   history_probe_bb "D"
    [current_probe_inst 100 PHI [Label "E"; Var "a"; Label "D"; Var "b"] ["formal_var_0"];
     current_probe_inst 2 ASSIGN [Var "formal_var_0"] ["v"];
     current_probe_inst 3 ASSIGN [Lit 2w] ["b"];
     current_probe_inst 4 JNZ [Var "formal_var_0"; Label "D"; Label "X"] []];
   history_probe_bb "X" [current_probe_inst 5 STOP [] []]]
End
Theorem history_probe_control_target_blocks:
  (FST (make_ssa_current_fn history_probe_supply current_probe_loop)).fn_blocks =
    history_probe_control_target
Proof
  EVAL_TAC
QED

Definition history_probe_control_s1_def:
  history_probe_control_s1 = history_probe_state [("a",1w)] "E" "D"
End
Definition history_probe_control_s2_def:
  history_probe_control_s2 = history_probe_state [("a",1w);("v",1w);("b",2w)] "D" "D"
End
Definition history_probe_control_s3_def:
  history_probe_control_s3 = history_probe_state [("a",1w);("v",2w);("b",2w)] "D" "D"
End
Definition history_probe_control_t2_def:
  history_probe_control_t2 = history_probe_state
    [("a",1w);("formal_var_0",1w);("v",1w);("b",2w)] "D" "D"
End
Definition history_probe_control_t3_def:
  history_probe_control_t3 = history_probe_state
    [("a",1w);("formal_var_0",2w);("v",2w);("b",2w)] "D" "D"
End
Theorem history_probe_control_source_E:
  run_block 1 ctx (HD current_probe_loop.fn_blocks)
    (init_venom_state "E") = OK history_probe_control_s1
Proof
  EVAL_TAC >> simp[]
QED
Theorem history_probe_control_source_D:
  run_block 1 ctx (EL 1 current_probe_loop.fn_blocks)
    history_probe_control_s1 = OK history_probe_control_s2
Proof
  EVAL_TAC >> simp[]
QED
Theorem history_probe_control_source_revisit:
  run_block 1 ctx (EL 1 current_probe_loop.fn_blocks)
    history_probe_control_s2 = OK history_probe_control_s3
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM,
    finite_mapTheory.FLOOKUP_UPDATE] >> gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_control_target_E:
  run_block 1 ctx (HD history_probe_control_target)
    (init_venom_state "E") = OK history_probe_control_s1
Proof
  EVAL_TAC >> simp[]
QED
Theorem history_probe_control_target_D:
  run_block 1 ctx (EL 1 history_probe_control_target)
    history_probe_control_s1 = OK history_probe_control_t2
Proof
  EVAL_TAC >> simp[]
QED
Theorem history_probe_control_target_revisit:
  run_block 1 ctx (EL 1 history_probe_control_target)
    history_probe_control_t2 = OK history_probe_control_t3
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM,
    finite_mapTheory.FLOOKUP_UPDATE] >> gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_control_source_lookups:
  lookup_block (init_venom_state "E").vs_current_bb current_probe_loop.fn_blocks =
    SOME (HD current_probe_loop.fn_blocks) /\
  lookup_block history_probe_control_s1.vs_current_bb current_probe_loop.fn_blocks =
    SOME (EL 1 current_probe_loop.fn_blocks) /\
  lookup_block history_probe_control_s2.vs_current_bb current_probe_loop.fn_blocks =
    SOME (EL 1 current_probe_loop.fn_blocks)
Proof
  EVAL_TAC
QED
Theorem history_probe_control_target_lookups:
  lookup_block (init_venom_state "E").vs_current_bb history_probe_control_target =
    SOME (HD history_probe_control_target) /\
  lookup_block history_probe_control_s1.vs_current_bb history_probe_control_target =
    SOME (EL 1 history_probe_control_target) /\
  lookup_block history_probe_control_t2.vs_current_bb history_probe_control_target =
    SOME (EL 1 history_probe_control_target)
Proof
  EVAL_TAC
QED
Theorem history_probe_control_walks:
  (history_probe_walk 2 ctx current_probe_loop (init_venom_state "E") =
    SOME history_probe_control_s2) /\
  (history_probe_walk 3 ctx current_probe_loop (init_venom_state "E") =
    SOME history_probe_control_s3) /\
  (history_probe_walk 2 ctx
      (FST (make_ssa_current_fn history_probe_supply current_probe_loop))
      (init_venom_state "E") = SOME history_probe_control_t2) /\
  (history_probe_walk 3 ctx
      (FST (make_ssa_current_fn history_probe_supply current_probe_loop))
      (init_venom_state "E") = SOME history_probe_control_t3)
Proof
  simp[history_probe_walk_positive, history_probe_walk_def,
    history_probe_control_target_blocks,
    history_probe_control_source_lookups, history_probe_control_target_lookups,
    history_probe_control_source_E, history_probe_control_source_D,
    history_probe_control_source_revisit, history_probe_control_target_E,
    history_probe_control_target_D, history_probe_control_target_revisit]
QED
Theorem history_probe_control_revisit_agreement:
  (\(s0,s1,t0,t1). IS_SOME s0 /\ IS_SOME s1 /\ s0 = t0 /\ s1 = t1)
    (history_probe_revisits ctx current_probe_loop 3)
Proof
  simp[history_probe_revisits_def, history_probe_observe_def,
    history_probe_control_walks] >> EVAL_TAC
QED

Definition history_probe_nested_target_def:
  history_probe_nested_target =
  [history_probe_bb "E"
    [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
     current_probe_inst 1 ASSIGN [Lit 2w] ["b"];
     current_probe_inst 2 ASSIGN [Lit 3w] ["x"];
     current_probe_inst 3 JMP [Label "H"] []];
   history_probe_bb "H"
    [current_probe_inst 102 PHI [Label "E"; Var "x"; Label "J";
        Var "formal_var_2"] ["formal_var_0"];
     current_probe_inst 101 PHI [Label "E"; Var "a"; Label "J"; Var "b"] ["formal_var_1"];
     current_probe_inst 4 ASSIGN [Var "formal_var_1"] ["v"];
     current_probe_inst 5 ADD [Var "formal_var_0"; Var "formal_var_1"] ["z"];
     current_probe_inst 6 JMP [Label "I"] []];
   history_probe_bb "I"
    [current_probe_inst 100 PHI [Label "H"; Var "formal_var_0"; Label "D";
        Var "formal_var_3"] ["formal_var_2"];
     current_probe_inst 7 ADD [Var "formal_var_2"; Var "a"] ["w"];
     current_probe_inst 8 JNZ [Var "w"; Label "D"; Label "J"] []];
   history_probe_bb "D"
    [current_probe_inst 9 ASSIGN [Lit 4w] ["formal_var_3"];
     current_probe_inst 10 JMP [Label "I"] []];
   history_probe_bb "J" [current_probe_inst 11 JMP [Label "H"] []]]
End
Theorem history_probe_nested_target_blocks:
  (FST (make_ssa_current_fn history_probe_supply history_probe_nested)).fn_blocks =
    history_probe_nested_target
Proof
  EVAL_TAC
QED

Definition history_probe_nested_s2_def:
  history_probe_nested_s2 = history_probe_state
    [("a",1w);("b",2w);("x",3w);("v",1w);("z",4w)] "H" "I"
End
Definition history_probe_nested_s3_def:
  history_probe_nested_s3 = history_probe_state
    [("a",1w);("b",2w);("x",3w);("v",1w);("z",4w);("w",4w)] "I" "D"
End
Definition history_probe_nested_s4_def:
  history_probe_nested_s4 = history_probe_state
    [("a",1w);("b",2w);("x",4w);("v",1w);("z",4w);("w",4w)] "D" "I"
End
Definition history_probe_nested_s5_def:
  history_probe_nested_s5 = history_probe_state
    [("a",1w);("b",2w);("x",4w);("v",1w);("z",4w);("w",5w)] "I" "D"
End
Definition history_probe_nested_t2_def:
  history_probe_nested_t2 = history_probe_state
    [("a",1w);("b",2w);("x",3w);("formal_var_0",3w);
     ("formal_var_1",1w);("v",1w);("z",4w)] "H" "I"
End
Definition history_probe_nested_t3_def:
  history_probe_nested_t3 = history_probe_state
    [("a",1w);("b",2w);("x",3w);("formal_var_0",3w);
     ("formal_var_1",1w);("v",1w);("z",4w);("formal_var_2",3w);("w",4w)] "I" "D"
End
Definition history_probe_nested_t4_def:
  history_probe_nested_t4 = history_probe_state
    [("a",1w);("b",2w);("x",3w);("formal_var_0",3w);
     ("formal_var_1",1w);("v",1w);("z",4w);("formal_var_2",3w);("w",4w);
     ("formal_var_3",4w)] "D" "I"
End
Definition history_probe_nested_t5_def:
  history_probe_nested_t5 = history_probe_state
    [("a",1w);("b",2w);("x",3w);("formal_var_0",3w);
     ("formal_var_1",1w);("v",1w);("z",4w);("formal_var_2",4w);("w",5w);
     ("formal_var_3",4w)] "I" "D"
End
Theorem history_probe_nested_source_E:
  run_block 1 ctx (HD history_probe_nested.fn_blocks)
    (init_venom_state "E") = OK history_probe_backedges_s1
Proof
  EVAL_TAC >> simp[]
QED
Theorem history_probe_nested_source_H:
  run_block 1 ctx (EL 1 history_probe_nested.fn_blocks)
    history_probe_backedges_s1 = OK history_probe_nested_s2
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def]
QED
Theorem history_probe_nested_source_I:
  run_block 1 ctx (EL 2 history_probe_nested.fn_blocks)
    history_probe_nested_s2 = OK history_probe_nested_s3
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def]
QED
Theorem history_probe_nested_source_D:
  run_block 1 ctx (EL 3 history_probe_nested.fn_blocks)
    history_probe_nested_s3 = OK history_probe_nested_s4
Proof
  EVAL_TAC >> simp[finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM,
    finite_mapTheory.FLOOKUP_UPDATE] >> gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_nested_source_revisit:
  run_block 1 ctx (EL 2 history_probe_nested.fn_blocks)
    history_probe_nested_s4 = OK history_probe_nested_s5
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_nested_target_E:
  run_block 1 ctx (HD history_probe_nested_target)
    (init_venom_state "E") = OK history_probe_backedges_s1
Proof
  EVAL_TAC >> simp[]
QED
Theorem history_probe_nested_target_H:
  run_block 1 ctx (EL 1 history_probe_nested_target)
    history_probe_backedges_s1 = OK history_probe_nested_t2
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_nested_target_I:
  run_block 1 ctx (EL 2 history_probe_nested_target)
    history_probe_nested_t2 = OK history_probe_nested_t3
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def]
QED
Theorem history_probe_nested_target_D:
  run_block 1 ctx (EL 3 history_probe_nested_target)
    history_probe_nested_t3 = OK history_probe_nested_t4
Proof
  EVAL_TAC >> simp[]
QED
Theorem history_probe_nested_target_revisit:
  run_block 1 ctx (EL 2 history_probe_nested_target)
    history_probe_nested_t4 = OK history_probe_nested_t5
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem history_probe_nested_source_lookups:
  lookup_block (init_venom_state "E").vs_current_bb history_probe_nested.fn_blocks =
    SOME (HD history_probe_nested.fn_blocks) /\
  lookup_block history_probe_backedges_s1.vs_current_bb history_probe_nested.fn_blocks =
    SOME (EL 1 history_probe_nested.fn_blocks) /\
  lookup_block history_probe_nested_s2.vs_current_bb history_probe_nested.fn_blocks =
    SOME (EL 2 history_probe_nested.fn_blocks) /\
  lookup_block history_probe_nested_s3.vs_current_bb history_probe_nested.fn_blocks =
    SOME (EL 3 history_probe_nested.fn_blocks) /\
  lookup_block history_probe_nested_s4.vs_current_bb history_probe_nested.fn_blocks =
    SOME (EL 2 history_probe_nested.fn_blocks)
Proof
  EVAL_TAC
QED
Theorem history_probe_nested_target_lookups:
  lookup_block (init_venom_state "E").vs_current_bb history_probe_nested_target =
    SOME (HD history_probe_nested_target) /\
  lookup_block history_probe_backedges_s1.vs_current_bb history_probe_nested_target =
    SOME (EL 1 history_probe_nested_target) /\
  lookup_block history_probe_nested_t2.vs_current_bb history_probe_nested_target =
    SOME (EL 2 history_probe_nested_target) /\
  lookup_block history_probe_nested_t3.vs_current_bb history_probe_nested_target =
    SOME (EL 3 history_probe_nested_target) /\
  lookup_block history_probe_nested_t4.vs_current_bb history_probe_nested_target =
    SOME (EL 2 history_probe_nested_target)
Proof
  EVAL_TAC
QED
Theorem history_probe_nested_walks:
  (history_probe_walk 4 ctx history_probe_nested (init_venom_state "E") =
    SOME history_probe_nested_s4) /\
  (history_probe_walk 5 ctx history_probe_nested (init_venom_state "E") =
    SOME history_probe_nested_s5) /\
  (history_probe_walk 4 ctx
      (FST (make_ssa_current_fn history_probe_supply history_probe_nested))
      (init_venom_state "E") = SOME history_probe_nested_t4) /\
  (history_probe_walk 5 ctx
      (FST (make_ssa_current_fn history_probe_supply history_probe_nested))
      (init_venom_state "E") = SOME history_probe_nested_t5)
Proof
  simp[history_probe_walk_positive, history_probe_walk_def,
    history_probe_nested_target_blocks,
    history_probe_nested_source_lookups, history_probe_nested_target_lookups,
    history_probe_nested_source_E, history_probe_nested_source_H,
    history_probe_nested_source_I, history_probe_nested_source_D,
    history_probe_nested_source_revisit, history_probe_nested_target_E,
    history_probe_nested_target_H, history_probe_nested_target_I,
    history_probe_nested_target_D, history_probe_nested_target_revisit]
QED
Theorem history_probe_nested_revisit_agreement:
  (\(s0,s1,t0,t1). IS_SOME s0 /\ IS_SOME s1 /\ s0 = t0 /\ s1 = t1)
    (history_probe_revisits ctx history_probe_nested 5)
Proof
  simp[history_probe_revisits_def, history_probe_observe_def,
    history_probe_nested_walks] >> EVAL_TAC
QED

Definition history_probe_irreducible_target_def:
  history_probe_irreducible_target =
  [history_probe_bb "E"
    [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
     current_probe_inst 1 ASSIGN [Lit 2w] ["b"];
     current_probe_inst 2 ASSIGN [Lit 3w] ["x"];
     current_probe_inst 3 JNZ [Var "a"; Label "H"; Label "I"] []];
   history_probe_bb "H"
    [current_probe_inst 101 PHI [Label "E"; Var "x"; Label "I";
        Var "formal_var_0"] ["formal_var_1"];
     current_probe_inst 4 PHI [Label "E"; Var "a"; Label "I"; Var "b"] ["v"];
     current_probe_inst 5 ADD [Var "formal_var_1"; Var "v"] ["z"];
     current_probe_inst 6 ASSIGN [Lit 4w] ["formal_var_2"];
     current_probe_inst 7 JMP [Label "I"] []];
   history_probe_bb "I"
    [current_probe_inst 100 PHI [Label "E"; Var "x"; Label "H";
        Var "formal_var_2"] ["formal_var_0"];
     current_probe_inst 8 ADD [Var "formal_var_0"; Var "a"] ["w"];
     current_probe_inst 9 JMP [Label "H"] []]]
End
Theorem history_probe_irreducible_target_blocks:
  (FST (make_ssa_current_fn history_probe_supply history_probe_irreducible)).fn_blocks =
    history_probe_irreducible_target
Proof
  EVAL_TAC
QED

Definition history_probe_irreducible_s2_def:
  history_probe_irreducible_s2 = history_probe_state
    [("a",1w);("b",2w);("x",4w);("v",1w);("z",4w)] "H" "I"
End
Definition history_probe_irreducible_s3_def:
  history_probe_irreducible_s3 = history_probe_state
    [("a",1w);("b",2w);("x",4w);("v",1w);("z",4w);("w",5w)] "I" "H"
End
Definition history_probe_irreducible_s4_def:
  history_probe_irreducible_s4 = history_probe_state
    [("a",1w);("b",2w);("x",4w);("v",2w);("z",6w);("w",5w)] "H" "I"
End
Definition history_probe_irreducible_t2_def:
  history_probe_irreducible_t2 = history_probe_state
    [("a",1w);("b",2w);("x",3w);("formal_var_1",3w);
     ("v",1w);("z",4w);("formal_var_2",4w)] "H" "I"
End
Definition history_probe_irreducible_t3_def:
  history_probe_irreducible_t3 = history_probe_state
    [("a",1w);("b",2w);("x",3w);("formal_var_1",3w);
     ("v",1w);("z",4w);("formal_var_2",4w);("formal_var_0",4w);("w",5w)] "I" "H"
End
Definition history_probe_irreducible_t4_def:
  history_probe_irreducible_t4 = history_probe_state
    [("a",1w);("b",2w);("x",3w);("formal_var_1",4w);
     ("v",2w);("z",6w);("formal_var_2",4w);("formal_var_0",4w);("w",5w)] "H" "I"
End
Theorem history_probe_irreducible_source_E:
  run_block 1 ctx (HD history_probe_irreducible.fn_blocks)
    (init_venom_state "E") = OK history_probe_backedges_s1
Proof
  EVAL_TAC >> simp[]
QED
Theorem history_probe_irreducible_source_H:
  run_block 1 ctx (EL 1 history_probe_irreducible.fn_blocks)
    history_probe_backedges_s1 = OK history_probe_irreducible_s2
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_irreducible_source_I:
  run_block 1 ctx (EL 2 history_probe_irreducible.fn_blocks)
    history_probe_irreducible_s2 = OK history_probe_irreducible_s3
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def]
QED
Theorem history_probe_irreducible_source_revisit:
  run_block 1 ctx (EL 1 history_probe_irreducible.fn_blocks)
    history_probe_irreducible_s3 = OK history_probe_irreducible_s4
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_irreducible_target_E:
  run_block 1 ctx (HD history_probe_irreducible_target)
    (init_venom_state "E") = OK history_probe_backedges_s1
Proof
  EVAL_TAC >> simp[]
QED
Theorem history_probe_irreducible_target_H:
  run_block 1 ctx (EL 1 history_probe_irreducible_target)
    history_probe_backedges_s1 = OK history_probe_irreducible_t2
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED
Theorem history_probe_irreducible_target_I:
  run_block 1 ctx (EL 2 history_probe_irreducible_target)
    history_probe_irreducible_t2 = OK history_probe_irreducible_t3
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def]
QED
Theorem history_probe_irreducible_target_revisit:
  run_block 1 ctx (EL 1 history_probe_irreducible_target)
    history_probe_irreducible_t3 = OK history_probe_irreducible_t4
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def,
    finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem history_probe_irreducible_source_lookups:
  lookup_block (init_venom_state "E").vs_current_bb history_probe_irreducible.fn_blocks =
    SOME (HD history_probe_irreducible.fn_blocks) /\
  lookup_block history_probe_backedges_s1.vs_current_bb history_probe_irreducible.fn_blocks =
    SOME (EL 1 history_probe_irreducible.fn_blocks) /\
  lookup_block history_probe_irreducible_s2.vs_current_bb history_probe_irreducible.fn_blocks =
    SOME (EL 2 history_probe_irreducible.fn_blocks) /\
  lookup_block history_probe_irreducible_s3.vs_current_bb history_probe_irreducible.fn_blocks =
    SOME (EL 1 history_probe_irreducible.fn_blocks)
Proof
  EVAL_TAC
QED
Theorem history_probe_irreducible_target_lookups:
  lookup_block (init_venom_state "E").vs_current_bb history_probe_irreducible_target =
    SOME (HD history_probe_irreducible_target) /\
  lookup_block history_probe_backedges_s1.vs_current_bb history_probe_irreducible_target =
    SOME (EL 1 history_probe_irreducible_target) /\
  lookup_block history_probe_irreducible_t2.vs_current_bb history_probe_irreducible_target =
    SOME (EL 2 history_probe_irreducible_target) /\
  lookup_block history_probe_irreducible_t3.vs_current_bb history_probe_irreducible_target =
    SOME (EL 1 history_probe_irreducible_target)
Proof
  EVAL_TAC
QED
Theorem history_probe_irreducible_walks:
  (history_probe_walk 3 ctx history_probe_irreducible (init_venom_state "E") =
    SOME history_probe_irreducible_s3) /\
  (history_probe_walk 4 ctx history_probe_irreducible (init_venom_state "E") =
    SOME history_probe_irreducible_s4) /\
  (history_probe_walk 3 ctx
      (FST (make_ssa_current_fn history_probe_supply history_probe_irreducible))
      (init_venom_state "E") = SOME history_probe_irreducible_t3) /\
  (history_probe_walk 4 ctx
      (FST (make_ssa_current_fn history_probe_supply history_probe_irreducible))
      (init_venom_state "E") = SOME history_probe_irreducible_t4)
Proof
  simp[history_probe_walk_positive, history_probe_walk_def,
    history_probe_irreducible_target_blocks,
    history_probe_irreducible_source_lookups, history_probe_irreducible_target_lookups,
    history_probe_irreducible_source_E, history_probe_irreducible_source_H,
    history_probe_irreducible_source_I, history_probe_irreducible_source_revisit,
    history_probe_irreducible_target_E, history_probe_irreducible_target_H,
    history_probe_irreducible_target_I, history_probe_irreducible_target_revisit]
QED
Theorem history_probe_irreducible_revisit_agreement:
  (\(s0,s1,t0,t1). IS_SOME s0 /\ IS_SOME s1 /\ s0 = t0 /\ s1 = t1)
    (history_probe_revisits ctx history_probe_irreducible 4)
Proof
  simp[history_probe_revisits_def, history_probe_observe_def,
    history_probe_irreducible_walks] >> EVAL_TAC
QED

(* This finite family checks actual block executions, not all-state
   equivalence, universal exclusion of degenerate merges, or frame_sim. *)
Theorem history_probe_revisit_agreement:
  !fn n. MEM (fn,n) [(history_probe_diamond,4); (history_probe_backedges,4);
       (history_probe_nested,5); (history_probe_irreducible,4); (current_probe_loop,3)] ==>
    (\(s0,s1,t0,t1). IS_SOME s0 /\ IS_SOME s1 /\ s0 = t0 /\ s1 = t1)
      (history_probe_revisits ctx fn n)
Proof
  rpt gen_tac >> pure_rewrite_tac[listTheory.MEM] >> strip_tac >> gvs[] >>
  metis_tac[history_probe_diamond_revisit_agreement,
    history_probe_backedges_revisit_agreement, history_probe_nested_revisit_agreement,
    history_probe_irreducible_revisit_agreement, history_probe_control_revisit_agreement]
QED
