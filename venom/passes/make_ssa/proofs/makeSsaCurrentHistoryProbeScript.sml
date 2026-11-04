(* Bounded real-pass probes; these are not universal exclusion lemmas. *)
Theory makeSsaCurrentHistoryProbe
Ancestors
  makeSsaCurrentDefs makeSsaCurrentSimDefs makeSsaCurrentReinsertionSlots venomWf cfgWf
  unitShapeDefs o1PassContract

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
