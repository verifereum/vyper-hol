Theory o1LabelFlowMiddleSsaAssembly
Ancestors
  o1LabelFlowMiddleSsa o1LabelFlowMiddleCleanupFlow makeSsaDefs

Theorem make_ssa_current_fn_label_flow:
  wf_function f /\ fn_inst_wf f /\ make_ssa_input_ok f /\
  ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  label_flow_ok (ctx with ctx_functions := [f]) /\
  (!x. code_end_var f x ==> ?d op. MEM d (fn_insts f) /\
    d.inst_opcode = ADD /\ d.inst_operands = [op; Label "code_end"] /\
    d.inst_outputs = [x] /\
    (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
    (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
      MEM (Var x) j.inst_operands ==>
      j.inst_opcode = CODECOPY /\
      (?dst sz. j.inst_operands = [dst; Var x; sz] /\
        dst <> Var x /\ sz <> Var x) /\
      ?a b. bb.bb_instructions = a ++ [d;j] ++ b)) /\
  make_ssa_current_fn s f = (g,t) ==>
  label_flow_ok (ctx with ctx_functions := [g])
Proof
  Cases_on `fn_entry_label f`
  >- (simp[make_ssa_current_fn_def] >> strip_tac >> gvs[]) >>
  simp[make_ssa_current_fn_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  `label_flow_ok (ctx with ctx_functions := [f with fn_blocks := bbs2])` by
    (irule prepared_renaming_label_flow >> goal_assum $ drule_at Any >>
     simp[current_dom_tree_def, current_succ_map_def] >> metis_tac[]) >>
  drule simplify_current_phis_if_label_flow >> simp[]
QED
