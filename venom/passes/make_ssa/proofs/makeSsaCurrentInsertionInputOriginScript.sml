Theory makeSsaCurrentInsertionInputOrigin
Ancestors makeSsaCurrentInsertionDemand makeSsaCurrentDemandOrigin
  makeSsaCurrentExceptionalDemandOrigin makeSsaCurrentExitTokens
  makeSsaCurrentActualAvailable venomWf venomInst venomExecProps list rich_list

Theorem current_actual_insertion_input_nondefault:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\
  first_block_no_preds fn /\ entry_block fn = SOME eb /\
  LRC (fn_cfg_edge fn) route eb.bb_label p /\
  MEM ep events /\ current_event_label ep = p /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block h fn.fn_blocks = SOME hb /\ fn_cfg_edge fn p h /\
  current_actual_inserted fn v h /\
  (!i. i < LENGTH (collect_phis hb.bb_instructions) ==>
    ~MEM v (inst_defs (EL i hb.bb_instructions))) ==>
  !w. current_event_exit_env ep v <> CurrentDefault w
Proof
  strip_tac >>
  `current_demand fn v p (LENGTH pb.bb_instructions)` by
    metis_tac[current_actual_insertion_exit_demand] >>
  Cases_on `?ob phi. MEM ob fn.fn_blocks /\
    MEM phi (collect_phis ob.bb_instructions) /\
    MEM v (MAP SND (phi_pairs phi.inst_operands))`
  >- (`current_event_exit_env ep v =
        current_chain_token fn (current_actual_inserted fn) v (route ++ [p]) (CurrentDefault v)` by
        (irule current_certificate_rooted_exceptional_demand_exit >> metis_tac[]) >>
      `?l bb i. MEM l (route ++ [p]) /\ lookup_block l fn.fn_blocks = SOME bb /\
        MEM i bb.bb_instructions /\ MEM v i.inst_outputs` by
        (irule current_demand_route_definition >> metis_tac[]) >>
      simp[] >> irule current_chain_token_definition_nondefault >> metis_tac[]) >>
  `!b phi. MEM b fn.fn_blocks /\ MEM phi (collect_phis b.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))` by metis_tac[] >>
  `MEM hb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions))` by
    (irule current_actual_insertion_exit_live >> metis_tac[]) >>
  irule current_certificate_rooted_demand_nondefault >> metis_tac[]
QED

Theorem current_actual_insertion_input_defined:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  current_actual_inserted fn v h /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block h fn.fn_blocks = SOME hb /\ fn_cfg_edge fn p h /\
  (!i. i < LENGTH (collect_phis hb.bb_instructions) ==>
    ~MEM v (inst_defs (EL i hb.bb_instructions))) /\
  current_actual_domain_cut fn (CurrentBody fuel pb) before /\
  before.vs_current_bb = p /\
  get_instruction pb before.vs_inst_idx = SOME inst /\ inst_wf inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst before = OK after ==>
  ?value. lookup_var v after = SOME value
Proof
  strip_tac >>
  `current_demand fn v p (LENGTH pb.bb_instructions)` by
    metis_tac[current_actual_insertion_exit_demand] >>
  irule current_actual_exit_demand_defined >> metis_tac[]
QED
