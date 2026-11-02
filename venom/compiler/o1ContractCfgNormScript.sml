(*
 * CFG normalization (the supply variant the O1 dispatcher runs) against
 * the O1 pass contract.
 *
 * The pass splits each critical edge p -> t with a fresh block that
 * forwards the PHI values t reads along that edge into fresh variables and
 * jumps to t; t's PHIs then name the split block and the forwarded
 * variables.  A run of the output takes one extra block per split edge
 * and otherwise matches the input's run, so the two correspond with
 * different fuel.  A forwarding ASSIGN reads every PHI value for the edge,
 * duplicates included, where the input's PHI reads only the first; wf_ssa
 * makes each of them defined at the predecessor's end.
 *)
Theory o1ContractCfgNorm
Ancestors
  o1PassLift cfgNormDefs cfgNormSupplyProofs venomFnScheduleRunner venomWf
  venomInst irSupply cfgNormSupplySim contextCodegenRel venomExecSemantics
  venomExecProofs venomStepProps

Theorem supply_first_block_no_preds_iff:
  fn.fn_blocks <> [] ==>
  (first_block_no_preds fn <=>
    ~?a. fn_cfg_edge fn a (HD fn.fn_blocks).bb_label)
Proof
  simp[unitShapeDefsTheory.first_block_no_preds_def, listTheory.EVERY_MEM, fn_cfg_edge_def] >>
  metis_tac[]
QED

Theorem insert_split_supply_first_block_no_preds:
  wf_function fn /\ first_block_no_preds fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  insert_split_supply s fn pred target = (fn',s') ==>
  first_block_no_preds fn'
Proof
  rpt strip_tac >>
  `wf_function fn'` by metis_tac[insert_split_supply_wf_function] >>
  `fn.fn_blocks <> [] /\ fn'.fn_blocks <> []` by
    gvs[wf_function_def, fn_has_entry_def] >>
  `fn_entry_label fn' = fn_entry_label fn` by metis_tac[insert_split_supply_entry] >>
  `(HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label` by
    (Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def]) >>
  gvs[supply_first_block_no_preds_iff] >>
  match_mp_tac (SIMP_RULE bool_ss [] insert_split_supply_no_incoming) >>
  simp[] >>
  Cases_on `fn.fn_blocks` >> gvs[fn_labels_def]
QED

Theorem supply_active_terminator_exec_block:
  st.vs_inst_idx < LENGTH bb.bb_instructions /\
  EL st.vs_inst_idx bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst st = OK sp /\
  ~sp.vs_halted ==>
  exec_block fuel ctx bb st = OK sp
Proof
  rpt strip_tac >>
  simp[Once exec_block_def, get_instruction_def]
QED

Theorem supply_prefix_terminator_entry:
  wf_function f /\ fn_inst_wf f /\ supply_prefix_defined f st /\
  active_inst f inst st /\ is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst st = OK sp /\ ~sp.vs_halted ==>
  supply_entry_defined f sp
Proof
  rpt strip_tac >> gvs[active_inst_def] >>
  `exec_block fuel ctx bb st = OK sp` by
    (irule supply_active_terminator_exec_block >> metis_tac[]) >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `bb_well_formed bb` by gvs[wf_function_def] >>
  gvs[supply_prefix_defined_def, supply_entry_defined_def] >>
  reverse conj_tac
  >- (irule strict_dom_vars_defined_preserved_from_prefix >> simp[] >>
      qexistsl [`bb`, `ctx`, `fuel`, `st`] >> simp[] >> metis_tac[]) >>
  `MEM sp.vs_current_bb (bb_succs bb)` by
    (irule exec_block_current_bb_in_succs >> conj_tac
     >- (gvs[bb_well_formed_def] >> rpt strip_tac >>
         `i < LENGTH bb.bb_instructions` by decide_tac >>
         `i = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >> decide_tac) >>
     `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
     simp[] >> qexistsl [`ctx`, `fuel`, `st`] >> simp[]) >>
  irule fn_reachable_step >> qexists `st.vs_current_bb` >>
  simp[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem supply_prefix_enters_block:
  wf_function f /\ supply_entry_defined f st /\ enters_block f st sp ==>
  supply_prefix_defined f sp
Proof
  rpt strip_tac >> gvs[enters_block_def] >>
  drule lookup_block_MEM >> strip_tac >>
  irule supply_prefix_defined_eval_phis >> metis_tac[lookup_block_label]
QED

Theorem supply_frame_reach_prefix:
  !ctx f s0 inst st. frame_reach ctx f s0 inst st ==>
  active_inst f inst st /\
  (wf_function f /\ fn_inst_wf f /\ fn_entry_state f s0 ==>
   supply_prefix_defined f st)
Proof
  ho_match_mp_tac frame_reach_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> simp[] >> rpt strip_tac >>
      irule supply_prefix_enters_block >>
      metis_tac[supply_entry_defined_entry, fn_entry_state_def])
  >- (rpt gen_tac >> strip_tac >> simp[] >> rpt strip_tac >>
      irule supply_prefix_defined_step >> gvs[active_inst_def] >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >> simp[] >> rpt strip_tac >>
  irule supply_prefix_enters_block >>
  metis_tac[supply_prefix_terminator_entry]
QED

Theorem supply_frame_reach_not_halted:
  !ctx f s0 inst st. frame_reach ctx f s0 inst st ==>
  (~s0.vs_halted ==> ~st.vs_halted)
Proof
  ho_match_mp_tac frame_reach_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[enters_block_def] >>
      metis_tac[eval_phis_preserves_halted])
  >- (rpt strip_tac >> drule step_inst_ok_halted >> gvs[]) >>
  rpt strip_tac >> gvs[enters_block_def] >>
  metis_tac[eval_phis_preserves_halted]
QED

Theorem supply_frame_reach_terminator_entry:
  wf_function f /\ fn_inst_wf f /\ fn_entry_state f s0 /\
  frame_reach ctx f s0 inst st /\ is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst st = OK sp /\ ~sp.vs_halted ==>
  supply_entry_defined f sp
Proof
  metis_tac[supply_frame_reach_prefix, supply_prefix_terminator_entry]
QED

Theorem supply_frame_reach_forward_sources:
  wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ fn_entry_state f s0 /\
  frame_reach ctx f s0 inst st /\ MEM pred f.fn_blocks /\
  MEM target f.fn_blocks /\ pred.bb_label = st.vs_current_bb /\
  active_inst f inst st /\ is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst st = OK sp /\
  MEM v (phi_vars_needing_forward pred.bb_label pred target.bb_instructions) ==>
  v IN FDOM sp.vs_vars
Proof
  rpt strip_tac >>
  `supply_prefix_defined f st` by metis_tac[supply_frame_reach_prefix] >>
  `~sp.vs_halted` by
    metis_tac[supply_frame_reach_not_halted, step_inst_ok_halted,
              fn_entry_state_def] >>
  `exec_block fuel ctx pred st = OK sp` by
    (gvs[active_inst_def] >>
     `bb = pred` by metis_tac[same_label_same_block] >> gvs[] >>
     irule supply_active_terminator_exec_block >> metis_tac[]) >>
  irule phi_forward_sources_exec_block_defined >>
  qexistsl [`ctx`, `f`, `fuel`, `pred`, `st`, `target`] >> simp[]
QED

Theorem cfg_norm_function_supply_fn_bisim:
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  fn_bisim fn fn'
Proof
  cheat
QED

(* A split block's ASSIGNs and JMP touch no memory; every other
   instruction keeps its operands up to the renaming of PHI values. *)
Theorem cfg_norm_function_supply_frame_sim:
  ctx_bisim C C' /\
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  frame_sim C C' fn fn'
Proof
  cheat
QED
