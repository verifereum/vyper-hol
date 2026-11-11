(* Reached GAS sites for the actual current MakeSSA transformation. *)
Theory makeSsaCurrentEvents
Ancestors
  makeSsaCurrentLockstepShape makeSsaCurrentCopyPrefixRuntime
  makeSsaCurrentEntryPrefix makeSsaCurrentProps makeSsaCurrentForwardBase
  makeSsaCurrentForwardRuntime makeSsaCurrentExecRuntime
  makeSsaCurrentReturnRuntime makeSsaCurrentRuntime o1PassLift gasEvents
  o1FrameLockstep o1MakeSsaCfg makeSsaCurrentForwardCut
  makeSsaCurrentDemandRuntime makeSsaCurrentCutInv venomWf venomExecProps
  makeSsaCurrentWfSsa makeSsaCurrentDemand stateFrame
  makeSsaCurrentEdgePrefix makeSsaCurrentSuccessorRelation
  makeSsaCurrentPrefixTransport makeSsaCurrentLockstep
  venomExecSemantics venomInst venomState list rich_list arithmetic

(* Prefix erasure uses successful execution, not just syntactic silence. *)
Theorem current_prefix_steps_gas_events_block[local]:
  !xs st post rest.
  current_prefix_steps fuel C xs st post /\
  EVERY (\inst. inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE) xs /\
  DROP st.vs_inst_idx bb.bb_instructions = xs ++ rest ==>
  gas_events_block fuel C owner bb st =
  gas_events_block fuel C owner bb post
Proof
  Induct >> simp[current_prefix_steps_def] >> rpt strip_tac >>
  `st.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _`
      (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[LENGTH_DROP] >> decide_tac) >>
  `get_instruction bb st.vs_inst_idx = SOME h` by
    (simp[get_instruction_def] >>
     qpat_x_assum `DROP _ _ = _`
       (mp_tac o Q.AP_TERM `HD`) >> simp[HD_DROP]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [gas_events_block_def])) >>
  simp[gas_events_step_def] >>
  first_x_assum irule >> simp[] >> qexists_tac `rest` >>
  qpat_x_assum `DROP _ _ = _`
    (mp_tac o Q.AP_TERM `DROP 1`) >>
  simp[DROP_DROP_T, ADD1, ADD_COMM]
QED

(* The existing generic lookup transport also covers absent callees. *)
Theorem current_events_lookup_functions:
  LIST_REL (\fn fn'. ?t t'.
    ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
    make_ssa_current_fn t fn = (fn',t')) fs gs ==>
  OPTREL (\fn fn'. ?t t'.
    ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
    make_ssa_current_fn t fn = (fn',t'))
    (lookup_function name fs) (lookup_function name gs)
Proof
  strip_tac >> irule list_rel_lookup_function >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  metis_tac[make_ssa_current_fn_metadata, fn_identity_metadata_eq_def]
QED

(* Readiness supplies totality; failed ASSIGN prefixes cannot be erased. *)
Theorem current_ready_prefix_gas_events_block[local]:
  current_copy_prefix_ready D xs /\
  (!x. x IN D ==> IS_SOME (lookup_var x st)) /\
  DROP st.vs_inst_idx bb.bb_instructions = xs ++ rest ==>
  ?post. current_prefix_steps fuel C xs st post /\
    gas_events_block fuel C owner bb st =
      gas_events_block fuel C owner bb post /\
    post.vs_inst_idx = st.vs_inst_idx + LENGTH xs /\
    execution_frame post = execution_frame st /\
    post.vs_current_bb = st.vs_current_bb /\
    post.vs_prev_bb = st.vs_prev_bb
Proof
  strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE) xs` by
    (qpat_x_assum `current_copy_prefix_ready _ _` mp_tac >>
     map_every qid_spec_tac [`D`, `xs`] >> Induct >>
     simp[current_copy_prefix_ready_def] >> rpt strip_tac >> gvs[] >>
     metis_tac[]) >>
  drule_all current_copy_prefix_total >>
  disch_then (qspecl_then [`fuel`, `C`] strip_assume_tac) >>
  qexists_tac `post` >> asm_rewrite_tac[] >> conj_tac
  >- (irule current_prefix_steps_gas_events_block >> metis_tac[]) >>
  metis_tac[current_prefix_steps_index]
QED

Theorem current_events_decode_none[local]:
  inst_pair sg inst inst' ==>
  (decode_invoke inst = NONE <=> decode_invoke inst' = NONE)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >>
  gvs[inst_pair_def] >- simp[decode_invoke_def] >>
  rename1 `op_rename sg h h'` >>
  Cases_on `h` >> Cases_on `h'` >>
  gvs[op_rename_def, decode_invoke_def]
QED

Theorem current_events_setup_callee[local]:
  make_ssa_current_fn s fn = (fn',s') /\ state_rel sg st st' ==>
  setup_callee fn' args st' = setup_callee fn args st
Proof
  strip_tac >> irule setup_callee_execution_frame >>
  gvs[state_rel_def] >> metis_tac[make_ssa_current_fn_entry_label]
QED

Theorem current_events_noninvoke_error[local]:
  inst_wf inst /\ inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 ==>
  ((?e. step_inst fuel C inst st = Error e) <=>
   (?e. step_inst fuel C' inst' st' = Error e))
Proof
  strip_tac >>
  Cases_on `step_inst fuel C inst st` >>
  Cases_on `step_inst fuel C' inst' st'` >> simp[]
  >- (drule_all current_exec_step_noninvoke_ok_pair_forward >>
      disch_then (qspec_then `C'` mp_tac) >> simp[])
  >- (drule_all current_exec_step_noninvoke_halt_pair_forward >>
      disch_then (qspec_then `C'` mp_tac) >> simp[])
  >- (drule_all current_exec_step_noninvoke_abort_pair_forward >>
      disch_then (qspec_then `C'` mp_tac) >> simp[])
  >- (drule_all current_exec_step_noninvoke_intret_pair_forward >>
      disch_then (qspec_then `C'` mp_tac) >> simp[])
  >- (drule_all current_exec_step_noninvoke_ok_pair >>
      disch_then (qspec_then `C` mp_tac) >> simp[])
  >- (drule_all current_exec_step_noninvoke_halt_pair >>
      disch_then (qspec_then `C` mp_tac) >> simp[])
  >- (drule_all current_exec_step_noninvoke_abort_pair >>
      disch_then (qspec_then `C` mp_tac) >> simp[]) >>
  drule_all current_exec_step_noninvoke_intret_pair >>
  disch_then (qspec_then `C` mp_tac) >> simp[]
QED

(* The fuel induction supplies this premise for initialized callees only. *)
Theorem current_events_invoke_step[local]:
  LIST_REL (\fn fn'. ?t t'. ir_supply_covers_fn t fn /\
    ir_supply_inst_ok t /\ make_ssa_current_fn t fn = (fn',t'))
    C.ctx_functions C'.ctx_functions /\
  (!fn fn' cs. MEM fn C.ctx_functions /\ (?t t'. ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
      make_ssa_current_fn t fn = (fn',t')) /\ fn_entry_state fn cs ==>
    gas_events_blocks fuel C fn cs = gas_events_blocks fuel C' fn' cs) /\
  inst.inst_opcode = INVOKE /\ inst_pair sg inst inst' /\
  state_rel sg st st' ==>
  gas_events_step fuel C owner inst st =
    gas_events_step fuel C' owner inst' st'
Proof
  strip_tac >>
  `inst'.inst_opcode = INVOKE` by gvs[inst_pair_def] >>
  Cases_on `decode_invoke inst`
  >- (drule current_events_decode_none >> simp[gas_events_step_def]) >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  drule_all current_invoke_decode_args_pair >> strip_tac >>
  drule current_events_lookup_functions >>
  disch_then (qspec_then `pair0` mp_tac) >>
  Cases_on `lookup_function pair0 C.ctx_functions` >>
  Cases_on `lookup_function pair0 C'.ctx_functions` >>
  simp[optionTheory.OPTREL_def]
  >- simp[gas_events_step_def] >> strip_tac >>
  simp[gas_events_step_def] >>
  Cases_on `eval_operands pair1 st` >> simp[] >>
  rename1 `eval_operands pair1 st = SOME args` >>
  `setup_callee x' args st' = setup_callee x args st` by
    (irule current_events_setup_callee >> metis_tac[]) >>
  simp[] >> Cases_on `setup_callee x args st` >> simp[] >>
  first_x_assum irule >>
  metis_tac[setup_callee_fn_entry_state, venomInstTheory.lookup_function_MEM]
QED

Theorem current_events_invoke_result[local]:
  LIST_REL (\fn fn'. ?t t'. ir_supply_covers_fn t fn /\
    ir_supply_inst_ok t /\ make_ssa_current_fn t fn = (fn',t'))
    C.ctx_functions C'.ctx_functions /\
  (!fn fn' cs. MEM fn C.ctx_functions /\ (?t t'. ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
      make_ssa_current_fn t fn = (fn',t')) /\ fn_entry_state fn cs ==>
    case run_blocks fuel C fn cs of
      Error e => ?e'. run_blocks fuel C' fn' cs = Error e'
    | r => frame_result_rel r (run_blocks fuel C' fn' cs)) /\
  inst.inst_opcode = INVOKE /\ inst_pair sg inst inst' /\
  state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 ==>
  case step_inst fuel C inst st of
    OK t => ?t'. step_inst fuel C' inst' st' = OK t' /\ state_rel sg1 t t'
  | Error e => ?e'. step_inst fuel C' inst' st' = Error e'
  | r => frame_result_rel r (step_inst fuel C' inst' st')
Proof
  strip_tac >>
  `inst'.inst_opcode = INVOKE` by gvs[inst_pair_def] >>
  Cases_on `decode_invoke inst`
  >- (drule current_events_decode_none >> simp[] >>
      strip_tac >> simp[step_inst_def]) >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  drule_all current_invoke_decode_args_pair >> strip_tac >>
  drule current_events_lookup_functions >>
  disch_then (qspec_then `pair0` mp_tac) >>
  Cases_on `lookup_function pair0 C.ctx_functions` >>
  Cases_on `lookup_function pair0 C'.ctx_functions` >>
  simp[optionTheory.OPTREL_def]
  >- simp[step_inst_def] >> strip_tac >>
  simp[step_inst_def] >>
  Cases_on `eval_operands pair1 st` >> simp[] >>
  rename1 `eval_operands pair1 st = SOME args` >>
  `setup_callee x' args st' = setup_callee x args st` by
    (irule current_events_setup_callee >> metis_tac[]) >>
  simp[] >> Cases_on `setup_callee x args st` >> simp[] >>
  rename1 `setup_callee x args st = SOME cs` >>
  `fn_entry_state x cs` by metis_tac[setup_callee_fn_entry_state] >>
  first_x_assum (qspecl_then [`x`, `x'`, `cs`] mp_tac) >>
  (impl_tac >- metis_tac[venomInstTheory.lookup_function_MEM]) >>
  Cases_on `run_blocks fuel C x cs` >>
  Cases_on `run_blocks fuel C' x' cs` >>
  simp[frame_result_rel_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `bind_outputs inst.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state st v))`
  >- (Cases_on `bind_outputs inst'.inst_outputs i.iret_values
        (adopt_return_fmp i (merge_callee_state st' v'))` >> simp[] >>
      gvs[bind_outputs_def, current_last_output_slots_def]) >>
  `state_rel sg (adopt_return_fmp i (merge_callee_state st v))
    (adopt_return_fmp i (merge_callee_state st' v'))` by
    (irule current_return_merge_state_rel >> gvs[]) >>
  drule_all current_runtime_bind_last_slots_forward >> strip_tac >> simp[]
QED

Theorem current_events_noninvoke_result[local]:
  inst_wf inst /\ inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 ==>
  case step_inst fuel C inst st of
    OK t => ?t'. step_inst fuel C' inst' st' = OK t' /\ state_rel sg1 t t'
  | Error e => ?e'. step_inst fuel C' inst' st' = Error e'
  | r => frame_result_rel r (step_inst fuel C' inst' st')
Proof
  strip_tac >> Cases_on `step_inst fuel C inst st` >> simp[]
  >- (drule_all current_exec_step_noninvoke_ok_pair_forward >>
      disch_then (qspec_then `C'` strip_assume_tac) >> metis_tac[])
  >- (drule_all current_exec_step_noninvoke_halt_pair_forward >>
      disch_then (qspec_then `C'` strip_assume_tac) >> gvs[frame_result_rel_def])
  >- (drule_all current_exec_step_noninvoke_abort_pair_forward >>
      disch_then (qspec_then `C'` strip_assume_tac) >> gvs[frame_result_rel_def])
  >- (drule_all current_exec_step_noninvoke_intret_pair_forward >>
      disch_then (qspec_then `C'` strip_assume_tac) >> gvs[frame_result_rel_def]) >>
  drule_all current_events_noninvoke_error >>
  disch_then (qspecl_then [`fuel`, `C'`, `C`] mp_tac) >> simp[]
QED

Theorem current_events_cut_result[local]:
  LIST_REL (\fn fn'. ?t t'. ir_supply_covers_fn t fn /\
    ir_supply_inst_ok t /\ make_ssa_current_fn t fn = (fn',t'))
    C.ctx_functions C'.ctx_functions /\
  (!fn fn' cs. MEM fn C.ctx_functions /\ (?t t'. ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
      make_ssa_current_fn t fn = (fn',t')) /\ fn_entry_state fn cs ==>
    case run_blocks fuel C fn cs of
      Error e => ?e'. run_blocks fuel C' fn' cs = Error e'
    | r => frame_result_rel r (run_blocks fuel C' fn' cs)) /\
  fn_inst_wf fn /\ lookup_block l fn.fn_blocks = SOME old /\
  i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode <> PHI /\
  inst_pair (current_cut_sg fn A renamed H events l i)
    (EL i old.bb_instructions) inst' /\
  current_last_output_slots (current_cut_sg fn A renamed H events l i)
    (EL i old.bb_instructions).inst_outputs inst'.inst_outputs
    (current_cut_sg fn A renamed H events l (SUC i)) /\
  current_cut_inv fn A renamed H events l i st st' ==>
  case step_inst fuel C (EL i old.bb_instructions) st of
    OK t => ?t'. step_inst fuel C' inst' st' = OK t' /\
      current_cut_inv fn A renamed H events l (SUC i) t t'
  | Error e => ?e'. step_inst fuel C' inst' st' = Error e'
  | r => frame_result_rel r (step_inst fuel C' inst' st')
Proof
  strip_tac >>
  `state_rel (current_cut_sg fn A renamed H events l i) st st' /\
   (!v. current_demand fn v l i ==> IS_SOME (lookup_var v st))` by
    gvs[current_cut_inv_def] >>
  `inst_wf (EL i old.bb_instructions)` by
    metis_tac[fn_inst_wf_def, lookup_block_MEM, EL_MEM] >>
  `case step_inst fuel C (EL i old.bb_instructions) st of
     OK t => ?t'. step_inst fuel C' inst' st' = OK t' /\
       state_rel (current_cut_sg fn A renamed H events l (SUC i)) t t'
   | Error e => ?e'. step_inst fuel C' inst' st' = Error e'
   | r => frame_result_rel r (step_inst fuel C' inst' st')` by
    (Cases_on `(EL i old.bb_instructions).inst_opcode = INVOKE`
     >- (irule current_events_invoke_result >> metis_tac[]) >>
     irule current_events_noninvoke_result >> metis_tac[]) >>
  Cases_on `step_inst fuel C (EL i old.bb_instructions) st` >> gvs[] >>
  simp[current_cut_inv_def] >>
  metis_tac[current_demand_step_defined]
QED

Theorem current_events_block_suffix[local]:
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l fn'.fn_blocks = SOME bb' /\
  A l = current_block_annotations old pre /\
  LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
  (!j. LENGTH (collect_phis old.bb_instructions) <= j /\
       j < LENGTH old.bb_instructions ==>
       (EL (LENGTH pre + j) bb'.bb_instructions).inst_id =
         (EL j old.bb_instructions).inst_id) /\
  LIST_REL (\fn fn'. ?t t'. ir_supply_covers_fn t fn /\
    ir_supply_inst_ok t /\ make_ssa_current_fn t fn = (fn',t'))
    C.ctx_functions C'.ctx_functions /\
  (!f f' cs. MEM f C.ctx_functions /\ (?t t'. ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
      make_ssa_current_fn t f = (f',t')) /\ fn_entry_state f cs ==>
    gas_events_blocks fuel C f cs = gas_events_blocks fuel C' f' cs /\
    (case run_blocks fuel C f cs of
      Error e => ?e'. run_blocks fuel C' f' cs = Error e'
    | r => frame_result_rel r (run_blocks fuel C' f' cs))) /\
  LENGTH (collect_phis old.bb_instructions) <= i /\
  i <= LENGTH old.bb_instructions /\
  st.vs_current_bb = l /\ st.vs_inst_idx = i /\
  st'.vs_inst_idx = LENGTH pre + i /\
  current_cut_inv fn A renamed H events l i st st' ==>
  gas_events_block fuel C owner old st = gas_events_block fuel C' owner bb' st' /\
  (case exec_block fuel C old st of
    OK t => ?t'. exec_block fuel C' bb' st' = OK t' /\
      current_cut_inv fn A renamed H events l (LENGTH old.bb_instructions) t t'
  | Error e => ?e'. exec_block fuel C' bb' st' = Error e'
  | r => frame_result_rel r (exec_block fuel C' bb' st'))
Proof
  map_every qid_spec_tac [`st'`, `st`] >>
  measureInduct_on `LENGTH old.bb_instructions - i` >> rpt gen_tac >> strip_tac >>
  Cases_on `i = LENGTH old.bb_instructions`
  >- (once_rewrite_tac[gas_events_block_def, cj 2 run_defs] >>
      simp[get_instruction_def]) >>
  `i < LENGTH old.bb_instructions` by decide_tac >>
  `inst_wf (EL i old.bb_instructions)` by
    metis_tac[current_wf_phi_context_def, fn_inst_wf_def, lookup_block_MEM, EL_MEM] >>
  drule_all current_cut_inv_ordinary_step_forward >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `bb'' = bb'` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `bb'' = bb'` SUBST_ALL_TAC >>
  qpat_x_assum `!fuel. _` kall_tac >>
  drule_all current_cut_final_last_output_slots >> strip_tac >>
  `bb = bb'` by gvs[] >> qpat_x_assum `bb = bb'` SUBST_ALL_TAC >>
  `fn_inst_wf fn /\ bb_well_formed old` by
    metis_tac[current_wf_phi_context_def, wf_function_def, lookup_block_MEM] >>
  `(EL i old.bb_instructions).inst_opcode <> PHI` by
    (qpat_x_assum `!y. LENGTH old.bb_instructions - y < _ ==> _` kall_tac >>
     qpat_x_assum `bb_well_formed old` mp_tac >>
     simp_tac bool_ss [bb_well_formed_def] >> strip_tac >>
     metis_tac[current_phi_index_before_prefix, arithmeticTheory.NOT_LESS]) >>
  `state_rel (current_cut_sg fn A renamed H events l i) st st'` by
    fs[current_cut_inv_def] >>
  `gas_events_step fuel C owner (EL i old.bb_instructions) st =
   gas_events_step fuel C' owner (EL (LENGTH pre + i) bb'.bb_instructions) st'` by
    (Cases_on `(EL i old.bb_instructions).inst_opcode = INVOKE`
     >- (irule current_events_invoke_step >> metis_tac[]) >>
     `(EL (LENGTH pre + i) bb'.bb_instructions).inst_opcode =
       (EL i old.bb_instructions).inst_opcode` by fs[inst_pair_def] >>
     simp[gas_events_step_def]) >>
  `!f f' cs. MEM f C.ctx_functions /\ (?t t'. ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
      make_ssa_current_fn t f = (f',t')) /\ fn_entry_state f cs ==>
    case run_blocks fuel C f cs of
      Error e => ?e'. run_blocks fuel C' f' cs = Error e'
    | r => frame_result_rel r (run_blocks fuel C' f' cs)` by metis_tac[] >>
  drule_all current_events_cut_result >>
  disch_then (mk_asm "step") >>
  `(EL (LENGTH pre + i) bb'.bb_instructions).inst_opcode =
    (EL i old.bb_instructions).inst_opcode` by fs[inst_pair_def] >>
  `LENGTH pre + i < LENGTH bb'.bb_instructions` by simp[] >>
  once_rewrite_tac[gas_events_block_def, cj 2 run_defs] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel C (EL i old.bb_instructions) st` >>
  asm_x "step" mp_tac >> simp[]
  >- suspend "ok" >>
  qpat_x_assum `!y. LENGTH old.bb_instructions - y < _ ==> _` kall_tac >> strip_tac >>
  Cases_on `step_inst fuel C' (EL (LENGTH pre + i) bb'.bb_instructions) st'` >>
  gvs[frame_result_rel_def]
QED

Resume current_events_block_suffix[ok]:
  strip_tac >>
  rename1 `step_inst fuel C (EL i old.bb_instructions) st = OK t` >>
  `state_rel (current_cut_sg fn A renamed H events l (SUC i)) t t'` by
    fs[current_cut_inv_def] >>
  `execution_frame t' = execution_frame t` by metis_tac[state_rel_def] >>
  `t'.vs_halted = t.vs_halted` by
    (qpat_x_assum `execution_frame _ = _` mp_tac >>
     simp[execution_frame_def]) >>
  simp[arithmeticTheory.ADD_COMM] >>
  Cases_on `is_terminator (EL i old.bb_instructions).inst_opcode`
  >- (`SUC i = LENGTH old.bb_instructions` by
        (qpat_x_assum `bb_well_formed old` mp_tac >>
         simp_tac bool_ss [bb_well_formed_def] >> strip_tac >>
         simp[arithmeticTheory.SUC_PRE]) >>
      Cases_on `t.vs_halted` >> simp[frame_result_rel_def] >>
      gvs[]) >>
  `t.vs_current_bb = l` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
  simp[] >>
  qpat_x_assum `!y. LENGTH old.bb_instructions - y < _ ==> _`
    (qspec_then `SUC i` mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`t with vs_inst_idx := SUC i`,
    `t' with vs_inst_idx := SUC (i + LENGTH pre)`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM] >> gvs[]
QED
Finalise current_events_block_suffix

(* The actual replay, unlike inst_pair alone, retains ordinary GAS IDs. *)
Theorem current_events_ordinary_ids[local]:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l fn'.fn_blocks = SOME bb' /\
  LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old.bb_instructions ==>
  !j. LENGTH (collect_phis old.bb_instructions) <= j /\
      j < LENGTH old.bb_instructions ==>
      (EL (LENGTH pre + j) bb'.bb_instructions).inst_id =
        (EL j old.bb_instructions).inst_id
Proof
  strip_tac >> drule_all make_ssa_current_fn_block_shape >> strip_tac >>
  `bb'' = bb'` by gvs[] >> qpat_x_assum `bb'' = bb'` SUBST_ALL_TAC >>
  `LENGTH bb'.bb_instructions - LENGTH old.bb_instructions = LENGTH pre` by
    decide_tac >>
  gvs[makeSsaCurrentPrefixSuffixOwnerTheory.current_prefix_collect_length]
QED

(* A completed target block provides total PHI/copy preparation at its edge.
   Source entry existence is obtained from the cut interface, not termination. *)
Theorem current_events_successor_prepared[local]:
  make_ssa_current_fn s fn = (fn',s') /\
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  entry_block fn = SOME eb /\ wf_function fn' /\ wf_ssa fn' /\ fn_inst_wf fn' /\
  fn_cfg_edge fn p h /\ lookup_block p fn.fn_blocks = SOME old_p /\
  current_cut_inv fn A renamed H events p (LENGTH old_p.bb_instructions) t t' /\
  t.vs_prev_bb = SOME p /\ t.vs_current_bb = h /\
  lookup_block p fn'.fn_blocks = SOME pred /\ pred.bb_label = before.vs_current_bb /\
  strict_dom_vars_defined fn' before /\ fn_reachable fn' before.vs_current_bb /\
  before.vs_inst_idx <= LENGTH pred.bb_instructions /\
  (!j x. j < before.vs_inst_idx /\ j < LENGTH pred.bb_instructions /\
    MEM x (EL j pred.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x before)) /\
  exec_block fuel C' pred before = OK t' ==>
  ?old bb' pre post post' done.
    lookup_block h fn.fn_blocks = SOME old /\
    lookup_block h fn'.fn_blocks = SOME bb' /\
    A h = current_block_annotations old pre /\
    LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
    enters_block fn t post /\ enters_block fn' t' post' /\
    post.vs_inst_idx = LENGTH (collect_phis old.bb_instructions) /\
    current_prefix_steps (PRE fuel) C'
      (TAKE (LENGTH pre + LENGTH (collect_phis old.bb_instructions) -
        phi_prefix_length bb'.bb_instructions)
        (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions)) post' done /\
    done.vs_inst_idx = LENGTH pre + LENGTH (collect_phis old.bb_instructions) /\
    current_cut_inv fn A renamed H events h
      (LENGTH (collect_phis old.bb_instructions)) post done /\
    strict_dom_vars_defined fn' done /\ fn_reachable fn' h /\
    done.vs_inst_idx <= LENGTH bb'.bb_instructions /\
    (!j x. j < done.vs_inst_idx /\ j < LENGTH bb'.bb_instructions /\
      MEM x (EL j bb'.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x done))
Proof
  strip_tac >> drule_all current_cut_inv_block_entry_prefix >> strip_tac >>
  `t'.vs_current_bb = h` by fs[current_cut_inv_def, state_rel_def] >>
  `all_reachable fn'` by
    (irule makeSsaCurrentCfgTheory.make_ssa_current_fn_all_reachable >>
     qexistsl [`fn`, `s`, `s'`] >>
     fs[current_wf_phi_context_def, wf_function_def]) >>
  `fn_reachable fn' h` by
    (fs[cfgWfTheory.all_reachable_def] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `MEM pred fn'.fn_blocks /\ MEM bb' fn'.fn_blocks` by
    metis_tac[lookup_block_MEM] >>
  `EVERY inst_wf pred.bb_instructions /\ EVERY inst_wf bb'.bb_instructions` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `?new. lookup_block h renamed = SOME new /\
    bb' = if blocks_have_leading_phi fn.fn_blocks
      then simplify_current_phi_block new else new` by
    (qpat_x_assum `lookup_block h fn'.fn_blocks = _` mp_tac >>
     qpat_assum `fn' = _` SUBST1_TAC >>
     simp[makeSsaCurrentCleanupShapeTheory.current_cleanup_if_lookup] >>
     Cases_on `lookup_block h renamed` >> simp[] >> metis_tac[]) >>
  `phi_prefix_length new.bb_instructions = LENGTH pre +
    LENGTH (collect_phis old_h.bb_instructions)` by
    (drule_all makeSsaCurrentPrefixSuffixOwnerTheory.current_prefix_actual_endpoint >> simp[]) >>
  `lookup_block t'.vs_current_bb fn'.fn_blocks = SOME bb'` by metis_tac[] >>
  qabbrev_tac `copies = TAKE
    (phi_prefix_length new.bb_instructions - phi_prefix_length bb'.bb_instructions)
    (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions)` >>
  `?ph done. eval_phis t' bb'.bb_instructions = OK ph /\
    current_prefix_steps (PRE fuel) C' copies
      (ph with vs_inst_idx := phi_prefix_length bb'.bb_instructions) done /\
    done.vs_inst_idx = phi_prefix_length new.bb_instructions /\
    strict_dom_vars_defined fn' done /\
    done.vs_inst_idx <= LENGTH bb'.bb_instructions /\
    (!j x. j < done.vs_inst_idx /\ j < LENGTH bb'.bb_instructions /\
      MEM x (EL j bb'.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x done))` by
    (Cases_on `blocks_have_leading_phi fn.fn_blocks`
     >- suspend "cleaned" >> suspend "plain") >>
  `enters_block fn' t' (ph with vs_inst_idx := phi_prefix_length bb'.bb_instructions)` by
    (simp[contextCodegenRelTheory.enters_block_def] >> metis_tac[]) >>
  qpat_x_assum `!post'. enters_block _ _ post' ==> _` drule >> strip_tac >>
  drule_all current_cut_successor_prefix_relation >> strip_tac >>
  `old_h' = old_h /\ bb'' = bb'` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `old_h' = old_h` SUBST_ALL_TAC >>
  qpat_x_assum `bb'' = bb'` SUBST_ALL_TAC >>
  `LENGTH pre' = LENGTH pre` by decide_tac >>
  `current_prefix_steps (PRE fuel) C'
    (TAKE (LENGTH pre' + LENGTH (collect_phis old_h.bb_instructions) -
      phi_prefix_length bb'.bb_instructions)
      (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions))
    (ph with vs_inst_idx := phi_prefix_length bb'.bb_instructions) done` by
    (qpat_x_assum `current_prefix_steps (PRE fuel) _ _ _ _` mp_tac >>
     simp[Abbr `copies`]) >>
  qpat_x_assum `!post post' done fuel C. _` (drule_all_then strip_assume_tac) >>
  qexistsl [`old_h`, `bb'`, `pre'`, `post`,
    `ph with vs_inst_idx := phi_prefix_length bb'.bb_instructions`, `done`] >>
  asm_rewrite_tac[]
QED

Resume current_events_successor_prepared[cleaned]:
  `bb' = simplify_current_phi_block new` by asm_rewrite_tac[] >>
  `fn' = fn with fn_blocks := simplify_current_phis_if T renamed` by asm_rewrite_tac[] >>
  `copies = TAKE (phi_prefix_length new.bb_instructions - phi_prefix_length bb'.bb_instructions)
    (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions)` by
    simp[Abbr `copies`] >>
  drule_all current_completed_edge_cleaned_prefix_total >> strip_tac >>
  `!j. j < LENGTH copies ==> (EL j copies).inst_opcode = ASSIGN \/
      (EL j copies).inst_opcode = NOP` by
    (rpt strip_tac >>
     `j < phi_prefix_length new.bb_instructions - phi_prefix_length bb'.bb_instructions /\
      j < LENGTH (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions)` by
       (qpat_x_assum `j < LENGTH copies` mp_tac >>
        simp[NoAsms, Abbr `copies`, LENGTH_TAKE_EQ, LENGTH_DROP, MIN_DEF] >>
        rpt strip_tac >> decide_tac) >>
     `EL j copies = EL (phi_prefix_length bb'.bb_instructions + j) bb'.bb_instructions` by
       (qpat_assum `j < _ - _` mp_tac >>
        qpat_assum `j < LENGTH (DROP _ _)` mp_tac >>
        simp[NoAsms, Abbr `copies`, EL_TAKE, EL_DROP, ADD_COMM]) >>
     pop_assum SUBST1_TAC >>
     `phi_prefix_length bb'.bb_instructions <= phi_prefix_length bb'.bb_instructions + j /\
      phi_prefix_length bb'.bb_instructions + j < phi_prefix_length new.bb_instructions` by
       decide_tac >>
     metis_tac[simplify_current_phi_block_layout]) >>
  metis_tac[current_copy_prefix_steps_transport]
QED

Resume current_events_successor_prepared[plain]:
  `bb' = new` by metis_tac[] >>
  drule_all current_completed_edge_plain_prefix_total >> strip_tac >>
  `copies = []` by simp[Abbr `copies`] >>
  qexistsl [`post`, `post with vs_inst_idx := phi_prefix_length bb'.bb_instructions`] >>
  asm_rewrite_tac[current_prefix_steps_def] >> gvs[IgnAsm `fn' = _`] >> gvs[]
QED
Finalise current_events_successor_prepared

(* Prepared states precede initialized entries at each block-fuel level. *)
Theorem current_events_fuel[local]:
  LIST_REL (\fn fn'. ?s s'. ir_supply_covers_fn s fn /\
    ir_supply_inst_ok s /\ make_ssa_current_fn s fn = (fn',s'))
    C.ctx_functions C'.ctx_functions /\
  EVERY (\fn. make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
    first_block_no_preds fn /\ first_block_no_phi fn) C.ctx_functions ==>
  !fuel.
  (!fn fn' s s' renamed A H events eb raw raw' post post' done l old bb' pre copies.
    MEM fn C.ctx_functions /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
    make_ssa_current_fn s fn = (fn',s') /\
    current_wf_phi_context s fn renamed s' A H events /\
    fn' = fn with fn_blocks :=
      simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    entry_block fn = SOME eb /\ wf_function fn' /\ wf_ssa fn' /\ fn_inst_wf fn' /\
    lookup_block l fn.fn_blocks = SOME old /\ lookup_block l fn'.fn_blocks = SOME bb' /\
    A l = current_block_annotations old pre /\
    LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
    raw.vs_current_bb = l /\ raw'.vs_current_bb = l /\
    enters_block fn raw post /\ enters_block fn' raw' post' /\
    post.vs_inst_idx = LENGTH (collect_phis old.bb_instructions) /\
    copies = TAKE (LENGTH pre + LENGTH (collect_phis old.bb_instructions) -
      phi_prefix_length bb'.bb_instructions)
      (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions) /\
    current_prefix_steps (PRE fuel) C' copies post' done /\
    done.vs_inst_idx = LENGTH pre + LENGTH (collect_phis old.bb_instructions) /\
    current_cut_inv fn A renamed H events l
      (LENGTH (collect_phis old.bb_instructions)) post done /\
    strict_dom_vars_defined fn' done /\ fn_reachable fn' l /\
    done.vs_inst_idx <= LENGTH bb'.bb_instructions /\
    (!j x. j < done.vs_inst_idx /\ j < LENGTH bb'.bb_instructions /\
      MEM x (EL j bb'.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x done)) ==>
    gas_events_blocks fuel C fn raw = gas_events_blocks fuel C' fn' raw' /\
    (case run_blocks fuel C fn raw of
      Error e => ?e'. run_blocks fuel C' fn' raw' = Error e'
    | r => frame_result_rel r (run_blocks fuel C' fn' raw'))) /\
  (!fn fn' st. MEM fn C.ctx_functions /\
    (?s s'. ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
      make_ssa_current_fn s fn = (fn',s')) /\ fn_entry_state fn st ==>
    gas_events_blocks fuel C fn st = gas_events_blocks fuel C' fn' st /\
    (case run_blocks fuel C fn st of
      Error e => ?e'. run_blocks fuel C' fn' st = Error e'
    | r => frame_result_rel r (run_blocks fuel C' fn' st)))
Proof
  strip_tac >> Induct
  >- simp[gas_events_blocks_def, run_blocks_def] >>
  conj_asm1_tac
  >- suspend "prepared" >>
  suspend "entry"
QED

Resume current_events_fuel[prepared]:
  qpat_x_assum `_ /\ _` (CONJUNCTS_THEN2 (mk_asm "prepared_ih") assume_tac) >>
  rpt gen_tac >> strip_tac >>
  `make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
    first_block_no_preds fn /\ first_block_no_phi fn` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `run_block fuel C old raw = exec_block fuel C old post` by
    (irule simplifyCfgBypassRootedEntryTheory.scfg_enters_block_run_block >> qexists `fn` >> simp[]) >>
  `run_block fuel C' bb' raw' = exec_block fuel C' bb' post'` by
    (irule simplifyCfgBypassRootedEntryTheory.scfg_enters_block_run_block >> qexists `fn'` >>
     conj_tac >- metis_tac[] >> asm_rewrite_tac[]) >>
  `post.vs_current_bb = l` by
    (qpat_x_assum `enters_block fn raw post` mp_tac >>
     simp[contextCodegenRelTheory.enters_block_def] >> rpt strip_tac >>
     drule venomExecProofsTheory.eval_phis_preserves_current_bb >> simp[]) >>
  `post'.vs_inst_idx = phi_prefix_length bb'.bb_instructions` by
    (qpat_x_assum `enters_block fn' raw' post'` mp_tac >>
     simp[contextCodegenRelTheory.enters_block_def, IgnAsm `fn' = _`] >>
     rpt strip_tac >> gvs[IgnAsm `fn' = _`] >> metis_tac[]) >>
  `exec_block fuel C' bb' post' = exec_block fuel C' bb' done` by
    (irule current_prefix_steps_exec_block >>
     qexists `DROP (LENGTH pre + LENGTH (collect_phis old.bb_instructions) -
       phi_prefix_length bb'.bb_instructions)
       (DROP post'.vs_inst_idx bb'.bb_instructions)` >>
     qexists `copies` >> conj_tac >- simp[TAKE_DROP] >> fs[]) >>
  `!j. LENGTH (collect_phis old.bb_instructions) <= j /\
      j < LENGTH old.bb_instructions ==>
      (EL (LENGTH pre + j) bb'.bb_instructions).inst_id =
        (EL j old.bb_instructions).inst_id` by
    (metis_tac[current_events_ordinary_ids]) >>
  `LENGTH (collect_phis old.bb_instructions) <= LENGTH old.bb_instructions` by
    simp[makeSsaCurrentDemandDominanceTheory.current_collect_phis_length] >>
  `LENGTH (collect_phis old.bb_instructions) <= LENGTH (collect_phis old.bb_instructions)` by simp[] >>
  drule_all current_events_block_suffix >>
  disch_then (qspec_then `fn.fn_name`
    (CONJUNCTS_THEN2 assume_tac (mk_asm "block_result"))) >>
  `fn'.fn_name = fn.fn_name` by
    metis_tac[make_ssa_current_fn_metadata, fn_identity_metadata_eq_def] >>
  `gas_events_block fuel C' fn.fn_name bb' post' =
    gas_events_block fuel C' fn.fn_name bb' done` by
    (irule current_prefix_steps_gas_events_block >>
     qexistsl [`DROP (LENGTH copies) (DROP post'.vs_inst_idx bb'.bb_instructions)`, `copies`] >>
     conj_tac >- fs[TAKE_DROP, IgnAsm `fn' = _`] >>
     reverse conj_tac >- fs[IgnAsm `fn' = _`] >>
     suspend "silent") >>
  `gas_events_blocks (SUC fuel) C fn raw =
    gas_events_block fuel C fn.fn_name old post ++
      (case exec_block fuel C old post of
        OK t => if t.vs_halted then [] else gas_events_blocks fuel C fn t
      | _ => [])` by
    (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [gas_events_blocks_def])) >>
     qpat_x_assum `enters_block fn raw post` mp_tac >>
     simp[contextCodegenRelTheory.enters_block_def, IgnAsm `fn' = _`] >>
     rpt strip_tac >> gvs[IgnAsm `fn' = _`]) >>
  `gas_events_blocks (SUC fuel) C' fn' raw' =
    gas_events_block fuel C' fn.fn_name bb' done ++
      (case exec_block fuel C' bb' done of
        OK t => if t.vs_halted then [] else gas_events_blocks fuel C' fn' t
      | _ => [])` by
    (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [gas_events_blocks_def])) >>
     qpat_x_assum `enters_block fn' raw' post'` mp_tac >>
     simp[contextCodegenRelTheory.enters_block_def, IgnAsm `fn' = _`] >>
     rpt strip_tac >> gvs[IgnAsm `fn' = _`]) >>
  `run_blocks (SUC fuel) C fn raw =
    (case exec_block fuel C old post of
       OK t => if t.vs_halted then Halt t else run_blocks fuel C fn t
     | r => r)` by
    (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_blocks_def])) >>
     qpat_x_assum `enters_block fn raw post` mp_tac >>
     simp[contextCodegenRelTheory.enters_block_def, IgnAsm `fn' = _`] >>
     rpt strip_tac >> gvs[IgnAsm `fn' = _`] >>
     Cases_on `exec_block fuel C old post` >> simp[]) >>
  `run_blocks (SUC fuel) C' fn' raw' =
    (case exec_block fuel C' bb' done of
       OK t => if t.vs_halted then Halt t else run_blocks fuel C' fn' t
     | r => r)` by
    (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_blocks_def])) >>
     qpat_x_assum `enters_block fn' raw' post'` mp_tac >>
     simp[contextCodegenRelTheory.enters_block_def, IgnAsm `fn' = _`] >>
     rpt strip_tac >> gvs[IgnAsm `fn' = _`] >>
     Cases_on `exec_block fuel C' bb' done` >> simp[]) >>
  Cases_on `exec_block fuel C old post` >>
  asm_x "block_result" mp_tac >> simp[IgnAsm `fn' = _`] >> strip_tac
  >- suspend "ok" >>
  asm_x "prepared_ih" kall_tac >>
  qpat_x_assum `!fn fn' st. _` kall_tac >>
  Cases_on `exec_block fuel C' bb' done` >>
  fs[frame_result_rel_def, IgnAsm `fn' = _`]
QED

Resume current_events_fuel[entry]:
  qpat_x_assum `_ /\ _` kall_tac >>
  rpt gen_tac >> strip_tac >>
  `make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
    first_block_no_preds fn /\ first_block_no_phi fn` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `?eb. entry_block fn = SOME eb` by
    (Cases_on `fn.fn_blocks` >> fs[fn_entry_state_def, fn_entry_label_def, entry_block_def]) >>
  drule_all make_ssa_lockstep_phi_context >> strip_tac >>
  drule_all current_target_entry_prefix_initial >> strip_tac >>
  `ctx_bisim C C` by metis_tac[simplifyCfgSimToolsTheory.ctx_bisim_refl] >>
  drule_all current_phi_context_entry_cut >> strip_tac >>
  `wf_function fn'` by metis_tac[o1MakeSsaStructuralShapeTheory.make_ssa_current_fn_wf_function] >>
  `fn_inst_wf fn'` by metis_tac[o1MakeSsaFormatsTheory.make_ssa_current_fn_inst_wf] >>
  `wf_ssa fn'` by
    (irule makeSsaCurrentWfSsaTheory.make_ssa_current_fn_wf_ssa >>
     qexistsl_tac [`fn`, `s`, `s'`] >>
     fs[o1PassContractTheory.make_ssa_input_ok_def, IgnAsm `fn' = _`] >>
     conj_tac >- first_assum ACCEPT_TAC >> metis_tac[]) >>
  `st.vs_current_bb = eb.bb_label /\ st.vs_inst_idx = 0` by
    (Cases_on `fn.fn_blocks` >> fs[fn_entry_state_def, fn_entry_label_def, entry_block_def]) >>
  `bb = bb'` by gvs[IgnAsm `fn' = _`] >>
  `EVERY (\i. i.inst_opcode <> PHI) eb.bb_instructions` by
    (Cases_on `fn.fn_blocks` >>
     gvs[entry_block_def, o1PassContractTheory.first_block_no_phi_def]) >>
  `enters_block fn st st` by metis_tac[enters_block_no_phi] >>
  first_x_assum irule >>
  simp[IgnAsm `fn' = _`] >>
  qexistsl_tac [`A`, `H`, `st`, `events`, `st`, `st`, `renamed`, `s`, `s'`] >>
  simp[IgnAsm `fn' = _`, current_prefix_steps_def] >> metis_tac[]
QED
Resume current_events_fuel[silent]:
  `?new. lookup_block l renamed = SOME new /\
    bb' = if blocks_have_leading_phi fn.fn_blocks
      then simplify_current_phi_block new else new` by
    (qpat_x_assum `lookup_block l fn'.fn_blocks = _` mp_tac >>
     qpat_assum `fn' = _` SUBST1_TAC >>
     simp[makeSsaCurrentCleanupShapeTheory.current_cleanup_if_lookup] >>
     Cases_on `lookup_block l renamed` >> simp[] >> metis_tac[]) >>
  `phi_prefix_length new.bb_instructions = LENGTH pre +
    LENGTH (collect_phis old.bb_instructions)` by
    (drule_all makeSsaCurrentPrefixSuffixOwnerTheory.current_prefix_actual_endpoint >> simp[]) >>
  Cases_on `blocks_have_leading_phi fn.fn_blocks`
  >- (`bb' = simplify_current_phi_block new` by metis_tac[] >>
      qpat_assum `copies = _` (fn th => rewrite_tac[th]) >>
      rewrite_tac[EVERY_EL] >> qx_gen_tac `j` >> strip_tac >>
      `j < LENGTH pre + LENGTH (collect_phis old.bb_instructions) -
         phi_prefix_length bb'.bb_instructions /\
       j < LENGTH (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions)` by
        (fs[LENGTH_TAKE_EQ, LENGTH_DROP, MIN_DEF] >> gvs[]) >>
      `EL j (TAKE (LENGTH pre + LENGTH (collect_phis old.bb_instructions) -
          phi_prefix_length bb'.bb_instructions)
          (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions)) =
        EL (phi_prefix_length bb'.bb_instructions + j) bb'.bb_instructions` by
        (qpat_assum `j < _ - _` mp_tac >>
         qpat_assum `j < LENGTH (DROP _ _)` mp_tac >>
         simp[NoAsms, EL_TAKE, EL_DROP, ADD_COMM]) >>
      pop_assum SUBST1_TAC >>
      `phi_prefix_length bb'.bb_instructions <= phi_prefix_length bb'.bb_instructions + j /\
       phi_prefix_length bb'.bb_instructions + j < phi_prefix_length new.bb_instructions` by decide_tac >>
      `((EL (phi_prefix_length bb'.bb_instructions + j) bb'.bb_instructions).inst_opcode = ASSIGN) \/
       ((EL (phi_prefix_length bb'.bb_instructions + j) bb'.bb_instructions).inst_opcode = NOP)` by
        metis_tac[simplify_current_phi_block_layout] >> simp[]) >>
  `bb' = new` by metis_tac[] >> fs[]
QED

Resume current_events_fuel[ok]:
  `t'.vs_halted = v.vs_halted /\ t'.vs_current_bb = v.vs_current_bb` by
    fs[current_cut_inv_def, state_rel_def, stateFrameTheory.execution_frame_def] >>
  Cases_on `v.vs_halted`
  >- (fs[current_cut_inv_def, state_rel_def, frame_result_rel_def, IgnAsm `fn' = _`]) >>
  simp[IgnAsm `fn' = _`] >>
  `MEM old fn.fn_blocks /\ old.bb_label = l` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM, venomExecProofsTheory.lookup_block_label] >>
  `v.vs_prev_bb = SOME l` by
    (drule cfgNormSupplySimTheory.supply_run_block_entry_control >>
     disch_then (qspecl_then [`raw`, `v`, `fuel`, `C`, `old`] mp_tac) >>
     simp[IgnAsm `fn' = _`]) >>
  `bb_well_formed old /\ EVERY inst_wf old.bb_instructions` by
    (fs[wf_function_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM v.vs_current_bb (bb_succs old)` by
    (irule venomExecProofsTheory.exec_block_current_bb_in_succs >>
     reverse conj_tac
     >- (conj_tac
         >- (qpat_x_assum `bb_well_formed old` mp_tac >> simp[bb_well_formed_def]) >>
         reverse conj_tac >- asm_rewrite_tac[] >>
         qexistsl [`C`, `fuel`, `post`] >> simp[IgnAsm `fn' = _`]) >>
     qpat_x_assum `bb_well_formed old` mp_tac >>
     pure_rewrite_tac[bb_well_formed_def] >> rpt strip_tac >>
     `i < LENGTH old.bb_instructions` by decide_tac >>
     `i = PRE (LENGTH old.bb_instructions)` by metis_tac[] >> decide_tac) >>
  `fn_cfg_edge fn l v.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> qexists `old` >> simp[]) >>
  `bb'.bb_label = done.vs_current_bb` by
    (fs[current_cut_inv_def, state_rel_def] >>
     metis_tac[venomExecProofsTheory.lookup_block_label]) >>
  `fn_reachable fn' done.vs_current_bb` by
    (fs[current_cut_inv_def, state_rel_def] >> metis_tac[]) >>
  `v.vs_current_bb = v.vs_current_bb` by simp[] >>
  drule_all current_events_successor_prepared >> strip_tac >>
  asm_x "prepared_ih" irule >>
  simp[IgnAsm `fn' = _`] >>
  metis_tac[]
QED
Finalise current_events_fuel

Theorem make_ssa_current_fn_gas_events:
  LIST_REL (\fn fn'. ?s s'. ir_supply_covers_fn s fn /\
    ir_supply_inst_ok s /\ make_ssa_current_fn s fn = (fn',s'))
    C.ctx_functions C'.ctx_functions /\
  EVERY (\fn. make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
    first_block_no_preds fn /\ first_block_no_phi fn) C.ctx_functions /\
  MEM fn C.ctx_functions /\
  (?s s'. ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
    make_ssa_current_fn s fn = (fn',s')) /\ fn_entry_state fn st ==>
  gas_events_blocks fuel C fn st = gas_events_blocks fuel C' fn' st
Proof
  strip_tac >> drule_all current_events_fuel >>
  disch_then (qspec_then `fuel` (mp_tac o CONJUNCT2)) >>
  metis_tac[]
QED
