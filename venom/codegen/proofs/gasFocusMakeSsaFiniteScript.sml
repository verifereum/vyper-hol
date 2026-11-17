Theory gasFocusMakeSsaFinite
Ancestors
  gasFocusMakeSsaLocalEvents gasEvents
  makeSsaCurrentForwardCut makeSsaCurrentForwardBlock makeSsaCurrentForwardRuntime
  makeSsaCurrentEntryPrefix makeSsaCurrentPrefixTransport makeSsaCurrentCopyPrefixRuntime
  makeSsaCurrentWfSsa makeSsaCurrentCutInv makeSsaCurrentLockstep
  makeSsaCurrentCertificate makeSsaCurrentPrefixSuffixOwner
  o1ContractMakeSsaSrc o1PassLift o1FrameLockstep
  venomExecSemantics venomExecProofs venomExecProps venomWf venomInst
  contextCodegenRel stateFrame list rich_list arithmetic

(* Every direct ancestor above was checked against the exact NEW HELPER
   GUARD exclusion set in TO_focus_producer-lead-20261116T235445535981Z_m0071_t001;
   none is excluded. *)

Theorem current_invoke_events_pair[local]:
  inst.inst_opcode = INVOKE /\ inst_pair sg inst inst' /\
  state_rel sg st st' ==>
  gas_events_step fuel C owner' inst' st' =
  gas_events_step fuel C owner inst st
Proof
  strip_tac >>
  `inst'.inst_opcode = INVOKE` by fs[inst_pair_def] >>
  Cases_on `decode_invoke inst`
  >- (Cases_on `inst.inst_operands`
      >- (fs[inst_pair_def, gas_events_step_def, decode_invoke_def]) >>
      Cases_on `inst'.inst_operands` >> fs[inst_pair_def] >>
      rename1 `op_rename sg h h'` >>
      Cases_on `h` >> Cases_on `h'` >>
      gvs[op_rename_def, gas_events_step_def, decode_invoke_def]) >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  drule_all current_invoke_decode_args_pair >> strip_tac >>
  `!fn args. setup_callee fn args st' = setup_callee fn args st` by
    (rpt gen_tac >> irule setup_callee_execution_frame >> fs[state_rel_def]) >>
  simp[gas_events_step_def] >>
  Cases_on `lookup_function pair0 C.ctx_functions` >> simp[] >>
  Cases_on `eval_operands pair1 st` >> simp[]
QED

Theorem current_cut_block_events[local]:
  !i st st'.
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l fn'.fn_blocks = SOME bb' /\
  A l = current_block_annotations old pre /\
  LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
  LENGTH (collect_phis old.bb_instructions) <= i /\
  i <= LENGTH old.bb_instructions /\
  st.vs_current_bb = l /\ st.vs_inst_idx = i /\
  st'.vs_inst_idx = LENGTH pre + i /\
  current_cut_inv fn A renamed H events l i st st' ==>
  ?extra.
    gas_events_block fuel C fn'.fn_name bb' st' =
      gas_events_block fuel C fn.fn_name old st ++ extra /\
    (terminates (exec_block fuel C old st) ==> extra = [])
Proof
  measureInduct_on `LENGTH old.bb_instructions - i` >> rpt gen_tac >> strip_tac >>
  Cases_on `i = LENGTH old.bb_instructions`
  >- (qexists `[]` >> simp[Once gas_events_block_def, get_instruction_def] >>
      simp[Once gas_events_block_def, get_instruction_def]) >>
  `i < LENGTH old.bb_instructions` by decide_tac >>
  `inst_wf (EL i old.bb_instructions)` by
    metis_tac[fn_inst_wf_def, lookup_block_MEM, EL_MEM] >>
  drule_all current_cut_inv_ordinary_step_forward >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `bb'' = bb'` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `bb'' = bb'` SUBST_ALL_TAC >>
  `(EL (LENGTH pre + i) bb'.bb_instructions).inst_opcode =
    (EL i old.bb_instructions).inst_opcode` by fs[inst_pair_def] >>
  `gas_events_step fuel C fn'.fn_name
      (EL (LENGTH pre + i) bb'.bb_instructions) st' =
    gas_events_step fuel C fn.fn_name (EL i old.bb_instructions) st` by
    (Cases_on `(EL i old.bb_instructions).inst_opcode = GAS`
     >- (irule make_ssa_paired_gas_site >>
         simp[] >> conj_tac
         >- (qexistsl [`old`, `bb'`, `i`, `l`] >>
             gvs[makeSsaCurrentLockstepTheory.make_ssa_pos_def,
               makeSsaCurrentPrefixSuffixOwnerTheory.current_prefix_collect_length,
               ADD_COMM]) >>
         qexistsl [`s`, `s'`] >> simp[]) >>
     Cases_on `(EL i old.bb_instructions).inst_opcode = INVOKE`
     >- (irule current_invoke_events_pair >>
         fs[current_cut_inv_def] >> metis_tac[]) >>
     simp[gas_events_step_def]) >>
  once_rewrite_tac[gas_events_block_def] >>
  simp[get_instruction_def, Excl "ADD_COMM"] >>
  Cases_on `step_inst fuel C (EL i old.bb_instructions) st`
  >- suspend "ok"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "intret" >>
  suspend "error"
QED

Resume current_cut_block_events[ok]:
  qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >> fs[ADD_COMM] >>
  Cases_on `is_terminator (EL i old.bb_instructions).inst_opcode`
  >- (qexists `[]` >> gvs[]) >>
  `v.vs_current_bb = l` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`v with vs_inst_idx := SUC i`,
    `t' with vs_inst_idx := SUC (i + LENGTH pre)`] mp_tac) >>
  simp[ADD_COMM] >> strip_tac >> qexists `extra` >>
  gvs[APPEND_ASSOC] >> strip_tac >> first_x_assum irule >>
  qpat_x_assum `terminates _` mp_tac >>
  simp[Once (cj 2 run_defs), get_instruction_def]
QED
Resume current_cut_block_events[halt]:
  qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >> fs[ADD_COMM] >>
  Cases_on `step_inst fuel C (EL (i + LENGTH pre) bb'.bb_instructions) st'` >>
  qexists `[]` >> gvs[frame_result_rel_def]
QED
Resume current_cut_block_events[abort]:
  qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >> fs[ADD_COMM] >>
  Cases_on `step_inst fuel C (EL (i + LENGTH pre) bb'.bb_instructions) st'` >>
  qexists `[]` >> gvs[frame_result_rel_def]
QED
Resume current_cut_block_events[intret]:
  qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >> fs[ADD_COMM] >>
  Cases_on `step_inst fuel C (EL (i + LENGTH pre) bb'.bb_instructions) st'` >>
  qexists `[]` >> gvs[frame_result_rel_def]
QED
Resume current_cut_block_events[error]:
  gvs[ADD_COMM] >>
  simp[Once (cj 2 run_defs), get_instruction_def, terminates_not_error]
QED
Finalise current_cut_block_events
