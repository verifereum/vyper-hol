(* Discharge the raw history obligation using the block-local allocation windows. *)
Theory runtimePeakMemoryProof
Ancestors
  runtimeDynamicPeakMemory runtimePeakMemoryCode loweringBudgetDallocaWindows
  loweringBudgetCreateCopy loweringBudgetAccountCodes e2eDefs
  loweringBudgetRecorderOutcomes loweringCallBudgetHistory contextCodegenRel
  contextRawReachable vyperLoweringCorrect compileVyper vyperCompiler unitTransformDefs
  venomExecProofs o1LowerDloadRunnerBoundary
  o1PassContract venomLayout venomState venomInst venomExecSemantics
  ptrDiscipline finite_map words arithmetic list

Theorem raw_dynamic_peak_memory_from_windows:
  lowering_context_ok ctx /\
  account_code_lengths_ok vs.vs_accounts /\ ~vs.vs_halted /\
  raw_variant fmp vs0 vs /\
  cp_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
  LENGTH vs0.vs_outcomes < 2 ** 64 /\
  outcomes_accounts_typed (SOME vs0.vs_outcomes) /\
  LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 /\
  (!fn i s. MEM fn ctx.ctx_functions /\ active_inst fn i s /\
    i.inst_opcode = DALLOCA ==>
      raw_call_dalloca_window fn i s \/ create_copy_dalloca_window fn i s) ==>
  !fn i s. raw_reachable vs0 ctx fn i s ==>
    s.vs_initial_fmp = fmp /\
    w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
    fmp_frontier_rel cp_fmp (w2n fmp)
      (cp_fmp + (w2n s.vs_fmp - w2n fmp)) s.vs_fmp /\
    (i.inst_opcode = DALLOCA ==>
     w2n s.vs_fmp <= w2n fmp + 2 ** 64 * 2 ** 64 /\
     !sz_op sz.
       i.inst_operands = [sz_op] /\ eval_operand sz_op s = SOME sz ==>
       w2n s.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256))
Proof
  strip_tac >>
  `vs0.vs_accounts = vs.vs_accounts /\ ~vs0.vs_halted /\
   vs0.vs_initial_fmp = fmp /\ vs0.vs_fmp = fmp` by
    (fs[raw_variant_def, gas_variant_def, venom_state_component_equality] >>
     metis_tac[]) >>
  mp_tac raw_dynamic_peak_memory_from_history >>
  impl_tac >- (
    asm_rewrite_tac[] >> rpt strip_tac >>
    qpat_x_assum `root = _` SUBST_ALL_TAC >>
    `MEM entry ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
    `!fn. MEM fn ctx.ctx_functions ==> ALL_DISTINCT (fn_labels fn)` by
      fs[lowering_context_ok_def, EVERY_MEM] >>
    `entered.vs_outcomes = vs0.vs_outcomes /\
     entered.vs_accounts = vs0.vs_accounts` by
      (imp_res_tac enters_block_preserves_outcomes >>
       imp_res_tac account_codes_enters_block >> fs[]) >>
    `entered.vs_call_ctx = vs0.vs_call_ctx` by
      (drule ld_enters_block_call_ctx >> simp[]) >>
    mp_tac (Q.INST [`root` |-> `<| bp_stack := []; bp_params := [];
      bp_prov := FEMPTY; bp_taint := entry_taint; bp_fn := entry;
      bp_state := entered |>`, `lo` |-> `cp_fmp`,
      `start` |-> `vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                            vs_inst_idx := 0|>`]
      lower_budget_dynamic_history_certificate) >>
    fs[]) >>
  simp[]
QED

Theorem raw_headroom_from_dalloca_windows:
  lowering_context_ok ctx /\ account_code_lengths_ok vi.vs_accounts /\
  ~vi.vs_halted /\ vi.vs_fmp = vi.vs_initial_fmp /\
  w2n vi.vs_initial_fmp < 2 ** 254 /\
  LENGTH vi.vs_outcomes < 2 ** 64 /\
  outcomes_accounts_typed (SOME vi.vs_outcomes) /\
  LENGTH vi.vs_call_ctx.cc_calldata < 2 ** 64 /\
  (!fn i s. MEM fn ctx.ctx_functions /\ active_inst fn i s /\
    i.inst_opcode = DALLOCA ==>
      raw_call_dalloca_window fn i s \/ create_copy_dalloca_window fn i s \/
      create_blueprint_dalloca_window fn i s) ==>
  !fn i s. raw_reachable vi ctx fn i s ==> dalloca_fmp_headroom i s
Proof
  strip_tac >>
  mp_tac (Q.INST [`vs0` |-> `vi`, `lo` |-> `w2n vi.vs_initial_fmp`]
    raw_dalloca_headroom_from_history) >>
  impl_tac >-
    (asm_rewrite_tac[] >> rpt strip_tac >>
     qpat_x_assum `root = _` SUBST_ALL_TAC >>
     `MEM entry ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
     `!fn. MEM fn ctx.ctx_functions ==> ALL_DISTINCT (fn_labels fn)` by
       fs[lowering_context_ok_def, EVERY_MEM] >>
     `entered.vs_outcomes = vi.vs_outcomes /\
      entered.vs_accounts = vi.vs_accounts` by
       (imp_res_tac enters_block_preserves_outcomes >>
        imp_res_tac account_codes_enters_block >> fs[]) >>
     `entered.vs_call_ctx = vi.vs_call_ctx` by
       (drule ld_enters_block_call_ctx >> simp[]) >>
     mp_tac (Q.INST [`root` |-> `<| bp_stack := []; bp_params := [];
       bp_prov := FEMPTY; bp_taint := entry_taint; bp_fn := entry;
       bp_state := entered |>`, `lo` |-> `w2n vi.vs_initial_fmp`,
       `current` |-> `i`,
       `start` |-> `vi with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                            vs_inst_idx := 0|>`]
       lower_budget_headroom_history_certificate) >>
     fs[]) >>
  simp[]
QED
