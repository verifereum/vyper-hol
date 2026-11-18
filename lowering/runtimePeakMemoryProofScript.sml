(* Discharge the raw history obligation using the two runtime emitters. *)
Theory runtimePeakMemoryProof
Ancestors
  runtimeDynamicPeakMemory runtimePeakMemoryCode loweringBudgetDallocaWindows
  loweringBudgetCreateCopy loweringBudgetAccountCodes e2eDefs
  loweringBudgetRecorderOutcomes loweringCallBudgetHistory contextCodegenRel
  contextRawReachable vyperLoweringCorrect compileVyper vyperCompiler unitTransformDefs
  venomExecProofs
  o1PassContract venomLayout venomState venomInst venomExecSemantics
  finite_map words arithmetic list

Theorem lower_vyper_runtime_unit_dynamic_peak_memory_from_windows:
  lower_vyper_runtime_unit source_tops rpolicy = SOME unit /\
  source_typing_ok source_tops am tx /\
  initial_venom_state_rel source_tops am tx vs /\
  raw_variant fmp vs0 vs /\
  cp_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
  LENGTH vs0.vs_outcomes < 2 ** 64 /\
  outcomes_accounts_typed (SOME vs0.vs_outcomes) /\
  LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 /\
  (!fn i s. MEM fn unit.cu_context.ctx_functions /\ active_inst fn i s /\
    i.inst_opcode = DALLOCA ==>
      raw_call_dalloca_window fn i s \/ create_copy_dalloca_window fn i s) ==>
  !fn i s. raw_reachable vs0 unit.cu_context fn i s ==>
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
  mp_tac lower_vyper_runtime_unit_dynamic_peak_memory_from_history >>
  impl_tac >- (
    asm_rewrite_tac[] >> rpt strip_tac >>
    qpat_x_assum `root = _` SUBST_ALL_TAC >>
    drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
    `MEM entry unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
    `!fn. MEM fn unit.cu_context.ctx_functions ==> ALL_DISTINCT (fn_labels fn)` by
      fs[lowering_context_ok_def, EVERY_MEM] >>
    `vs0.vs_accounts = vs.vs_accounts` by
      (qpat_assum `raw_variant fmp vs0 vs`
        (mp_tac o AP_TERM ``\(v:venom_state). v.vs_accounts`` o
         REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
       simp[]) >>
    `account_code_lengths_ok vs.vs_accounts` by metis_tac[runtime_initial_account_codes] >>
    `entered.vs_outcomes = vs0.vs_outcomes /\
     entered.vs_accounts = vs0.vs_accounts` by
      (imp_res_tac enters_block_preserves_outcomes >>
       imp_res_tac account_codes_enters_block >> fs[]) >>
    `entered.vs_call_ctx = vs0.vs_call_ctx` by
      (qpat_x_assum `enters_block _ _ _` mp_tac >>
       simp[enters_block_def] >> strip_tac >>
       drule eval_phis_only_updates_vs_vars >>
       disch_then (mp_tac o AP_TERM ``\(v:venom_state). v.vs_call_ctx``) >>
       simp[]) >>
    mp_tac (Q.INST [`root` |-> `<| bp_stack := []; bp_params := [];
      bp_prov := FEMPTY; bp_taint := entry_taint; bp_fn := entry;
      bp_state := entered |>`, `ctx` |-> `unit.cu_context`, `lo` |-> `cp_fmp`,
      `start` |-> `vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                            vs_inst_idx := 0|>`]
      lower_budget_dynamic_history_certificate) >>
    fs[]) >>
  simp[]
QED
