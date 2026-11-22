Theory runtimePeakMemoryBound
Ancestors
  runtimePeakMemoryPackage runtimePeakMemoryProof runtimePeakMemoryCode
  runtimePeakMemorySourceGate loweringBudgetAccountCodes
  vyperLoweringCorrect vyperCompiler e2eDefs
  contextCodegenRel contextRawReachable venomLayout venomState venomInst words list

val _ = Parse.hide "body";
val _ = Parse.hide "tops";

Theorem lower_vyper_runtime_unit_dynamic_peak_memory_bound:
  !tops rpolicy (unit:compilation_unit) (cp_fmp:num) am tx
   (fmp:bytes32) vs vs0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    (!vis mut nr rr name args dflts ret body.
       MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
       vis <> Deploy ==>
       ~supported_stmts_expr_exists
         (\e. ?ty raw salted rof order es d.
            e = Call ty
                  (CreateTarget (CreateFromBlueprint raw) salted rof order)
                  es d)
         body /\
       EVERY (\d0. ~supported_expr_exists
         (\e. ?ty raw salted rof order es d.
            e = Call ty
                  (CreateTarget (CreateFromBlueprint raw) salted rof order)
                  es d)
         d0) dflts) /\
    initial_venom_state_rel tops am tx vs /\
    vs.vs_initial_fmp = n2w cp_fmp /\
    vs.vs_fmp = n2w cp_fmp /\
    cp_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    raw_variant fmp vs0 vs /\
    LENGTH vs0.vs_outcomes < 2 ** 64 /\
    outcomes_accounts_typed (SOME vs0.vs_outcomes) /\
    LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !fn i s.
      raw_reachable vs0 unit.cu_context fn i s ==>
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
  rpt gen_tac >> strip_tac >>
  `blueprint_create_root =
    (\e. ?ty raw salted rof order es d.
       e = Call ty (CreateTarget (CreateFromBlueprint raw) salted rof order) es d)` by
    simp[FUN_EQ_THM, blueprint_create_root_def] >>
  `runtime_blueprint_free tops` by (fs[runtime_blueprint_free_def] >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`source_tops` |-> `tops`, `policy` |-> `rpolicy`]
    lower_vyper_runtime_unit_dalloca_windows) >>
  impl_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  `!fn. MEM fn unit.cu_context.ctx_functions ==> ALL_DISTINCT (fn_labels fn)` by
    (drule lower_vyper_runtime_unit_context_entry >>
     simp[lowering_context_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `lowering_context_ok unit.cu_context` by
    metis_tac[lower_vyper_runtime_unit_context_entry] >>
  `account_code_lengths_ok vs.vs_accounts /\ ~vs.vs_halted` by
    (fs[source_typing_ok_def, initial_venom_state_rel_def] >>
     metis_tac[initial_account_codes_after_transfer]) >>
  mp_tac (Q.INST [`ctx` |-> `unit.cu_context`] raw_dynamic_peak_memory_from_windows) >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[active_inst_dalloca_windows]) >>
  simp[]
QED

Theorem lower_vyper_runtime_unit_raw_headroom:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vi /\
  vi.vs_fmp = vi.vs_initial_fmp /\ w2n vi.vs_initial_fmp < 2 ** 254 /\
  LENGTH vi.vs_outcomes < 2 ** 64 /\
  outcomes_accounts_typed (SOME vi.vs_outcomes) /\
  LENGTH vi.vs_call_ctx.cc_calldata < 2 ** 64 ==>
  !fn i s. raw_reachable vi unit.cu_context fn i s ==> dalloca_fmp_headroom i s
Proof
  strip_tac >>
  `lowering_context_ok unit.cu_context` by
    metis_tac[lower_vyper_runtime_unit_context_entry] >>
  `account_code_lengths_ok vi.vs_accounts /\ ~vi.vs_halted` by
    (fs[source_typing_ok_def, initial_venom_state_rel_def] >>
     metis_tac[initial_account_codes_after_transfer]) >>
  mp_tac (Q.INST [`source_tops` |-> `tops`, `policy` |-> `rpolicy`,
    `window` |-> `\chunk k. raw_call_dalloca_chunk chunk k \/
       create_copy_dalloca_chunk chunk k \/ create_blueprint_dalloca_chunk chunk k`]
    lower_vyper_runtime_unit_dalloca_windows_for) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!fn. MEM fn unit.cu_context.ctx_functions ==> ALL_DISTINCT (fn_labels fn)` by
    fs[lowering_context_ok_def, EVERY_MEM] >>
  irule raw_headroom_from_dalloca_windows >>
  simp[] >> metis_tac[active_inst_dalloca_windows_with_blueprint]
QED
