Theory deployDynamicMemory
Ancestors
  deployPeakMemoryBound[ignore_grammar] deployPeakMemoryHeaders ctorDeployDefs
  runtimeDynamicPeakMemory
  e2eDeployDefs e2eDefs asmOptimizer
  compileVyper supportedStmtTraverse supportedExprTraverse vyperAST
  contextRawReachable unitTransformDefs unitShapeDefs lowerDloadDefs
  venomInst venomState venomLayout exprSimHypsDefs fmpLowerSequenceExec
  loweringShapeSource callRawVariant o1PassContract e2eEntry callTrace words list

val _ = Parse.hide "tops";
val _ = Parse.hide "body";

Definition top_body_has_def:
  top_body_has form (FunctionDecl vis mut nr rr name args dflts ret body) =
    (supported_stmts_expr_exists form body \/ EXISTS (supported_expr_exists form) dflts) /\
  top_body_has form _ = F
End

Definition deploy_dalloca_form_occurs_def:
  deploy_dalloca_form_occurs form tops <=>
    IS_SOME (SND (SND (SND (classify_functions tops)))) /\
    ?vis mut nr rr name args dflts ret body.
      MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
      (vis = Deploy \/ vis = Internal) /\
      (supported_stmts_expr_exists form body \/
       EXISTS (supported_expr_exists form) dflts)
End

Theorem deploy_raw_fmp_without_blueprint[local]:
  !policy tops runtime_bc rpolicy dunit dout prog prog' cplan
   am tx es vs vi (fmp:bytes32).
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    IS_SOME (SND (SND (SND (classify_functions tops)))) /\
    ~deploy_dalloca_form_occurs
      (\e. ?ty b s r ks es d.
            e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d) tops /\
    vs = opt_deploy_entry_state_own prog prog' cplan tops es /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    raw_variant fmp vi vs /\
    LENGTH vi.vs_outcomes < 2 ** 64 /\
    outcomes_accounts_typed (SOME vi.vs_outcomes) /\
    LENGTH vi.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !fn inst s. raw_reachable vi dunit.cu_context fn inst s ==>
      s.vs_initial_fmp = fmp /\
      w2n s.vs_initial_fmp <= w2n s.vs_fmp /\ dalloca_no_wrap inst s /\
      fmp_frontier_rel (w2n vs.vs_initial_fmp) (w2n fmp)
        (w2n vs.vs_initial_fmp + (w2n s.vs_fmp - w2n fmp)) s.vs_fmp /\
      (inst.inst_opcode = DALLOCA ==>
        w2n s.vs_fmp <= w2n fmp + 2 ** 64 * 2 ** 64)
Proof
  rpt gen_tac >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  `~vs.vs_halted /\ vs.vs_accounts = accounts_after_transfer tx am.accounts` by
    fs[opt_deploy_entry_state_own_def, opt_entry_state_own_def,
       entry_venom_state_def, init_venom_state_def, deploy_state_rel_def] >>
  `!vis mut nr rr name args dflts ret body.
      MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
      (vis = Deploy \/ vis = Internal) ==>
      ~supported_stmts_expr_exists
        (\e. ?ty b s r ks es d.
          e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d) body /\
      EVERY (\d0. ~supported_expr_exists
        (\e. ?ty b s r ks es d.
          e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d) d0)
        dflts` by
    (qpat_x_assum `~deploy_dalloca_form_occurs _ _` mp_tac >>
     asm_rewrite_tac [deploy_dalloca_form_occurs_def, EVERY_NOT_EXISTS] >>
     simp[] >> metis_tac[]) >>
  qspecl_then [`tops`, `rpolicy`, `runtime_bc`, `dunit`,
    `w2n vs.vs_initial_fmp`, `am`, `tx`, `fmp`, `vs`, `vi`]
    mp_tac lower_vyper_deploy_unit_dynamic_peak_memory_from_unit >>
  impl_tac >- (asm_rewrite_tac[] >> simp[]) >>
  simp[dalloca_no_wrap_def] >> metis_tac[]
QED

Theorem lower_vyper_deploy_unit_raw_fmp_raw_call_calldata:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan
   am tx es vs vi (fmp:bytes32).
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    deploy_dalloca_form_occurs
      (\e. ?ty f es d. e = Call ty (RawCallCalldataTarget f) es d) tops /\
    ~deploy_dalloca_form_occurs
      (\e. ?ty s r ks es d.
            e = Call ty (CreateTarget CreateCopyOf s r ks) es d) tops /\
    ~deploy_dalloca_form_occurs
      (\e. ?ty b s r ks es d.
            e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d) tops /\
    vs = opt_deploy_entry_state_own prog prog' cplan tops es /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    raw_variant fmp vi vs /\
    LENGTH vi.vs_outcomes < 2 ** 64 /\
    outcomes_accounts_typed (SOME vi.vs_outcomes) /\
    LENGTH vi.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !fn inst s. raw_reachable vi dunit.cu_context fn inst s ==>
      s.vs_initial_fmp = fmp /\
      w2n s.vs_initial_fmp <= w2n s.vs_fmp /\ dalloca_no_wrap inst s /\
      fmp_frontier_rel (w2n vs.vs_initial_fmp) (w2n fmp)
        (w2n vs.vs_initial_fmp + (w2n s.vs_fmp - w2n fmp)) s.vs_fmp /\
      (inst.inst_opcode = DALLOCA ==>
        w2n s.vs_fmp <= w2n fmp + 2 ** 64 * 2 ** 64)
Proof
  rpt gen_tac >> strip_tac >>
  `IS_SOME (SND (SND (SND (classify_functions tops))))` by
    fs[deploy_dalloca_form_occurs_def] >>
  qspecl_then [`policy`, `tops`, `runtime_bc`, `rpolicy`, `dunit`, `dout`,
    `prog`, `prog'`, `cplan`, `am`, `tx`, `es`, `vs`, `vi`, `fmp`]
    mp_tac deploy_raw_fmp_without_blueprint >>
  impl_tac >- asm_rewrite_tac[] >> simp[]
QED

Theorem lower_vyper_deploy_unit_raw_fmp_create_copy:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan
   am tx es vs vi (fmp:bytes32).
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    deploy_dalloca_form_occurs
      (\e. ?ty s r ks es d.
            e = Call ty (CreateTarget CreateCopyOf s r ks) es d) tops /\
    ~deploy_dalloca_form_occurs
      (\e. ?ty b s r ks es d.
            e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d) tops /\
    vs = opt_deploy_entry_state_own prog prog' cplan tops es /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    raw_variant fmp vi vs /\
    LENGTH vi.vs_outcomes < 2 ** 64 /\
    outcomes_accounts_typed (SOME vi.vs_outcomes) /\
    LENGTH vi.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !fn inst s. raw_reachable vi dunit.cu_context fn inst s ==>
      s.vs_initial_fmp = fmp /\
      w2n s.vs_initial_fmp <= w2n s.vs_fmp /\ dalloca_no_wrap inst s /\
      fmp_frontier_rel (w2n vs.vs_initial_fmp) (w2n fmp)
        (w2n vs.vs_initial_fmp + (w2n s.vs_fmp - w2n fmp)) s.vs_fmp /\
      (inst.inst_opcode = DALLOCA ==>
        w2n s.vs_fmp <= w2n fmp + 2 ** 64 * 2 ** 64)
Proof
  rpt gen_tac >> strip_tac >>
  `IS_SOME (SND (SND (SND (classify_functions tops))))` by
    fs[deploy_dalloca_form_occurs_def] >>
  qspecl_then [`policy`, `tops`, `runtime_bc`, `rpolicy`, `dunit`, `dout`,
    `prog`, `prog'`, `cplan`, `am`, `tx`, `es`, `vs`, `vi`, `fmp`]
    mp_tac deploy_raw_fmp_without_blueprint >>
  impl_tac >- asm_rewrite_tac[] >> simp[]
QED

Theorem lower_vyper_deploy_unit_raw_fmp_create_blueprint:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan
   am tx es vs vi (fmp:bytes32).
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    deploy_dalloca_form_occurs
      (\e. ?ty b s r ks es d.
            e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d) tops /\
    vs = opt_deploy_entry_state_own prog prog' cplan tops es /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    raw_variant fmp vi vs /\
    LENGTH vi.vs_outcomes < 2 ** 64 /\
    outcomes_accounts_typed (SOME vi.vs_outcomes) /\
    LENGTH vi.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !fn inst s. raw_reachable vi dunit.cu_context fn inst s ==>
      dalloca_fmp_headroom inst s
Proof
  rpt gen_tac >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  `~vs.vs_halted /\ vs.vs_accounts = accounts_after_transfer tx am.accounts` by
    fs[opt_deploy_entry_state_own_def, opt_entry_state_own_def,
       entry_venom_state_def, init_venom_state_def, deploy_state_rel_def] >>
  `~vi.vs_halted /\ vi.vs_accounts = vs.vs_accounts /\
    vi.vs_fmp = fmp /\ vi.vs_initial_fmp = fmp` by
    fs[raw_variant_def, gas_variant_def,
       venomStateTheory.venom_state_component_equality] >>
  metis_tac[lower_vyper_deploy_unit_raw_headroom]
QED

(* A constructor or packaged internal uses one of the three dynamic forms. *)
Theorem deploy_entry_raw_headroom:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan
   am tx es vs vi (fmp:bytes32).
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    deploy_dalloca_form_occurs expr_raw_shape_root tops /\
    LENGTH (call_trace es) < 2 ** 64 /\
    vs = opt_deploy_entry_state_own prog prog' cplan tops es /\
    w2n vs.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    raw_variant fmp vi vs ==>
    !fn inst s. raw_reachable vi dunit.cu_context fn inst s ==>
      dalloca_fmp_headroom inst s
Proof
  rpt gen_tac >> strip_tac >>
  `vs.vs_fmp = vs.vs_initial_fmp /\
    vs.vs_outcomes = MAP SND (call_trace es)` by
    simp[opt_deploy_entry_state_own_def, opt_entry_state_own_def,
         entry_venom_state_def] >>
  `vi.vs_outcomes = vs.vs_outcomes /\ vi.vs_call_ctx = vs.vs_call_ctx` by
    metis_tac[raw_variant_outcomes, raw_variant_call_ctx] >>
  `outcomes_accounts_typed (SOME vi.vs_outcomes)` by
    (qpat_assum `deploy_state_rel _ _ _ _ _`
       (mp_tac o MATCH_MP deploy_state_rel_call_outcomes_ok) >>
     simp[call_outcomes_ok_def, outcomes_accounts_typed_def]) >>
  `vi.vs_call_ctx.cc_calldata = []` by
    gvs[opt_deploy_entry_state_own_def, opt_entry_state_own_def,
        entry_venom_state_def, deploy_state_rel_def] >>
  Cases_on `deploy_dalloca_form_occurs
      (\e. ?ty b s r ks es d.
        e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d) tops`
  >- (qspecl_then [`fin`, `policy`, `tops`, `runtime_bc`, `rpolicy`, `dunit`,
         `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`, `es`, `vs`, `vi`, `fmp`]
       mp_tac lower_vyper_deploy_unit_raw_fmp_create_blueprint >>
     simp[LENGTH_MAP, EVAL ``LENGTH ([]:word8 list) < 2 ** 64``]) >>
  `IS_SOME (SND (SND (SND (classify_functions tops))))` by
    fs[deploy_dalloca_form_occurs_def] >>
  `~vi.vs_halted /\ vi.vs_initial_fmp = fmp /\ vi.vs_fmp = fmp` by
    fs[raw_variant_def, gas_variant_def, venomStateTheory.venom_state_component_equality,
       opt_deploy_entry_state_own_def, opt_entry_state_own_def,
       entry_venom_state_def, init_venom_state_def] >>
  qspecl_then [`policy`, `tops`, `runtime_bc`, `rpolicy`, `dunit`,
         `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`, `es`, `vs`, `vi`, `fmp`]
       mp_tac deploy_raw_fmp_without_blueprint >>
  impl_tac >- simp[LENGTH_MAP, EVAL ``LENGTH ([]:word8 list) < 2 ** 64``] >>
  strip_tac >> rpt strip_tac >>
  match_mp_tac (Q.INST [`ctx` |-> `dunit.cu_context`, `fn` |-> `fn`,
      `vs0` |-> `vi`, `i` |-> `inst`] raw_reachable_dalloca_headroom_from_peak) >>
  simp[EVAL ``LENGTH ([]:word8 list) < 2 ** 64``] >> metis_tac[]
QED
