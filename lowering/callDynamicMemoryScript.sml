(* Raw entry FMP bounds for the call pipeline and its gas-focus prefixes. *)
Theory callDynamicMemory
Ancestors
  loweringMemCorrect runtimePeakMemoryBound runtimePeakMemorySourceGate
  runtimeDynamicPeakMemory[ignore_grammar]
  vyperLoweringCorrect vyperCompiler vyperTypeContract e2eDefs e2eEntry
  e2eOptEntry callRawVariant exprSimHypsDefs supportedExprTraverse
  supportedStmtTraverse vyperAST callTrace vfmTotalBalance vfmReturndataBound
  vfmWfState lowerDloadDefs unitTransformDefs o1PassContract contextRawReachable
  venomState venomLayout words arithmetic list rich_list

val _ = Parse.hide "body";
val _ = Parse.hide "tops";
val _ = Parse.hide "raw_headroom";

Theorem call_source_raw_fmp:
  lower_vyper_runtime_unit tops rpolicy = SOME unit ==>
  ?fmp. w2n (initial_fmp : bytes32) <= w2n (fmp : bytes32) /\
        unit_alloca_budget unit.cu_context +
          32 * ctx_dload_count unit.cu_context <= w2n fmp /\
        (w2n initial_fmp < 2 ** 254 ==> w2n fmp < 2 ** 254)
Proof
  strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule vyperCompilerTheory.lowering_context_ok_static_headroom >> strip_tac >>
  qabbrev_tac `raw_headroom = unit_alloca_budget unit.cu_context +
                         32 * ctx_dload_count unit.cu_context` >>
  `raw_headroom < 2 ** 254` by
    fs[Abbr `raw_headroom`, ctx_dload_count_def, FILTER_FLAT, LENGTH_FLAT, MAP_MAP_o,
       combinTheory.o_DEF] >>
  `w2n (initial_fmp : bytes32) < dimword (:256)` by
    metis_tac[wordsTheory.w2n_lt] >>
  `MAX (w2n initial_fmp) raw_headroom < dimword (:256)` by
    (fs[MAX_DEF, wordsTheory.dimword_def, dimindex_256] >> decide_tac) >>
  qexists_tac `n2w (MAX (w2n initial_fmp) raw_headroom)` >>
  simp[w2n_n2w] >> gvs[Abbr `raw_headroom`, MAX_DEF] >> decide_tac
QED

Theorem call_raw_variant_headroom:
  !tops rp unit am tx vs0 fmp vi.
    lower_vyper_runtime_unit tops rp = SOME unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs0 /\
    vs0.vs_fmp = vs0.vs_initial_fmp /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    raw_variant fmp vi vs0 /\
    LENGTH vi.vs_outcomes < 2 ** 64 /\
    outcomes_accounts_typed (SOME vi.vs_outcomes) /\
    LENGTH vi.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !fn inst s. raw_reachable vi unit.cu_context fn inst s ==>
      dalloca_fmp_headroom inst s
Proof
  rpt gen_tac >> strip_tac >>
  `initial_venom_state_rel tops am tx vi` by
    metis_tac[raw_variant_initial_venom_state_rel] >>
  `~vi.vs_halted` by fs[initial_venom_state_rel_def] >>
  `vi.vs_initial_fmp = fmp /\ vi.vs_fmp = fmp` by
    (qpat_assum `raw_variant fmp vi vs0`
       (mp_tac o AP_TERM ``\st:venom_state. (st.vs_initial_fmp, st.vs_fmp)``
               o REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
     simp[] >> metis_tac[]) >>
  `blueprint_create_root =
     (\e. ?ty b s r ks es d.
       e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d)` by
    simp[FUN_EQ_THM, blueprint_create_root_def] >>
  Cases_on `runtime_blueprint_free tops`
  >- (qspecl_then [`tops`, `rp`, `unit`, `w2n vs0.vs_initial_fmp`,
                   `am`, `tx`, `fmp`, `vs0`, `vi`]
        mp_tac lower_vyper_runtime_unit_dynamic_peak_memory_bound >>
      impl_tac
      >- (qpat_assum `blueprint_create_root = _`
            (fn th => PURE_REWRITE_TAC [GSYM th]) >>
          asm_rewrite_tac[wordsTheory.n2w_w2n] >>
          qpat_assum `runtime_blueprint_free _`
            (mp_tac o REWRITE_RULE [runtime_blueprint_free_def]) >> simp[]) >>
      strip_tac >> metis_tac[raw_reachable_dalloca_headroom_from_peak]) >>
  `?art. check_contract F am.layouts tx.target [(NONE,tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  `?vis mut nr rr name args dflts ret body.
     MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
     vis <> Deploy /\
     (supported_stmts_expr_exists
        (\e. ?ty b s r ks es d.
               e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d) body \/
      EXISTS (supported_expr_exists
        (\e. ?ty b s r ks es d.
               e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d)) dflts)` by
    (qpat_x_assum `~runtime_blueprint_free _` mp_tac >>
     simp_tac bool_ss [runtime_blueprint_free_def, EVERY_MEM, EXISTS_MEM] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  qspecl_then [`tops`, `rp`, `unit`, `am.layouts`, `tx.target`, `art`]
    mp_tac lower_vyper_runtime_unit_blueprint_raw_fmp >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >>
  disch_then (qspecl_then [`am`, `tx`, `vi`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> simp[]
QED

Theorem call_state_rel_calldata_bound:
  call_state_rel tops bc am tx es ==> LENGTH tx.calldata < 2 ** 64
Proof
  rw[call_state_rel_def, evm_state_ok_def, frame_tx_rel_def,
     vfmCalldataBoundTheory.calldata_bounded_def] >> gvs[] >>
  metis_tac[vfmBufferTheory.LENGTH_buffer_to_list]
QED

Theorem call_entry_raw_headroom:
  !own tops rp unit am tx txp bc es prog prog' cplan vs0 fmp.
    lower_vyper_runtime_unit tops rp = SOME unit /\
    source_typing_ok tops am txp /\ call_state_rel tops bc am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    vs0 = (if own then opt_entry_state_own prog prog' cplan es
           else opt_entry_state prog prog' cplan es) /\
    txp = tx with code := vs0.vs_code /\
    initial_venom_state_rel tops am txp vs0 /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp ==>
    !vi fn inst s. raw_variant fmp vi vs0 /\
       raw_reachable vi unit.cu_context fn inst s ==>
       dalloca_fmp_headroom inst s
Proof
  rpt gen_tac >> strip_tac >>
  `source_deployment_rel tops am txp` by
    fs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def,
       source_deployment_rel_def, layouts_agree_def] >>
  `vs0.vs_fmp = vs0.vs_initial_fmp /\
    vs0.vs_outcomes = MAP SND (call_trace es)` by
    (Cases_on `own` >> gvs[opt_entry_state_own_def, opt_entry_state_def,
                            entry_venom_state_def]) >>
  `outcomes_accounts_typed (SOME vs0.vs_outcomes)` by
    (`wf_state es /\ balance_bounded (2 ** 256 - 1) es /\
      returndata_bounded es` by fs[call_state_rel_def, evm_state_ok_def] >>
     drule_all call_trace_outcomes_bounded >>
     simp[outcomes_accounts_typed_def, EVERY_MEM]) >>
  rpt gen_tac >> strip_tac >>
  `vs0.vs_call_ctx.cc_calldata = tx.calldata` by
    gvs[initial_venom_state_rel_def, venom_env_rel_def,
       loweringStateRelDefsTheory.call_ctx_rel_def] >>
  `LENGTH vi.vs_call_ctx.cc_calldata < 2 ** 64` by
    metis_tac[call_state_rel_calldata_bound, raw_variant_call_ctx] >>
  `vi.vs_outcomes = vs0.vs_outcomes` by metis_tac[raw_variant_outcomes] >>
  qspecl_then [`tops`, `rp`, `unit`, `am`, `txp`, `vs0`, `fmp`, `vi`]
    mp_tac call_raw_variant_headroom >>
  fs[] >> metis_tac[]
QED
