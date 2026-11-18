(* The deployment body's no-wrap input at the raw pointer above the
   immutable and static allocation regions. *)
Theory deployPeakMemoryCallerCheck
Ancestors
  runtimePeakMemoryCallerCheck ctorDeployDefs
  deployUnitProducers e2eDeployDefs e2eDefs e2eEntry callRawVariant
  compileVyper vyperCompiler lowerDloadDefs stackPlanGen
  immSectionDead o1PassContract exprSimHypsDefs
  fmpLowerSequenceExec unitTransformDefs fragGasPath
  contextRawReachable contextCodegenRel venomExecProofs venomInst venomState
  venomLayout vyperAST supportedStmtTraverse supportedExprTraverse
  vfmExecutionProp words list

val _ = Parse.hide "body";
val _ = Parse.hide "tops";

val lower_vyper_deploy_unit_dynamic_peak_memory_bound_quote : term = “
  !policy tops deploy_bc runtime_bc rpolicy (dunit:compilation_unit) dout
   prog cplan (cp_fmp:num) am tx es (fmp:bytes32) vs vs0.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    (!vis mut nr rr name args dflts ret body.
       MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
       (vis = Deploy \/ vis = Internal) ==>
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
    vs = deploy_entry_state prog cplan tops es /\
    vs.vs_initial_fmp = n2w cp_fmp /\
    vs.vs_fmp = n2w cp_fmp /\
    cp_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    raw_variant fmp vs0 vs /\
    LENGTH vs0.vs_outcomes < 2 ** 64 /\
    outcomes_accounts_typed (SOME vs0.vs_outcomes) /\
    LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !fn i s.
      raw_reachable vs0 dunit.cu_context fn i s ==>
      s.vs_initial_fmp = fmp /\
      w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
      fmp_frontier_rel cp_fmp (w2n fmp)
        (cp_fmp + (w2n s.vs_fmp - w2n fmp)) s.vs_fmp /\
      (i.inst_opcode = DALLOCA ==>
       w2n s.vs_fmp <= w2n fmp + 2 ** 64 * 2 ** 64 /\
       !sz_op sz.
         i.inst_operands = [sz_op] /\ eval_operand sz_op s = SOME sz ==>
         w2n s.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256))
”;

val deploy_ctor_frag_dalloca_no_wrap_quote : term = “
  !policy tops deploy_bc runtime_bc rpolicy (dunit:compilation_unit) dout
   prog cplan (cp_fmp:num) am tx es (fmp:bytes32) vs vs0
   func (s0:venom_state).
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    (!vis mut nr rr name args dflts ret body.
       MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
       (vis = Deploy \/ vis = Internal) ==>
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
    vs = deploy_entry_state prog cplan tops es /\
    vs.vs_initial_fmp = n2w cp_fmp /\
    vs.vs_fmp = n2w cp_fmp /\
    cp_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    raw_variant fmp vs0 vs /\
    LENGTH vs0.vs_outcomes < 2 ** 64 /\
    outcomes_accounts_typed (SOME vs0.vs_outcomes) /\
    LENGTH vs0.vs_call_ctx.cc_calldata < 2 ** 64 /\
    dunit.cu_context.ctx_entry = SOME "__deploy" /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__deploy" /\
    gas_path dunit.cu_context func
      (vs0 with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                   vs_inst_idx := 0 |>) 0 (OK s0) ==>
    !fn inst s.
      frag_reachable dunit.cu_context func s0 fn inst s ==>
      s.vs_initial_fmp = fmp /\
      w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
      fmp_frontier_rel cp_fmp (w2n fmp)
        (cp_fmp + (w2n s.vs_fmp - w2n fmp)) s.vs_fmp /\
      dalloca_no_wrap inst s /\
      (inst.inst_opcode = DALLOCA ==>
       w2n s.vs_fmp <= w2n fmp + 2 ** 64 * 2 ** 64)
”;

Theorem deploy_peak_memory_d3_from_d1:
  ^lower_vyper_deploy_unit_dynamic_peak_memory_bound_quote ==>
  ^deploy_ctor_frag_dalloca_no_wrap_quote
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `lowering_context_ok dunit.cu_context` by
    (fs[deploy_phases_def] >> metis_tac[lower_vyper_deploy_unit_context_ok]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[lowering_context_entry_no_phis, lookup_function_MEM] >>
  mp_tac (Q.INST [`ctx` |-> `dunit.cu_context`, `fn` |-> `func`,
                  `name` |-> `"__deploy"`, `lbl` |-> `"__deploy"`,
                  `raw` |-> `vs0`, `n` |-> `0`] entry_gas_path_raw_reachable) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `raw_reachable vs0 dunit.cu_context fn inst s` by
    metis_tac[raw_reachable_from_fragment] >>
  qpat_x_assum `!policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan
                      cp_fmp am tx es fmp vs vs0. _`
    (qspecl_then [`policy`, `tops`, `deploy_bc`, `runtime_bc`, `rpolicy`,
      `dunit`, `dout`, `prog`, `cplan`, `cp_fmp`, `am`, `tx`, `es`,
      `fmp`, `vs`, `vs0`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qspecl_then [`fn`, `inst`, `s`] mp_tac) >>
  asm_rewrite_tac[dalloca_no_wrap_def] >> metis_tac[]
QED

(* The constructor entry prefix supplies the endpoint consumed by
   ctorDeployBodyJoint when it applies the constructor's stmt_frag_full. *)
Theorem deploy_ctor_body_peak_memory_from_entry:
  ^deploy_ctor_frag_dalloca_no_wrap_quote /\
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_typing_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  (!vis mut nr rr name args dflts ret body.
     MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
     (vis = Deploy \/ vis = Internal) ==>
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
  LENGTH (call_trace es) < 2 ** 64 /\
  w2n (deploy_entry_state prog cplan tops es).vs_initial_fmp <= w2n fmp /\
  w2n fmp < 2 ** 254 /\
  imm_len tops + unit_alloca_budget dunit.cu_context +
    32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
  raw_variant fmp raw (deploy_entry_state prog cplan tops es) /\
  dunit.cu_context.ctx_entry = SOME "__deploy" /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__deploy" /\
  gas_path dunit.cu_context func
    (raw with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0 |>) 0 (OK s0) ==>
  !fn inst s. frag_reachable dunit.cu_context func s0 fn inst s ==>
    dalloca_no_wrap inst s
Proof
  strip_tac >>
  `cplan.cp_initial_fmp < 2 ** 254` by
    (fs[deploy_phases_def, generate_context_plan_def] >>
     drule generate_context_plan_with_headroom >> simp[]) >>
  `cplan.cp_initial_fmp <= w2n fmp` by
    (fs[deploy_entry_state_def, entry_venom_state_def,
        w2n_n2w, dimword_def, dimindex_256] >> decide_tac) >>
  `raw.vs_outcomes = MAP SND (call_trace es)` by
    (drule raw_variant_outcomes >>
     simp[deploy_entry_state_def, entry_venom_state_frame_fields]) >>
  `outcomes_accounts_typed (SOME raw.vs_outcomes)` by
    (`wf_state es /\ balance_bounded (2 ** 256 - 1) es /\ returndata_bounded es` by
       fs[deploy_state_rel_def] >>
     drule_all call_trace_outcomes_bounded >>
     simp[outcomes_accounts_typed_def, EVERY_MEM]) >>
  `LENGTH raw.vs_call_ctx.cc_calldata < 2 ** 64` by
    (drule raw_variant_call_ctx >>
     fs[deploy_entry_state_def, entry_venom_state_def, deploy_state_rel_def]) >>
  `LENGTH raw.vs_outcomes < 2 ** 64` by
    (qpat_assum `raw.vs_outcomes = _` (fn th => REWRITE_TAC [th, LENGTH_MAP]) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `!policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan
                      cp_fmp am tx es fmp vs vs0 func s0. _`
    (qspecl_then [`policy`, `tops`, `deploy_bc`, `runtime_bc`, `rpolicy`,
      `dunit`, `dout`, `prog`, `cplan`, `cplan.cp_initial_fmp`, `am`,
      `tx`, `es`, `fmp`, `deploy_entry_state prog cplan tops es`,
      `raw`, `func`, `s0`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
        simp[deploy_entry_state_def, entry_venom_state_def]]) >>
  disch_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> simp[]
QED
