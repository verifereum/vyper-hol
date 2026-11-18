(* Discharge the runtime body's no-wrap input at the raw pointer selected
   by the bounded call entry. H5 is a hypothesis in the caller check. *)
Theory runtimePeakMemoryCallerCheck
Ancestors
  e2eCorrectness e2eDefs e2eEntry callRawVariant stackPlanGen
  fragGasPath fragExec contextRawReachable contextCodegenRel
  contextCodegenRelProps dfAnalyzeProofs venomExecProofs venomExecSemantics
  venomFnInstsProofs venomInst venomState vyperLoweringCorrect
  vyperCompiler loweringStateRelDefs o1PassContract unitTransformDefs
  fmpLowerSequenceExec venomLayout vyperAST supportedStmtTraverse
  supportedExprTraverse vfmExecutionProp exprSimHypsDefs words list

val _ = Parse.hide "body";
val _ = Parse.hide "cp";
val _ = Parse.hide "tops";

val lower_vyper_runtime_unit_dynamic_peak_memory_bound_quote : term = “
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
”;

Theorem gas_path_edge_raw_reachable[local]:
  gas_path_edge ctx fn s n (OK t) /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!i. active_inst fn i s ==> raw_reachable raw ctx fn i s) /\
  active_inst fn inst t ==>
  raw_reachable raw ctx fn inst t
Proof
  strip_tac >>
  qpat_x_assum `gas_path_edge _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_path_edge_def]) >>
  `active_inst fn inst' s` by metis_tac[lookup_instruction_active] >>
  `raw_reachable raw ctx fn inst' s` by metis_tac[] >>
  gvs[exit_result_def]
  >- metis_tac[raw_reachable_next]
  >- metis_tac[enters_block_def, raw_reachable_block]
  >- (`~(jump_to lbl s).vs_halted /\ (jump_to lbl s).vs_inst_idx = 0` by
        simp[jump_to_def] >>
      `?target. lookup_block (jump_to lbl s).vs_current_bb fn.fn_blocks =
                 SOME target` by
        (qpat_x_assum `active_inst fn inst (jump_to lbl s)`
           (qx_choose_then `target` strip_assume_tac o
            REWRITE_RULE [active_inst_def]) >>
         mp_tac (Q.SPECL [`(jump_to lbl s).vs_current_bb`, `fn.fn_blocks`]
           lookup_block_exists) >>
         impl_tac >- (simp[MEM_MAP] >> qexists_tac `target` >> simp[]) >>
         disch_then (qx_choose_then `found` strip_assume_tac) >>
         qexists_tac `found` >> first_assum ACCEPT_TAC) >>
      `phi_prefix_length target.bb_instructions = 0` by
        metis_tac[lookup_block_MEM] >>
      `enters_block fn (jump_to lbl s) (jump_to lbl s)` by
        (simp[enters_block_def, eval_phis_no_phi] >>
         simp[venom_state_component_equality]) >>
      metis_tac[raw_reachable_block]) >>
  Cases_on `step_inst fuel ctx inst' s` >> gvs[exit_result_def]
QED

Theorem gas_path_raw_reachable[local]:
  !ctx fn s n r. gas_path ctx fn s n r ==>
    !t raw. r = OK t /\
      (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
      (!i. active_inst fn i s ==> raw_reachable raw ctx fn i s) ==>
      !i. active_inst fn i t ==> raw_reachable raw ctx fn i t
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >>
      first_x_assum irule >> simp[] >>
      metis_tac[gas_path_edge_raw_reachable]) >>
  simp[exit_result_def] >> rpt strip_tac >>
  Cases_on `r` >> gvs[exit_result_def]
QED

Theorem entry_gas_path_raw_reachable:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  gas_path ctx fn
    (raw with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
    n (OK s0) ==>
  !i. active_inst fn i s0 ==> raw_reachable raw ctx fn i s0
Proof
  strip_tac >>
  qabbrev_tac `start = raw with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                                  vs_inst_idx := 0|>` >>
  `enters_block fn start start` by
    (`?bb. lookup_block lbl fn.fn_blocks = SOME bb` by
       (qpat_x_assum `fn_entry_label fn = _` mp_tac >>
        Cases_on `fn.fn_blocks` >>
        simp[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
     `phi_prefix_length bb.bb_instructions = 0` by metis_tac[lookup_block_MEM] >>
     simp[enters_block_def, eval_phis_no_phi, Abbr `start`]) >>
  metis_tac[gas_path_raw_reachable, raw_reachable_entry]
QED

Theorem raw_reachable_from_fragment:
  !ctx fn0 s0 fn i s.
    frag_reachable ctx fn0 s0 fn i s ==>
    !raw. (!j. active_inst fn0 j s0 ==> raw_reachable raw ctx fn0 j s0) ==>
    raw_reachable raw ctx fn i s
Proof
  ho_match_mp_tac frag_reachable_ind >>
  rpt conj_tac >> rpt strip_tac >> metis_tac[raw_reachable_rules]
QED

Theorem lowering_context_entry_no_phis:
  lowering_context_ok ctx /\ MEM func ctx.ctx_functions /\ MEM bb func.fn_blocks ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  rpt strip_tac >> irule no_phis_phi_prefix_length_zero >>
  fs[lowering_context_ok_def, ptr_ok_check_def, EVERY_MEM] >>
  metis_tac[MEM_fn_insts]
QED

(* Selected entries, fallbacks and entries after the lock provide the same
   zero-mark prefix to the dalloca_no_wrap premise of stmt_frag_full. *)
Theorem runtime_body_peak_memory_from_entry:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  (!fn i s. raw_reachable raw unit.cu_context fn i s ==>
    dalloca_no_wrap i s) /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__entry" /\
  gas_path unit.cu_context func
    (raw with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                vs_inst_idx := 0|>) 0 (OK s0) ==>
  !fn inst s. frag_reachable unit.cu_context func s0 fn inst s ==>
    dalloca_no_wrap inst s
Proof
  strip_tac >>
  drule_then (assume_tac o CONJUNCT1) lower_vyper_runtime_unit_context_entry >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[lowering_context_entry_no_phis, lookup_function_MEM] >>
  mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `fn` |-> `func`,
                  `name` |-> `"__entry"`, `lbl` |-> `"__entry"`,
                  `n` |-> `0`] entry_gas_path_raw_reachable) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  metis_tac[raw_reachable_from_fragment]
QED

Theorem bounded_context_plan_initial_fmp[local]:
  generate_context_plan ctx = SOME cp ==> cp.cp_initial_fmp < 2 ** 254
Proof
  simp[generate_context_plan_def] >> strip_tac >>
  drule generate_context_plan_with_headroom >> simp[]
QED

Theorem bounded_call_entry_peak_memory:
  ^lower_vyper_runtime_unit_dynamic_peak_memory_bound_quote /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  call_state_rel tops (assemble prog') am tx es /\
  source_typing_ok tops am txp /\
  generate_context_plan out.po_unit.cu_context = SOME cp /\
  opt = opt_entry_state prog prog' cp es /\
  txp = tx with code := opt.vs_code /\
  LENGTH (call_trace es) < 2 ** 64 /\
  w2n opt.vs_initial_fmp <= w2n fmp /\
  w2n fmp < 2 ** 254 /\
  unit_alloca_budget unit.cu_context +
    32 * ctx_dload_count unit.cu_context <= w2n fmp /\
  raw_variant fmp raw opt /\
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
       d0) dflts) ==>
  LENGTH raw.vs_call_ctx.cc_calldata < 2 ** 64 /\
  outcomes_accounts_typed (SOME raw.vs_outcomes) /\
  LENGTH raw.vs_outcomes < 2 ** 64 /\
  raw.vs_fmp = raw.vs_initial_fmp /\
  w2n raw.vs_initial_fmp < 2 ** 254 /\
  unit_alloca_budget unit.cu_context +
    32 * ctx_dload_count unit.cu_context <= w2n raw.vs_initial_fmp /\
  (!fn inst s. raw_reachable raw unit.cu_context fn inst s ==>
     dalloca_no_wrap inst s) /\
  (!func s0.
     unit.cu_context.ctx_entry = SOME "__entry" /\
     lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
     fn_entry_label func = SOME "__entry" /\
     gas_path unit.cu_context func
       (raw with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                   vs_inst_idx := 0|>) 0 (OK s0) ==>
     !fn inst s. frag_reachable unit.cu_context func s0 fn inst s ==>
       dalloca_no_wrap inst s)
Proof
  strip_tac >>
  `initial_venom_state_rel tops am txp opt` by
    metis_tac[opt_entry_initial_venom_state_rel] >>
  `source_deployment_rel tops am txp` by
    gvs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def,
        source_deployment_rel_def, layouts_agree_def] >>
  `opt.vs_initial_fmp = n2w cp.cp_initial_fmp /\
   opt.vs_fmp = n2w cp.cp_initial_fmp` by
    fs[opt_entry_state_def, entry_venom_state_def] >>
  `cp.cp_initial_fmp <= w2n fmp` by
    (drule bounded_context_plan_initial_fmp >> strip_tac >>
     fs[wordsTheory.w2n_n2w, wordsTheory.dimword_def,
        fcpLib.INDEX_CONV ``dimindex(:256)``] >>
     decide_tac) >>
  `raw.vs_outcomes = MAP SND (call_trace es)` by
    (drule raw_variant_outcomes >>
     simp[opt_entry_state_def, entry_venom_state_frame_fields]) >>
  `outcomes_accounts_typed (SOME raw.vs_outcomes)` by
    (`wf_state es /\ balance_bounded (2 ** 256 - 1) es /\ returndata_bounded es` by
       fs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def,
          evm_state_ok_def] >>
     drule_all call_trace_outcomes_bounded >>
     simp[outcomes_accounts_typed_def, EVERY_MEM]) >>
  `LENGTH raw.vs_call_ctx.cc_calldata < 2 ** 64` by
    metis_tac[raw_variant_opt_entry_calldata_bound] >>
  `LENGTH raw.vs_outcomes < 2 ** 64` by
    (qpat_assum `raw.vs_outcomes = _` (fn th => REWRITE_TAC [th, LENGTH_MAP]) >>
     first_assum ACCEPT_TAC) >>
  `raw.vs_fmp = fmp /\ raw.vs_initial_fmp = fmp` by
    (qpat_assum `raw_variant fmp raw opt`
       (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
     disch_then (mp_tac o Q.AP_TERM `\s:venom_state. (s.vs_fmp,s.vs_initial_fmp)`) >>
     simp[] >> strip_tac >> gvs[]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `!tops rpolicy unit cp_fmp am tx fmp vs vs0. _`
    (qspecl_then [`tops`, `rpolicy`, `unit`, `cp.cp_initial_fmp`, `am`,
                  `txp`, `fmp`, `opt`, `raw`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_tac >>
  `!fn inst s. raw_reachable raw unit.cu_context fn inst s ==>
     dalloca_no_wrap inst s` by
    (rpt gen_tac >> strip_tac >>
     first_x_assum drule >> simp[dalloca_no_wrap_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  mp_tac runtime_body_peak_memory_from_entry >>
  impl_tac >- asm_rewrite_tac[] >> simp[]
QED
