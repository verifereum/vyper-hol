(* The constructor body and the deployment wrapper use the same source
   outcome oracle and the same finite storage observation. *)
Theory entryCreateDeploySelected
Ancestors
  entryCreateBodyCut entryCreateNativeCut entryCreateNativeResume
  e2eDeployRawFmp deployUnitProducers acceptedContextPhi
  ctorDeployLoweringArms ctorDeployLoweringEntry ctorDeployBodySimulation
  ctorDeployLoweringFrame ctorDeployLoweringDefs fragGasOrigin fragExec
  vyperInterpreter vyperState vyperStorageFootprint e2eDeployDefs ctorDeployDefs
  venomState venomExecSemantics deployUnitExecution venomInstProofs
  fragGasPath venomExecProofs dftGasFromListTraceDefs blockSimHelpers list arithmetic
  ctorDeployLoweringPrefix ctorDeployLoweringCode vyperTypeDeploymentMachine
  e2eEntry o1PassContract vyperCompiler venomInst vyperTypeContractSoundness
  immutableDeployExecution emitHelperProps algebraicOptCmpBlockProofs compileEnv
  entryCreateReject asmOptimizer e2eDefs unitTransformDefs deployDynamicMemory
  loweringShapeDefs lowerDloadDefs ctorDeployRunBounded ctorDeployLoweringReturn
  ctorDeployLoweringEntryPrefix ctorDeployLoweringEntryTransport ctorDeployBodyShadow
  bodyFullShadowBodyInv ptrDiscipline stmtSimDefs bodyPtrDefs fragExecPtr
  gasShadowUnit gasShadowState gasShadowStmtEnv exprLowering vyperState fragGasPathMem
  contextRawReachable allocaBudgetProps passSimulationDefs contextCodegenRel
  deployBodyReachability ctorDeployShape

val _ = Parse.hide "body";
val _ = Parse.hide "base";

Theorem selected_deploy_trace_failure[local]:
  deploy_source_ok tops am tx /\ tx.function_name = "__init__" /\
  deploy_ctor_start tops am tx (mut,F,source_body,am_c,es0) /\
  (!gx. eval_stmts (deploy_evaluation_context tops am tx) body
          (es0 with <|gas_obs := gx; outcomes := SOME os|>) =
        eval_stmts (deploy_evaluation_context tops am tx) source_body
          (es0 with <|gas_obs := gx; outcomes := SOME os|>)) /\
  create_body_cut explicit tops (deploy_evaluation_context tops am tx)
    (initial_state am []) (eval_stmts (deploy_evaluation_context tops am tx) body)
    (es0 with outcomes := SOME os,sb) (before,(key,fn,inst,s)) /\
  (!gs. deploy_storage_ok tops am tx os gs) /\
  (!gs. ~deploy_source_exempt tops
    (load_contract (SOME os) gs am tx [(NONE,tops)] [])) /\
  (!gs. load_contract (SOME os) gs am tx [(NONE,tops)] [] <>
    INR (Error (RuntimeError "create initcode too large"))) ==>
  inst_create_size_ok inst s
Proof
  strip_tac >> CCONTR_TAC >>
  qabbrev_tac `cx = deploy_evaluation_context tops am tx` >>
  qabbrev_tac `gx = gas_explicit (create_cut_marks explicit before) sb.vs_gas_readings` >>
  Cases_on `eval_stmts cx source_body
    (es0 with <|gas_obs := gx; outcomes := SOME os|>)` >>
  rename1 `_ = (res,ee)` >>
  qunabbrev_tac `cx` >>
  drule_all deploy_ctor_source_trace >> strip_tac >>
  rule_assum_tac (SIMP_RULE std_ss [vyperStateTheory.evaluation_state_fupdcanon]) >>
  `deploy_storage_ok tops am tx os gx` by simp[] >>
  drule deploy_storage_ok_domain >> simp[deploy_storage_trace_def] >> strip_tac >>
  `valid_horizon (deploy_evaluation_context tops am tx) (initial_state am [])
     (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `create_cut_failure tops res` by
    (qpat_x_assum `create_body_cut _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [create_body_cut_def]) >>
     simp[] >>
     disch_then (qspecl_then [`storage_trace_horizon ee.storage_trace`, `[]`, `res`, `ee`] mp_tac) >>
     qpat_assum `Abbrev (gx = _)`
       (fn eq => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq)]) >>
     simp[vyperStateTheory.evaluation_state_fupdcanon]) >>
  qpat_x_assum `!gs. ~deploy_source_exempt _ _` (qspec_then `gx` mp_tac) >>
  qpat_x_assum `!gs. load_contract _ _ _ _ _ _ <> _` (qspec_then `gx` mp_tac) >>
  gvs[create_cut_failure_def, load_contract_def, deploy_ctor_finish_def,
      deploy_source_exempt_def]
QED

Theorem selected_deploy_terminal[local]:
  lowering_context_ok unit.cu_context /\
  deploy_unit_execution_correct_with shadow_ctx marks tops runtime_bc am tx unit vi /\
  (!gs. deploy_storage_ok tops am tx vi.vs_outcomes gs) /\
  (!gs. ~deploy_source_exempt tops
    (load_contract (SOME vi.vs_outcomes) gs am tx [(NONE,tops)] [])) ==>
  ?func rv fuel src obs.
    unit.cu_context.ctx_entry = SOME "__deploy" /\
    lookup_function "__deploy" unit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__deploy" /\
    gas_origin_path T (gas_explicit_sites unit.cu_context shadow_ctx)
      unit.cu_context func
      (vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)
      marks rv /\
    exit_result rv /\ run_context fuel unit.cu_context vi = rv /\
    (!err. rv <> Error err) /\
    (!tail. load_contract_trace (SOME vi.vs_outcomes)
      (gas_explicit marks vi.vs_gas_readings ++ tail) am tx [(NONE,tops)] [] = (src,obs)) /\
    storage_trace_domain (deploy_evaluation_context tops am tx) (initial_state am []) obs
Proof
  strip_tac >>
  qpat_x_assum `deploy_unit_execution_correct_with _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [deploy_unit_execution_correct_with_def])
  >- (qpat_x_assum `!tail. ~_` (qspec_then `[]` mp_tac) >> simp[])
  >- (qpat_assum `!tail. load_contract_trace _ _ _ _ _ _ = _`
        (qspec_then `[]` (assume_tac o SIMP_RULE std_ss [listTheory.APPEND_NIL])) >>
      qpat_x_assum `!gs. ~deploy_source_exempt _ _`
        (qspec_then `gas_explicit marks vi.vs_gas_readings` mp_tac) >>
      simp[load_contract_def]) >>
  drule_all gas_origin_path_events >> strip_tac >>
  qexistsl [`func`, `r`, `SUC fuel`, `src`, `obs`] >> simp[] >> conj_tac
  >- ( simp[run_context_def, run_function_def] >>
       drule_all lowering_context_ok_block_phi >> strip_tac >>
       drule_all run_blocks_run_from_no_phi >> simp[venom_state_fupdfupds]) >>
  Cases_on `r` >> gvs[exit_result_def]
QED

(* A successful caller edge cannot cross a native error. At a terminal
   fuel budget it preserves the actual visit list up to the next cursor. *)
Theorem deploy_edge_trace_continue[local]:
  gas_path_edge ctx fn s n (OK t) /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  (!err. run_from fuel ctx fn s <> Error err) ==>
  ?k d' front.
    run_from fuel ctx fn s = run_from k ctx fn t /\
    create_trace_from p d fuel ctx fn s =
      front ++ create_trace_from p d' k ctx fn t
Proof
  strip_tac >>
  qpat_x_assum `gas_path_edge _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss [gas_path_edge_def])
  >> gvs[exit_result_def]
  >- suspend "within"
  >- suspend "enter"
  >- suspend "jump"
  >> (Cases_on `step_inst fuel' ctx inst s` >> gvs[exit_result_def])
QED

Resume deploy_edge_trace_continue[within]:
  `!err. step_inst fuel ctx inst s <> Error err` by
    (rpt strip_tac >> fs[run_from_def, Once exec_block_def]) >>
  `step_inst fuel ctx inst s = OK t'` by
    (Cases_on `fuel' <= fuel`
     >- (irule (cj 1 fuel_mono) >> simp[] >> qexists `fuel'` >> simp[]) >>
     `fuel <= fuel'` by decide_tac >>
     metis_tac[cj 1 fuel_mono]) >>
  `t'.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
  drule_all create_trace_from_next >> strip_tac >>
  drule_all exec_block_step >> strip_tac >>
  qexistsl [`fuel`, `d`, `((p,d,inst.inst_id),fn,inst,s)::trace_step p d fuel ctx fn inst s`] >>
  simp[run_from_def]
QED

Resume deploy_edge_trace_continue[enter]:
  `!err. step_inst fuel ctx inst s <> Error err` by
    (rpt strip_tac >> fs[run_from_def, Once exec_block_def]) >>
  `step_inst fuel ctx inst s = OK t'` by
    (Cases_on `fuel' <= fuel`
     >- (irule (cj 1 fuel_mono) >> simp[] >> qexists `fuel'` >> simp[]) >>
     `fuel <= fuel'` by decide_tac >>
     metis_tac[cj 1 fuel_mono]) >>
  `exec_block fuel ctx bb s = OK t'` by simp[Once exec_block_def] >>
  namedCases_on `fuel` ["", "small"]
  >- fs[run_from_def, Once run_blocks_def] >>
  `phi_prefix_length target.bb_instructions = 0` by metis_tac[] >>
  `entered = t'` by fs[eval_phis_no_phi] >> gvs[] >>
  `trace_block p d (SUC small) ctx fn bb s =
    ((p,d,inst.inst_id),fn,inst,s)::trace_step p d (SUC small) ctx fn inst s` by
    simp[Once (cj 2 trace_defs)] >>
  `trace_blocks p d (SUC small) ctx fn entered =
    create_trace_from p (SUC d) small ctx fn (entered with vs_inst_idx := 0)` by
    (once_rewrite_tac[cj 3 trace_defs] >> simp[create_trace_from_def]) >>
  `run_blocks (SUC small) ctx fn entered =
    run_from small ctx fn (entered with vs_inst_idx := 0)` by
    (irule run_blocks_run_from_no_phi >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl [`small`, `SUC d`, `((p,d,inst.inst_id),fn,inst,s)::trace_step p d (SUC small) ctx fn inst s`] >>
  simp[run_from_def, Once create_trace_from_def]
QED

Resume deploy_edge_trace_continue[jump]:
  `step_inst fuel ctx inst s = OK (jump_to lbl s)` by metis_tac[step_inst_non_invoke] >>
  `exec_block fuel ctx bb s = OK (jump_to lbl s)` by simp[Once exec_block_def] >>
  `(jump_to lbl s).vs_halted = F` by simp[jump_to_def] >>
  namedCases_on `fuel` ["", "small"] >- fs[run_from_def, Once run_blocks_def] >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- fs[run_from_def, Once run_blocks_def, jump_to_def] >>
  `phi_prefix_length x.bb_instructions = 0` by metis_tac[] >>
  `(jump_to lbl s) with vs_inst_idx := 0 = jump_to lbl s` by
    simp[jump_to_def, venom_state_fupdfupds] >>
  `trace_block p d (SUC small) ctx fn bb s = [((p,d,inst.inst_id),fn,inst,s)]` by
    simp[Once (cj 2 trace_defs), trace_step_noninvoke] >>
  `trace_blocks p d (SUC small) ctx fn (jump_to lbl s) =
   create_trace_from p (SUC d) small ctx fn (jump_to lbl s)` by
    (once_rewrite_tac[cj 3 trace_defs] >> simp[create_trace_from_def, jump_to_def,
                                             eval_phis_no_phi, venom_state_fupdfupds]) >>
  `run_blocks (SUC small) ctx fn (jump_to lbl s) =
   run_from small ctx fn (jump_to lbl s)` by
    (qpat_assum `jump_to lbl s with vs_inst_idx := 0 = _`
       (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >>
     irule run_blocks_run_from_no_phi >> simp[jump_to_def] >> metis_tac[]) >>
  qexistsl [`small`, `SUC d`, `[ ((p,d,inst.inst_id),fn,inst,s) ]`] >>
  simp[run_from_def, Once create_trace_from_def]
QED
Finalise deploy_edge_trace_continue

Theorem deploy_path_trace_continue[local]:
  gas_path ctx fn s n (OK t) /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  (!err. run_from fuel ctx fn s <> Error err) ==>
  ?k d' front.
    run_from fuel ctx fn s = run_from k ctx fn t /\
    create_trace_from p d fuel ctx fn s =
      front ++ create_trace_from p d' k ctx fn t
Proof
  `!ctx fn s n r. gas_path ctx fn s n r ==>
    !t fuel p d. r = OK t /\
      (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
      (!err. run_from fuel ctx fn s <> Error err) ==>
      ?k d' front.
        run_from fuel ctx fn s = run_from k ctx fn t /\
        create_trace_from p d fuel ctx fn s =
          front ++ create_trace_from p d' k ctx fn t` suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> qexistsl [`fuel`, `d`, `[]`] >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[exit_result_def] >>
  drule_all deploy_edge_trace_continue >>
  disch_then (qspecl_then [`p`, `d`] strip_assume_tac) >>
  first_x_assum (qspecl_then [`k`, `p`, `d'`] mp_tac) >> simp[] >>
  impl_tac >- metis_tac[] >> strip_tac >> metis_tac[APPEND_ASSOC]
QED

Theorem selected_deploy_no_start[local]:
  deploy_phases policy tops (assemble prog,runtime_bc) (rpolicy,dunit,dout,prog,cplan) /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops (assemble prog') am tx es /\
  raw_variant fmp vi (opt_deploy_entry_state_own prog prog' cplan tops es) /\
  classify_functions tops = (exts,ints,fb,SOME cf) /\
  (!mut nr body am_c es0. ~deploy_ctor_start tops am tx (mut,nr,body,am_c,es0)) ==>
  ?ss. run_context 1 dunit.cu_context vi = Abort Revert_abort ss
Proof
  strip_tac >> drule_all deploy_prefix_no_start_nonpayable >> strip_tac >>
  drule_all deploy_ctor_code_exists >> strip_tac >>
  drule_all deploy_prefix_selected_guard >> strip_tac >>
  `supported_program tops /\ supported_program_deploy tops` by fs[deploy_source_ok_def] >>
  drule_all deploy_prefix_ctor_entry_label >> strip_tac >>
  `vi.vs_call_ctx.cc_callvalue = n2w tx.value` by
    gvs[raw_variant_def, gas_variant_def, venom_state_component_equality,
        opt_deploy_entry_state_own_def, opt_entry_state_own_def, entry_venom_state_def,
        deploy_state_rel_def, call_context_component_equality] >>
  `tx.value < 2 ** 256` by
    fs[deploy_source_ok_def, deploy_typing_ok_constants_ready, call_tx_well_typed_def] >>
  `vi.vs_call_ctx.cc_callvalue <> 0w` by
    fs[wordsTheory.n2w_11, wordsTheory.dimword_def, arithmeticTheory.LESS_MOD] >>
  irule deploy_prefix_context_guard_abort >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem residual_selected_visit[local]:
  C.ctx_entry = SOME nm /\ lookup_function nm C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  (!label b. lookup_block label fn.fn_blocks = SOME b ==>
      phi_prefix_length b.bb_instructions = 0) /\
  gas_path C fn (vi with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
    n (OK base) /\
  (!err. run_context (SUC fuel) C vi <> Error err) /\
  trace_context (SUC fuel) C vi = before ++ [visit] ==>
  ?k d local_before.
    create_trace_from [] d k C fn base = local_before ++ [visit] /\
    run_from k C fn base = run_context (SUC fuel) C vi
Proof
  strip_tac >>
  qabbrev_tac `entry = vi with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` >>
  `phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  `run_context (SUC fuel) C vi = run_from fuel C fn entry` by
    simp[run_context_def, run_function_def, run_blocks_run_from_no_phi,
         Abbr `entry`, venom_state_fupdfupds] >>
  `trace_context (SUC fuel) C vi = create_trace_from [] 1 fuel C fn entry` by
    (qpat_x_assum `trace_context _ _ _ = before ++ [visit]` kall_tac >>
     simp[trace_context_def, trace_function_def, Abbr `entry`] >>
     once_rewrite_tac[cj 3 trace_defs] >>
     simp[create_trace_from_def, eval_phis_no_phi, venom_state_fupdfupds]) >>
  `!err. run_from fuel C fn entry <> Error err` by metis_tac[] >>
  drule_all deploy_path_trace_continue >>
  disch_then (qspecl_then [`[]`, `1`] strip_assume_tac) >>
  `?bb i. lookup_block base.vs_current_bb fn.fn_blocks = SOME bb /\
           get_instruction bb base.vs_inst_idx = SOME i` by
    (`!err. run_from k C fn base <> Error err` by metis_tac[] >>
     Cases_on `lookup_block base.vs_current_bb fn.fn_blocks` >- fs[run_from_def] >>
     Cases_on `get_instruction x base.vs_inst_idx` >> fs[run_from_def, Once exec_block_def]) >>
  `create_trace_from [] d' k C fn base <> []` by
    simp[create_trace_from_def, Once (cj 2 trace_defs)] >>
  `?local_before. create_trace_from [] d' k C fn base = local_before ++ [visit]` by
    (`LAST (create_trace_from [] d' k C fn base) = visit` by
       (qpat_x_assum `trace_context _ _ _ = before ++ [visit]`
          (mp_tac o AP_TERM ``LAST : list_visit list -> list_visit``) >>
        simp[rich_listTheory.LAST_APPEND_NOT_NIL]) >>
     qexists `FRONT (create_trace_from [] d' k C fn base)` >>
     metis_tac[APPEND_FRONT_LAST]) >>
  qexistsl [`k`, `d'`, `local_before`] >> simp[]
QED

Theorem epilogue_exec_result[local]:
  !pre s. DROP s.vs_inst_idx bb.bb_instructions = pre ++ [r] ++ tail /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; MCOPY; CODECOPY]) pre /\
  r.inst_opcode = RETURN ==>
  (?e. exec_block fuel ctx bb s = Error e) \/ (?t. exec_block fuel ctx bb s = Halt t)
Proof
  Induct >> rpt gen_tac >> strip_tac >> gvs[]
  >- (`get_instruction bb s.vs_inst_idx = SOME r` by
        metis_tac[algebraicOptCmpBlockProofsTheory.ao_cmp_get_instruction_drop] >>
      `(?e. step_inst_base r s = Error e) \/ (?t. step_inst_base r s = Halt t)` by
        (Cases_on `step_inst_base r s` >> simp[] >>
         qpat_x_assum `step_inst_base r s = _` mp_tac >>
         simp[step_inst_base_opcode_eqs] >> rpt CASE_TAC >> gvs[]) >>
      pop_assum strip_assume_tac
      >- (disj1_tac >> simp[Once exec_block_def, step_inst_non_invoke]) >>
      disj2_tac >> simp[Once exec_block_def, step_inst_non_invoke]) >>
  `get_instruction bb s.vs_inst_idx = SOME h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre ++ [r] ++ tail` by
    metis_tac[algebraicOptCmpBlockProofsTheory.ao_cmp_get_instruction_drop] >>
  `h.inst_opcode <> INVOKE /\ ~is_terminator h.inst_opcode` by
    fs[is_terminator_def] >>
  `(?u. step_inst fuel ctx h s = OK u) \/ (?e. step_inst fuel ctx h s = Error e)` by
    (simp[step_inst_non_invoke] >> Cases_on `step_inst_base h s` >> simp[] >>
     qpat_x_assum `step_inst_base h s = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, exec_alloca_def, exec_pure2_def] >>
     rpt CASE_TAC >> gvs[]) >>
  pop_assum strip_assume_tac >>
  (FIRST [qpat_assum `step_inst _ _ _ _ = Error _` (K disj1_tac) >>
            simp[Once exec_block_def] >> NO_TAC,
          rename1 `step_inst _ _ _ _ = OK u` >>
          first_x_assum (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
          simp[] >> strip_tac >>
          FIRST [qpat_assum `exec_block _ _ _ _ = Error _` (K disj1_tac), disj2_tac] >>
          simp[Once exec_block_def]])
QED

(* No state assumptions about the wrapper's memory are needed: it may
   return or error, but it cannot be the terminal exceptional CREATE. *)
Theorem deploy_epilogue_no_create_abort[local]:
  compile_constructor_epilogue rt cap imm ex = ((),fin) /\
  fn_has_code ex fin f /\ ex.cs_current_insts = [] /\
  s.vs_current_bb = ex.cs_current_bb /\ s.vs_inst_idx = 0 ==>
  run_from k C f s <> Abort ExHalt_abort target
Proof
  strip_tac >> `~block_is_terminated ex` by simp[block_is_terminated_def] >>
  `s.vs_inst_idx = LENGTH ex.cs_current_insts` by simp[] >>
  drule_all compile_constructor_epilogue_code_placement >> simp[] >> strip_tac >>
  drule compile_constructor_epilogue_terminal_shape >> strip_tac >>
  fs[rich_listTheory.IS_PREFIX_APPEND] >>
  `(?e. exec_block k C bb s = Error e) \/ (?t. exec_block k C bb s = Halt t)` by
    (irule epilogue_exec_result >>
     qexistsl [`pre`, `mk_inst id RETURN [dst;szop] []`, `l`] >> simp[mk_inst_def]) >>
  gvs[run_from_def]
QED

Theorem deploy_normal_exit_no_create_abort[local]:
  emit_inst JMP [Label exit_lbl] [] sb = ((),sj) /\ fn_has_code sb sj f /\
  ex.cs_current_bb = exit_lbl /\ ex.cs_current_insts = [] /\
  compile_constructor_epilogue rt cap imm ex = ((),fin) /\ fn_has_code ex fin f /\
  (!lbl bb. lookup_block lbl f.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  run_from k C f s <> Abort ExHalt_abort target
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  `step_inst k C (mk_inst sb.cs_next_id JMP [Label exit_lbl] []) s =
   OK (jump_to exit_lbl s)` by simp[step_inst_non_invoke, Once step_inst_base_def, mk_inst_def] >>
  `exec_block k C bb s = OK (jump_to exit_lbl s)` by
    (once_rewrite_tac[exec_block_def] >>
     simp[] >> simp[is_terminator_def, mk_inst_def, jump_to_def]) >>
  simp[run_from_def, jump_to_def] >>
  Cases_on `k` >- simp[Once run_blocks_def] >>
  Cases_on `lookup_block exit_lbl f.fn_blocks` >- simp[Once run_blocks_def] >>
  `phi_prefix_length x.bb_instructions = 0` by metis_tac[] >>
  `lookup_block (jump_to exit_lbl s).vs_current_bb f.fn_blocks = SOME x` by
    simp[jump_to_def] >>
  `run_blocks (SUC n) C f (jump_to exit_lbl s) =
   run_from n C f ((jump_to exit_lbl s) with vs_inst_idx := 0)` by
    (irule run_blocks_run_from_no_phi >> goal_assum (drule_at Any) >> simp[]) >>
  `run_from n C f (jump_to exit_lbl s) <> Abort ExHalt_abort target` by
    (irule deploy_epilogue_no_create_abort >> simp[jump_to_def] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  gvs[jump_to_def]
QED

(* The body producer works at an already entered, compiled statement
   fragment. The selected hit is not assumed to be inside the fragment: a
   normal completion to the first continuation cursor is the other case. *)
Definition deploy_body_create_cut_rule_def:
  deploy_body_create_cut_rule tops runtime_bc rpolicy dunit am tx os <=>
  let C = dunit.cu_context;
      cx = deploy_evaluation_context tops am tx;
      st0 = initial_state am [];
      DF = \H. deploy_dead H tops runtime_bc am tx;
      lo = imm_len tops in
  !body cenv f Csh fsh sa sb sha shb base src G tn d k before key hit i s.
    (?mut source_body am_c es0.
      deploy_ctor_start tops am tx (mut,F,source_body,am_c,es0) /\
      src = es0 with outcomes := SOME os) /\
    (?nkey ut imm exit_lbl sj st_exit st_epilogue st_final.
      deploy_ctor_code tops rpolicy runtime_bc dunit
        (body,cenv,F,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,f)) /\
    compile_stmts cenv NoLoop NoneT body sa = ((),sb) /\
    compile_stmts (gas_shadow_env T cenv) NoLoop NoneT (MAP gas_shadow_stmt body)
      sha = ((),shb) /\
    shadow_body_inv tops C Csh /\ gas_shadow_context C Csh /\
    gas_shadow_function f fsh /\ gas_shadow_state sa sha /\ gas_shadow_state sb shb /\
    fn_has_code sa sb f /\ fn_has_code sha shb fsh /\
    MEM f C.ctx_functions /\ MEM fsh Csh.ctx_functions /\
    fn_inst_ids_distinct f /\ ctx_inst_ids_distinct C /\
    (!label bb. lookup_block label f.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
    ~base.vs_halted /\ base.vs_current_bb = sa.cs_current_bb /\
    base.vs_inst_idx = LENGTH sa.cs_current_insts /\
    return_buf_frame NONE cenv sa base /\ alloca_history f base /\
    (ctx_has_dalloca C ==> allocas_below_fmp base) /\
    (!fn inst s. frag_reachable C f base fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H src.storage_trace ==>
      stmt_state_rel H C f cenv cx src base /\
      ghost_inv_at (DF H) lo NONE cenv cx src G tn base) /\
    create_trace_from [] d k C f base = before ++ [(key,hit,i,s)] /\
    run_from k C f base = Abort ExHalt_abort (halt_state (set_returndata [] s)) /\
    ~inst_create_size_ok i s ==>
    create_body_cut (gas_explicit_sites C Csh) tops cx st0 (eval_stmts cx body)
      (src,base) (before,(key,hit,i,s)) \/
    ?n u. gas_path C f base n (OK u) /\ ~block_is_terminated sb /\
          ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts
End

Theorem selected_deploy_raw_create_size_from_body:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es fmp vi.
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    deploy_phases policy tops (assemble prog,runtime_bc) (rpolicy,dunit,dout,prog,cplan) /\
    deploy_source_ok tops am tx /\ deploy_dalloca_form_occurs expr_create_root tops /\
    deploy_state_rel tops (assemble prog') am tx es /\ LENGTH (call_trace es) < 2 ** 64 /\
    w2n (opt_deploy_entry_state_own prog prog' cplan tops es).vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    raw_variant fmp vi (opt_deploy_entry_state_own prog prog' cplan tops es) /\
    (!gs. deploy_storage_ok tops am tx (MAP SND (call_trace es)) gs) /\
    (!gs. ~deploy_source_exempt tops
      (load_contract (SOME (MAP SND (call_trace es))) gs am tx [(NONE,tops)] [])) /\
    (!gs. load_contract (SOME (MAP SND (call_trace es))) gs am tx [(NONE,tops)] [] <>
      INR (Error (RuntimeError "create initcode too large"))) /\
    deploy_body_create_cut_rule tops runtime_bc rpolicy dunit am tx
      (MAP SND (call_trace es)) ==>
    !fn i s. raw_reachable vi dunit.cu_context fn i s ==> inst_create_size_ok i s
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> CCONTR_TAC >>
  qabbrev_tac `C = dunit.cu_context` >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by fs[deploy_phases_def] >>
  drule lower_vyper_deploy_unit_context_ok >> strip_tac >>
  `EVERY wf_function C.ctx_functions` by
    fs[Abbr `C`, lowering_context_ok_def, ptr_ok_check_def, EVERY_MEM] >>
  `vi.vs_outcomes = MAP SND (call_trace es) /\ vi.vs_initial_fmp = fmp` by
    fs[raw_variant_def, gas_variant_def, venom_state_component_equality,
       opt_deploy_entry_state_own_def, opt_entry_state_own_def, entry_venom_state_def] >>
  `!gs. deploy_storage_ok tops am tx vi.vs_outcomes gs` by simp[] >>
  qunabbrev_tac `C` >>
  drule_all deploy_unit_execution_correct_selected_raw_fmp >> strip_tac >>
  qpat_x_assum `!vs. raw_variant _ vs _ ==> _` drule >> strip_tac >>
  `!gs. ~deploy_source_exempt tops
     (load_contract (SOME vi.vs_outcomes) gs am tx [(NONE,tops)] [])` by simp[] >>
  drule_all selected_deploy_terminal >> strip_tac >>
  qabbrev_tac `C = dunit.cu_context` >>
  `!err. run_context fuel C vi <> Error err` by simp[] >>
  drule_all raw_reached_oversized_create_terminal >> strip_tac >>
  `?exts ints fb cf. classify_functions tops = (exts,ints,fb,SOME cf)` by
    (qpat_x_assum `deploy_dalloca_form_occurs _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[deploy_dalloca_form_occurs_def] >>
     qmatch_goalsub_abbrev_tac `IS_SOME (SND (SND (SND cl)))` >>
     PairCases_on `cl` >> Cases_on `cl3` >> simp[]) >>
  namedCases_on `fuel` ["", "kfuel"]
  >- gvs[trace_context_def, trace_function_def] >>
  reverse (Cases_on `?mut nr body' am_c es0. deploy_ctor_start tops am tx (mut,nr,body',am_c,es0)`)
  >- (`!mut nr body' am_c es0. ~deploy_ctor_start tops am tx (mut,nr,body',am_c,es0)` by metis_tac[] >>
      qunabbrev_tac `C` >> drule_all selected_deploy_no_start >> strip_tac >>
      qabbrev_tac `C = dunit.cu_context` >>
      `terminates (run_context 1 C vi)` by simp[terminates_def] >>
      `1 <= SUC kfuel` by simp[] >> drule_all run_context_terminates_mono >> simp[]) >>
  pop_assum strip_assume_tac >>
  `~nr` by metis_tac[deploy_ctor_not_nonreentrant] >> gvs[] >>
  suspend "body"
QED

Resume selected_deploy_raw_create_size_from_body[body]:
  drule_all deploy_ctor_code_exists >> strip_tac >>
  drule_all deploy_relocated_data_layout >> strip_tac >>
  qpat_x_assum `DROP _ (assemble prog') = runtime_bc` kall_tac >>
  `IS_SOME (FLOOKUP (lo_reloc prog prog') "runtime_begin")` by simp[] >>
  `raw_variant vi.vs_initial_fmp vi
    (opt_deploy_entry_state_own prog prog' cplan tops es with vs_outcomes := vi.vs_outcomes)` by
    fs[raw_variant_def, gas_variant_def, venom_state_component_equality] >>
  `ctx_has_dalloca C ==> imm_len tops + unit_alloca_budget C <= w2n vi.vs_initial_fmp /\
     w2n vi.vs_initial_fmp < 2 ** 254` by simp[] >>
  qunabbrev_tac `C` >> drule_all deploy_ctor_entry_joint_raw >> strip_tac >> gvs[] >>
  `supported_program tops /\ supported_program_deploy tops` by fs[deploy_source_ok_def] >>
  drule_all deploy_ctor_original_entry_shape >> strip_tac >>
  `!label bb. lookup_block label func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all deploy_ctor_raw_blocks_no_phi >> simp[]) >>
  `!err. run_context (SUC kfuel) dunit.cu_context vi <> Error err` by simp[] >>
  drule_all residual_selected_visit >> strip_tac >>
  suspend "apply"
QED

Resume selected_deploy_raw_create_size_from_body[apply]:
  drule_all deploy_ctor_body_shadow >>
  disch_then (qx_choosel_then [`csh`,`fsh`,`sha`,`shb`] strip_assume_tac) >>
  qabbrev_tac `body = subst_consts_stmts (module_consts_env tops []) body'` >>
  `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
  `MEM func dunit.cu_context.ctx_functions /\ fn_inst_ids_distinct func /\
   compile_stmts cenv NoLoop NoneT body sa = ((),sb) /\
   fn_has_code sa sb func /\ fn_has_code sb sj func /\
   st_exit.cs_current_bb = exit_lbl /\ st_exit.cs_current_insts = [] /\
   st_epilogue = st_exit /\
   compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm
     st_exit = ((),st_final) /\ fn_has_code st_exit st_final func /\
   (~block_is_terminated sb ==>
     emit_inst JMP [Label exit_lbl] [] sb = ((),sj))` by
    (qpat_x_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
     simp[deploy_ctor_code_def, comp_return_def, new_block_def] >>
     rpt strip_tac >> gvs[]) >>
  qabbrev_tac `entry = vi with <|vs_prev_bb := NONE;
    vs_current_bb := "__deploy"; vs_inst_idx := 0|>` >>
  `enters_block func entry entry` by
    simp[enters_block_def, Abbr `entry`, eval_phis_no_phi, venom_state_fupdfupds] >>
  `!ii. active_inst func ii entry ==> raw_reachable vi dunit.cu_context func ii entry` by
    (rpt strip_tac >> irule raw_reachable_entry >> fs[Abbr `entry`]) >>
  `!ii. active_inst func ii s0 ==> raw_reachable vi dunit.cu_context func ii s0` by
    (rpt strip_tac >> irule raw_reachable_gas_path >>
     simp[] >> conj_tac >- metis_tac[] >>
     qexistsl [`0`,`entry`] >> simp[]) >>
  `ctx_has_dalloca dunit.cu_context ==>
    !fn inst st. raw_reachable vi dunit.cu_context fn inst st ==> dalloca_fmp_headroom inst st` by
    (strip_tac >>
     `deploy_dalloca_form_occurs expr_raw_shape_root tops` by
       metis_tac[deploy_unit_no_dalloca_static] >>
     `deploy_typing_ok tops am tx` by fs[deploy_source_ok_def] >>
     `w2n vi.vs_initial_fmp < 2 ** 254 /\
      imm_len tops + unit_alloca_budget dunit.cu_context +
        32 * ctx_dload_count dunit.cu_context <= w2n vi.vs_initial_fmp` by simp[] >>
     `LENGTH (call_trace es) < 2 ** 64` by simp[] >>
     `opt_deploy_entry_state_own prog prog' cplan tops es =
      opt_deploy_entry_state_own prog prog' cplan tops es` by simp[] >>
     qpat_x_assum `raw_reachable vi _ _ _ _` kall_tac >>
     rpt strip_tac >> drule_all deploy_entry_raw_headroom >> simp[]) >>
  `!fn inst st. frag_reachable dunit.cu_context func s0 fn inst st ==>
       dalloca_fmp_headroom inst st` by
    (rpt strip_tac >> Cases_on `ctx_has_dalloca dunit.cu_context`
     >- (drule_all raw_reachable_through_fragment >> metis_tac[]) >>
     drule_all frag_reachable_members >> strip_tac >>
     fs[ctx_has_dalloca_def, EXISTS_MEM, dalloca_fmp_headroom_def] >> metis_tac[]) >>
  suspend "cut"
QED

Resume selected_deploy_raw_create_size_from_body[cut]:
  `!H. valid_horizon (deploy_evaluation_context tops am tx) (initial_state am []) H
      (es0 with outcomes := SOME (MAP SND (call_trace es))).storage_trace ==>
      stmt_state_rel H dunit.cu_context func cenv (deploy_evaluation_context tops am tx)
        (es0 with outcomes := SOME (MAP SND (call_trace es))) s0 /\
      ghost_inv_at (deploy_dead H tops runtime_bc am tx) (imm_len tops) NONE cenv
        (deploy_evaluation_context tops am tx)
        (es0 with outcomes := SOME (MAP SND (call_trace es))) G0 tn0 s0` by
    (simp[] >> rpt strip_tac >>
     qpat_assum `!st0 H. valid_horizon _ st0 H _ ==> _`
       (qspecl_then [`initial_state am []`,`H`] mp_tac) >> simp[]) >>
  `create_body_cut (gas_explicit_sites dunit.cu_context csh) tops
      (deploy_evaluation_context tops am tx) (initial_state am [])
      (eval_stmts (deploy_evaluation_context tops am tx) body)
      (es0 with outcomes := SOME (MAP SND (call_trace es)),s0)
      (local_before,((p,d,i.inst_id),fn,i,s)) \/
   ?n u. gas_path dunit.cu_context func s0 n (OK u) /\ ~block_is_terminated sb /\
     ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
     u.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qpat_x_assum `deploy_body_create_cut_rule _ _ _ _ _ _ _`
       (irule o SIMP_RULE std_ss [deploy_body_create_cut_rule_def, LET_THM]) >>
     simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (goal_assum (drule_at (Pat `deploy_ctor_start _ _ _ _`)) >> simp[]) >>
     conj_tac >- (qexistsl [`d'`,`k`] >> simp[]) >>
     qexistsl [`G0`,`cenv`,`fsh`,`sa`,`sha`,`shb`,`tn0`] >>
     simp[] >> rpt conj_tac >>
     FIRST [goal_assum (drule_at (Pat `deploy_ctor_code _ _ _ _ _`)) >> simp[],
            metis_tac[]]) >>
  pop_assum strip_assume_tac
  >- (`!gx. eval_stmts (deploy_evaluation_context tops am tx) body
           (es0 with <|gas_obs := gx; outcomes := SOME (MAP SND (call_trace es))|>) =
         eval_stmts (deploy_evaluation_context tops am tx) body'
           (es0 with <|gas_obs := gx; outcomes := SOME (MAP SND (call_trace es))|>)` by
        (drule_all deploy_ctor_body_substitution >>
         simp[Abbr `body`, vyperStateTheory.evaluation_state_fupdcanon]) >>
      drule_all selected_deploy_trace_failure >> simp[]) >>
  `!err. run_from k dunit.cu_context func s0 <> Error err` by simp[] >>
  drule_all deploy_path_trace_continue >>
  disch_then (qspecl_then [`[]`,`d'`] strip_assume_tac) >>
  `emit_inst JMP [Label exit_lbl] [] sb = ((),sj)` by simp[] >>
  drule_all deploy_normal_exit_no_create_abort >> simp[] >>
  qexistsl [`halt_state (set_returndata [] s)`,`k'`,`dunit.cu_context`] >>
  metis_tac[]
QED
Finalise selected_deploy_raw_create_size_from_body
