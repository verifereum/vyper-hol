(*
 * LowerDload against the O1 pass contract: the runs of the input and the
 * output match up to the dead bytes D.
 * Kept in its own theory so its proof can be worked on apart from the
 * other rows; o1ContractLowerDloadStage assembles them.
 *
 * TOP-LEVEL:
 *   lower_dload_stage_sim
 *   lower_dload_stage_events_upto: the first n gas events of a run that
 *     stays safe up to its n-th event, with no termination needed
 *)
Theory o1ContractLowerDloadSim
Ancestors
  o1SafeUpto
  o1ContractLowerDload o1PassContract ptrDiscipline unitMemInv
  lowerDloadDefs venomPassSchedule list venomFnScheduleRunner
  venomCompilerTypes irSupply venomPassDispatcher venomInst
  o1LowerDloadPairedAllocation o1LowerDloadAddressArithmetic
  o1LowerDloadFreshNext o1LowerDloadRepeatedNext o1LowerDloadJointParam
  o1LowerDloadJointTernary o1LowerDloadJointArithmetic o1LowerDloadJointRead0
  o1LowerDloadJointRead1 o1LowerDloadJointResidualScalar o1LowerDloadJointIdentity
  o1LowerDloadJointRetpc o1LowerDloadJointVarsUpdate o1LowerDloadJointBump
  o1LowerDloadJointCompare o1LowerDloadRangeTransport
  o1LowerDloadJointRangeCopy o1LowerDloadJointCleanWrite
  o1LowerDloadJointRangeRead o1LowerDloadForwardAbort o1LowerDloadJointReturn
  o1LowerDloadJointPop o1LowerDloadJointRestore o1LowerDloadJointReturnBoundary
  o1LowerDloadJointCall o1LowerDloadInvokeArguments o1LowerDloadAbortResult
  o1LowerDloadHaltResult o1LowerDloadBranchExec o1LowerDloadSegmentContinuation
  o1LowerDloadOrdinaryDispatch o1LowerDloadEntryFetch o1LowerDloadRootResult
  o1LowerDloadRunnerBoundary o1LowerDloadRootEntry o1LowerDloadJointEntry
  venomExecSemantics o1LowerDloadSourceEntry o1LowerDloadRunner
  o1LowerDloadRunnerExec
  o1LowerDloadEndpointConsumer o1LowerDloadJointRelation o1LowerDloadOccurrence
  o1LowerDloadOccurrenceHeadroom venomWf passSimulationDefs venomState gasEvents
  o1LowerDloadShared gasCount

(* The runner supplies a covering supply separately for each function. *)
Theorem lower_dload_stage_supply_rel:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' ==>
  LIST_REL (\f g. ?s t. ir_supply_covers_fn s f /\
                         lower_dload_function_supply s f = (g,t))
    C.ctx_functions C'.ctx_functions
Proof
  rw[ctx_pass_stage_def] >>
  irule LIST_REL_mono >> goal_assum (drule_at Any) >>
  rpt strip_tac >> gvs[fn_pass_step_def, AllCaseEqs()] >>
  rename1 `lower_dload_function_supply s f = (g,t)` >>
  `MEM f observed.cu_context.ctx_functions` by
    (gvs[lookup_unique_function_def, AllCaseEqs()] >>
     `MEM f (FILTER (\g. g.fn_name = f.fn_name)
                observed.cu_context.ctx_functions)` by simp[] >>
     gvs[MEM_FILTER]) >>
  qexistsl [`s`, `t`] >> simp[] >>
  gvs[ir_supply_covers_unit_def, ir_supply_covers_fn_def, list_subset_def,
      unit_ir_inst_ids_def, unit_ir_vars_def, unit_ir_labels_def,
      EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem lower_dload_stage_lookup_supply:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  lookup_function name C.ctx_functions = SOME f ==>
  ?g s t. lookup_function name C'.ctx_functions = SOME g /\
          ir_supply_covers_fn s f /\
          lower_dload_function_supply s f = (g,t)
Proof
  strip_tac >> drule lower_dload_stage_supply_rel >>
  qpat_x_assum `ctx_pass_stage _ _ _ _ _` kall_tac >>
  qpat_x_assum `lookup_function _ _ = _` mp_tac >>
  qid_spec_tac `f` >>
  Q.SPEC_TAC (`C'.ctx_functions`, `gs`) >>
  Q.SPEC_TAC (`C.ctx_functions`, `fs`) >>
  Induct >> Cases_on `gs` >>
  simp[lookup_function_def, FIND_thm] >> rpt strip_tac >>
  rename1 `lower_dload_function_supply supply src = (dst,supply')` >>
  drule lower_dload_function_supply_labels >> strip_tac >>
  Cases_on `src.fn_name = name` >> gvs[] >>
  fs[GSYM lookup_function_def] >> metis_tac[]
QED

Theorem lower_dload_stage_invoke_entry:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  o1_ctx_shape C /\ ptr_discipline_upto lo ncut C vs /\ gas_cut ncut vs s /\ opaque_use_ok caller /\
  ld_joint_boundary vs C C' lo D stk PG G tn caller callinst s t
    n a U B HP H sites X ts /\ active_inst caller callinst s /\
  callinst.inst_opcode = INVOKE /\ decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs sn ==>
  ?callee' args' ct s1 t1 inst.
    lookup_function nm C'.ctx_functions = SOME callee' /\
    lookup_function callee.fn_name C'.ctx_functions = SOME callee' /\
    opaque_use_ok callee /\ ~cs.vs_halted /\
    enters_block callee cs s1 /\ active_inst callee inst s1 /\
    eval_operands ops t = SOME args' /\
    setup_callee callee' args' t = SOME ct /\ enters_block callee' ct t1 /\
    s1.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    t1.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address /\
    ld_joint_boundary vs C C' lo D
      (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1 t1
      (SUC n) n (<|of_owner := a; of_prov := H; of_params := HP |> :: U)
      B (MAP (op_prov H) ops) FEMPTY sites X (t::ts)
Proof
  strip_tac >>
  drule_all lower_dload_stage_lookup_supply >> strip_tac >>
  `wf_function callee` by metis_tac[ld_ctx_shape_lookup_wf] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `~cs.vs_halted` by metis_tac[ld_setup_callee_not_halted] >>
  drule_all ld_wf_enters_block_fetch >> strip_tac >>
  `opaque_use_ok callee` by metis_tac[ld_ctx_shape_lookup_opaque] >>
  drule_all ld_joint_boundary_call_invariant >> strip_tac >>
  `callee.fn_name = nm` by
    (qpat_x_assum `lookup_function nm C.ctx_functions = SOME callee` mp_tac >>
     Q.SPEC_TAC (`C.ctx_functions`, `fns`) >> qid_spec_tac `callee` >>
     Induct_on `fns` >> simp[lookup_function_def, FIND_thm] >>
     rpt strip_tac >> Cases_on `h.fn_name = nm` >>
     gvs[lookup_function_def]) >>
  qexistsl_tac [`g`, `args'`, `ct`, `sn`, `t1`, `inst`] >> simp[]
QED

Theorem ld_terminating_invoke_inversion:
  i.inst_opcode = INVOKE /\ step_inst k C i s = r /\ terminates r ==>
  ?nm ops fn args cs cr.
    decode_invoke i = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME fn /\
    eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
    run_blocks k C fn cs = cr /\ terminates cr /\
    ((?ir se s1. cr = IntRet ir se /\
       bind_outputs i.inst_outputs ir.iret_values
         (adopt_return_fmp ir (merge_callee_state s se)) = SOME s1 /\ r = OK s1) \/
     (?se. cr = Halt se /\ r = Halt se) \/
     (?ab se. cr = Abort ab se /\ r = Abort ab se))
Proof
  strip_tac >>
  qpat_x_assum `step_inst k C i s = r` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `decode_invoke i`
  >- (strip_tac >> gvs[terminates_def]) >> simp[] >>
  rename1 `decode_invoke i = SOME dec` >> PairCases_on `dec` >>
  Cases_on `lookup_function dec0 C.ctx_functions`
  >- (strip_tac >> gvs[terminates_def]) >> simp[] >>
  Cases_on `eval_operands dec1 s`
  >- (strip_tac >> gvs[terminates_def]) >> simp[] >>
  rename1 `lookup_function dec0 C.ctx_functions = SOME fn` >>
  rename1 `eval_operands dec1 s = SOME args` >>
  Cases_on `setup_callee fn args s`
  >- (strip_tac >> gvs[terminates_def]) >> simp[] >>
  rename1 `setup_callee fn args s = SOME cs` >>
  Cases_on `run_blocks k C fn cs` >> simp[] >>
  rpt strip_tac >> gvs[terminates_def, AllCaseEqs()] >>
  qpat_x_assum `Error _ = _` (SUBST_ALL_TAC o SYM) >> gvs[]
QED

(* A nonempty event list of an INVOKE is its callee's run events. *)
Theorem ld_invoke_events_inversion:
  i.inst_opcode = INVOKE /\ gas_events_step k C owner i s <> [] ==>
  ?nm ops callee args cs.
    decode_invoke i = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    gas_events_step k C owner i s = gas_events_blocks k C callee cs
Proof
  strip_tac >> fs[gas_events_step_def] >> BasicProvers.every_case_tac >> gvs[]
QED

(* A callee that returns before its budget ends inside the cut. *)
Theorem ld_blocks_ret_cut[local]:
  run_blocks k C fn s = IntRet ir se /\
  j + LENGTH vs.vs_gas_readings <= ncut + LENGTH s.vs_gas_readings /\
  LENGTH (gas_events_blocks k C fn s) < j ==>
  gas_cut ncut vs se
Proof
  strip_tac >> fs[gas_events_length] >>
  mp_tac (cj 3 gas_count_suffix) >>
  disch_then (qspecl_then [`k`,`C`,`fn`,`s`] mp_tac) >>
  simp[gas_count_suffix_def] >> strip_tac >>
  simp[gas_cut_def, LENGTH_DROP] >> decide_tac
QED

val ldStepClause = fst (dest_conj (fst (dest_imp
  (concl ld_runner_conditional_induction))));

val ldPacket = fst (strip_comb (fst (dest_imp
  (concl ld_runner_packet_terminates))));

Theorem ld_runner_step_clause:
  ^ldStepClause
Proof
  qabbrev_tac `RR = ^ldPacket` >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  drule_all ld_budget_cut >> strip_tac >>
  `ptr_discipline_upto lo ncut C vs` by
    fs[o1_safe_upto_def, o1_ptr_safe_upto_def] >>
  reverse conj_tac
  >- (strip_tac >>
      `gas_events_step fuel C fn.fn_name inst s <> []` by
        (strip_tac >> gvs[]) >>
      drule_all ld_invoke_events_inversion >> strip_tac >>
      `?sn. enters_block callee cs sn` by metis_tac[ld_run_enters] >>
      `j + LENGTH vs.vs_gas_readings <= ncut + LENGTH cs.vs_gas_readings` by
        (drule ld_setup_callee_gas_readings >> simp[]) >>
      drule_all lower_dload_stage_invoke_entry >> strip_tac >>
      qpat_x_assum `enters_block callee cs sn` kall_tac >>
      `run_blocks fuel C callee cs = run_blocks fuel C callee cs` by simp[] >>
      first_x_assum (drule_all_then (mp_tac o CONJUNCT2) o
        SIMP_RULE bool_ss [PULL_EXISTS]) >>
      impl_tac >- (qpat_x_assum `j <= _` mp_tac >> simp[]) >> strip_tac >>
      qexists_tac `m` >> gvs[gas_events_step_def]) >>
  strip_tac >>
  drule_at (Pat `terminates _`) ld_terminating_invoke_inversion >>
  disch_then (qspecl_then [`s`, `fuel`, `inst`, `C`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `setup_callee callee args s = SOME cs` >>
  `gas_events_step fuel C fn.fn_name inst s =
   gas_events_blocks fuel C callee cs` by simp[gas_events_step_def] >>
  `LENGTH (gas_events_blocks fuel C callee cs) < j` by metis_tac[] >>
  `?sn. enters_block callee cs sn` by metis_tac[ld_run_enters] >>
  `j + LENGTH vs.vs_gas_readings <= ncut + LENGTH cs.vs_gas_readings` by
    (drule ld_setup_callee_gas_readings >> simp[]) >>
  `!ir' se'. run_blocks fuel C callee cs = IntRet ir' se' ==>
     gas_cut ncut vs se'` by metis_tac[ld_blocks_ret_cut] >>
  drule_all lower_dload_stage_invoke_entry >> strip_tac >>
  qpat_x_assum `enters_block callee cs sn` kall_tac >>
  first_x_assum (drule_all_then (mp_tac o CONJUNCT1) o
    SIMP_RULE bool_ss [PULL_EXISTS]) >>
  impl_tac >- simp[] >> strip_tac >>
  gvs[] >>
  qpat_x_assum `RR _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `RR`] >> strip_tac
  >- suspend "return"
  >- suspend "halt"
  >> suspend "abort"
QED

Resume ld_runner_step_clause[return]:
  `wf_function fn` by
    (drule ld_joint_source >>
     disch_then (strip_assume_tac o MATCH_MP occ_frame_reachable_annotation) >>
     fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  `cs.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address` by
    metis_tac[ld_setup_callee_call_ctx] >>
  drule_at (Pat `ld_joint_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (SIMP_RULE bool_ss [PULL_EXISTS] ld_return_endpoint_consume) >>
  simp[] >> disch_then (drule_all_then strip_assume_tac) >>
  `s1.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address` by
    (qpat_x_assum `bind_outputs _ jr.iret_values _ = _` kall_tac >>
     qspec_then `\u. u.vs_call_ctx.cc_address` mp_tac
       venomInstProofs1Theory.bind_outputs_preserves >>
     simp[update_var_def] >> disch_then drule >>
     simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  `step_inst m C' inst t = OK t1'` by simp[Once step_inst_def] >>
  qexists_tac `m` >>
  conj_tac >- simp[gas_events_step_def] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume ld_runner_step_clause[halt]:
  qexists_tac `m` >> simp[Once step_inst_def] >> simp[Once step_inst_def] >>
  gvs[] >> simp[gas_events_step_def]
QED
Resume ld_runner_step_clause[abort]:
  qexists_tac `m` >> simp[Once step_inst_def] >> simp[Once step_inst_def] >>
  gvs[] >> simp[gas_events_step_def]
QED
Finalise ld_runner_step_clause

val ldS0 = ``vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>``;

(* The pass keeps the entry function, its label and the context run. *)
Theorem ld_stage_entry[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  ?fn' u u'. C'.ctx_entry = SOME name /\
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl /\
    ir_supply_covers_fn u fn /\ lower_dload_function_supply u fn = (fn',u') /\
    !m. run_context m C' vs = run_blocks m C' fn' ^ldS0
Proof
  strip_tac >> drule_all lower_dload_stage_lookup_supply >> strip_tac >>
  drule lower_dload_function_supply_labels >> strip_tac >>
  qexistsl_tac [`g`, `s`, `t`] >>
  fs[ctx_pass_stage_def, run_context_def, run_function_def]
QED

Theorem lower_dload_stage_root_entry:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_safe_upto D lo ncut C vs /\ 0 < ncut /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\ enters_block fn ^ldS0 s1 ==>
  ?fn' inst bb.
    C'.ctx_entry = SOME name /\
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl /\
    (!m. run_context m C' vs = run_blocks m C' fn' ^ldS0) /\
    enters_block fn' ^ldS0 s1 /\ ~vs.vs_halted /\ ~s1.vs_halted /\
    lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s1.vs_inst_idx = SOME inst /\ active_inst fn inst s1 /\
    ld_joint_boundary vs C C' lo D [] [] FEMPTY entry_taint fn inst s1 s1
      1 0 [] FEMPTY [] FEMPTY FEMPTY FEMPTY []
Proof
  strip_tac >>
  drule_all ld_stage_entry >> disch_then (qspec_then `vs` strip_assume_tac) >>
  `wf_function fn` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >>
     `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
     first_x_assum drule >> simp[o1_fn_shape_def]) >>
  `~vs.vs_halted` by
    gvs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  `~s1.vs_halted` by (drule ld_enters_block_halted >> simp[]) >>
  `gas_cut ncut vs s1` by
    (qpat_assum `enters_block fn _ s1`
       (strip_assume_tac o REWRITE_RULE [contextCodegenRelTheory.enters_block_def]) >>
     imp_res_tac gas_count_phis_ok >> gvs[gas_cut_def]) >>
  drule_all ld_wf_enters_block_fetch >> strip_tac >>
  drule_all ld_joint_entry >> strip_tac >>
  qexistsl_tac [`fn'`, `inst`, `bb`] >> simp[]
QED


(* Zero-size allocation provenance cannot license a pointer comparison. *)
Theorem access_ok_zero_size_comparison:
  access_ok lo G fn inst s /\
  (inst.inst_opcode = LT \/ inst.inst_opcode = GT \/ inst.inst_opcode = EQ) /\
  inst.inst_operands = [Var u; Var w] /\ FLOOKUP G u = SOME (b,0)
  ==> F
Proof
  strip_tac >>
  `u IN FDOM G` by metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  fs[access_ok_def] >>
  first_x_assum (qspecl_then [`u`, `w`] mp_tac) >> simp[]
QED


Theorem lower_dload_translate_add:
  !x z b c. ((x:bytes32) + n2w c - n2w b) + z =
             (x + z) + n2w c - n2w b
Proof
  wordsLib.WORD_DECIDE_TAC
QED

Theorem lower_dload_translate_sub:
  !x z b c. ((x:bytes32) + n2w c - n2w b) - z =
             (x - z) + n2w c - n2w b
Proof
  wordsLib.WORD_DECIDE_TAC
QED

Theorem lower_dload_translate_comparisons:
  !x y b c sz.
    b <= w2n (x:bytes32) /\ w2n x <= b+sz /\
    b <= w2n (y:bytes32) /\ w2n y <= b+sz /\
    b+sz < dimword (:256) /\ c+sz < dimword (:256) ==>
    ((x = y) <=> (x + n2w c - n2w b = y + n2w c - n2w b)) /\
    ((w2n x < w2n y) <=>
      (w2n (x + n2w c - n2w b) < w2n (y + n2w c - n2w b))) /\
    ((w2n y < w2n x) <=>
      (w2n (y + n2w c - n2w b) < w2n (x + n2w c - n2w b)))
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (x + n2w c - n2w b) = c + (w2n x - b)` by
    (irule lower_dload_translate_endpoint >> asm_rewrite_tac[] >>
     qexists_tac `sz` >> asm_rewrite_tac[]) >>
  `w2n (y + n2w c - n2w b) = c + (w2n y - b)` by
    (irule lower_dload_translate_endpoint >> asm_rewrite_tac[] >>
     qexists_tac `sz` >> asm_rewrite_tac[]) >>
  pure_rewrite_tac[GSYM wordsTheory.w2n_11] >>
  asm_rewrite_tac[] >> decide_tac
QED


(* The simulation: every run of C that stays inside the gas cut is matched
   by a run of C' up to the dead bytes D, event for event.  The DLOAD
   offset bound (in o1_safe_upto) keeps the code_end-relative CODECOPY
   offset from wrapping; code_layout_valid (in o1_run_state_ok) binds
   "code_end" to the code/data boundary; the headroom bound (in
   o1_safe_upto) and the callee-first order keep the shifted alloca sites
   from wrapping; the pointer discipline and the taint bound (in
   o1_safe_upto) keep the shifted alloca addresses out of what the run
   observes. *)
val ldMutualResult = snd (dest_imp (concl ld_runner_conditional_induction));

Theorem ld_runner_simulation:
  ^ldMutualResult
Proof
  mp_tac ld_runner_conditional_induction >>
  (impl_tac >- (conj_tac
    >- ACCEPT_TAC ld_runner_step_clause
    >> ACCEPT_TAC ld_runner_exec_clause)) >>
  simp[]
QED

val _ = if null (hyp ld_runner_simulation) andalso
               aconv (concl ld_runner_simulation) ldMutualResult
        then () else raise Fail "mutual runner audit failed";

(* The run of the entry function, cut after its first j events. *)
Theorem ld_root_simulation:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  callee_first names C.ctx_functions /\ o1_safe_upto D lo ncut C vs /\
  0 < j /\ j <= ncut /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\ enters_block fn ^ldS0 s1 ==>
  ?fn'. C'.ctx_entry = SOME name /\
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl /\
    (!m. run_context m C' vs = run_blocks m C' fn' ^ldS0) /\
    (terminates (run_blocks fuel C fn ^ldS0) /\
     LENGTH (gas_events_blocks fuel C fn ^ldS0) < j ==>
     ?m. gas_events_blocks m C' fn' ^ldS0 = gas_events_blocks fuel C fn ^ldS0 /\
         terminates (run_blocks m C' fn' ^ldS0) /\
         dead_result_rel D (run_blocks fuel C fn ^ldS0)
           (run_blocks m C' fn' ^ldS0)) /\
    (j <= LENGTH (gas_events_blocks fuel C fn ^ldS0) ==>
     ?m. TAKE j (gas_events_blocks m C' fn' ^ldS0) =
         TAKE j (gas_events_blocks fuel C fn ^ldS0))
Proof
  strip_tac >>
  `0 < ncut` by decide_tac >>
  drule_all lower_dload_stage_root_entry >> strip_tac >>
  `opaque_use_ok fn` by metis_tac[ld_ctx_shape_lookup_opaque] >>
  `fn.fn_name = name` by
    (qpat_assum `lookup_function name C.ctx_functions = SOME fn`
       (mp_tac o REWRITE_RULE [lookup_function_def]) >>
     disch_then (mp_tac o MATCH_MP venomExecPropsTheory.FIND_P) >> simp[]) >>
  `lookup_function fn.fn_name C'.ctx_functions = SOME fn'` by simp[] >>
  `run_context fuel C vs = run_blocks fuel C fn ^ldS0` by
    simp[run_context_def, run_function_def] >>
  `j + LENGTH vs.vs_gas_readings <= ncut + LENGTH (^ldS0).vs_gas_readings`
    by simp[] >>
  `~(^ldS0).vs_halted` by simp[] >>
  `run_blocks fuel C fn ^ldS0 = run_blocks fuel C fn ^ldS0` by simp[] >>
  `C = C` by simp[] >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] (cj 3 ld_runner_simulation)) >>
  strip_tac >>
  qexists_tac `fn'` >> simp[] >> conj_tac
  >- (strip_tac >>
      qpat_x_assum `!v0. (_ ==> _) /\ (_ ==> _)`
        (mp_tac o CONJUNCT1 o Q.SPEC `fuel`) >>
      impl_tac >- simp[] >> strip_tac >>
      qpat_x_assum `run_context fuel C vs = _` (fn th =>
        drule ld_root_result_shape >>
        disch_then (qspecl_then [`vs`,`fuel`]
          (strip_assume_tac o REWRITE_RULE [th]))) >>
      gvs[terminates_def] >> qexists_tac `m` >> gvs[terminates_def]) >>
  strip_tac >>
  qpat_x_assum `!v0. (_ ==> _) /\ (_ ==> _)`
    (mp_tac o CONJUNCT2 o Q.SPEC `fuel`) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac `m` >> gvs[]
QED

Theorem lower_dload_stage_sim_events:
  !rpolicy D view C C' vs names fuel.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
    terminates (run_context fuel C vs) ==>
    ?fuel' name fn fn' lbl.
      C.ctx_entry = SOME name /\ C'.ctx_entry = SOME name /\
      lookup_function name C.ctx_functions = SOME fn /\
      lookup_function name C'.ctx_functions = SOME fn' /\
      fn_entry_label fn = SOME lbl /\ fn_entry_label fn' = SOME lbl /\
      dead_result_rel D (run_context fuel C vs) (run_context fuel' C' vs) /\
      terminates (run_context fuel' C' vs) /\
      gas_events_blocks fuel' C' fn'
        (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) =
      gas_events_blocks fuel C fn
        (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
Proof
  rpt strip_tac >>
  `run_context fuel C vs = run_context fuel C vs` by simp[] >>
  drule_all ld_run_context_entry >> strip_tac >>
  qpat_x_assum `s0 = _` SUBST_ALL_TAC >>
  drule o1_src_inv_safe_upto >> strip_tac >>
  qabbrev_tac `j = SUC (LENGTH (gas_events_blocks fuel C fn ^ldS0))` >>
  first_x_assum (qspec_then `j` assume_tac) >>
  `0 < j /\ j <= j` by simp[Abbr `j`] >>
  drule_all ld_root_simulation >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  qpat_x_assum `terminates _ /\ _ ==> _` mp_tac >>
  impl_tac >- (simp[Abbr `j`] >> metis_tac[]) >> strip_tac >>
  qexistsl_tac [`m`, `name`, `fn`, `fn'`, `lbl`] >> gvs[]
QED

Theorem lower_dload_stage_sim:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions ==>
    ctx_sim D C C' vs vs
Proof
  rpt strip_tac >> simp[ctx_sim_def] >> rpt strip_tac >>
  drule_all lower_dload_stage_sim_events >> strip_tac >>
  qexists_tac `fuel'` >> simp[]
QED

(* Admission checks run through holbuild check. *)
val _ = if null (hyp lower_dload_stage_sim)
        then () else raise Fail "lower_dload_stage_sim proof audit failed";

(* The first n events of a run inside the cut, with no termination. *)
Theorem lower_dload_stage_events_upto:
  !rpolicy D view C C' vs names lo n fuel name fn lbl.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    callee_first names C.ctx_functions /\ o1_safe_upto D lo n C vs /\
    C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    n <= LENGTH (gas_events_blocks fuel C fn
           (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) ==>
    ?fuel' fn'.
      C'.ctx_entry = SOME name /\ lookup_function name C'.ctx_functions = SOME fn' /\
      fn_entry_label fn' = SOME lbl /\
      n <= LENGTH (gas_events_blocks fuel' C' fn'
             (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) /\
      TAKE n (gas_events_blocks fuel' C' fn'
        (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) =
      TAKE n (gas_events_blocks fuel C fn
        (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))
Proof
  rpt strip_tac >>
  Cases_on `n = 0`
  >- (gvs[] >> drule_all ld_stage_entry >>
      disch_then (qspec_then `vs` strip_assume_tac) >>
      qexists_tac `fn'` >> simp[]) >>
  `gas_events_blocks fuel C fn ^ldS0 <> []` by (strip_tac >> gvs[]) >>
  `?s1. enters_block fn ^ldS0 s1` by metis_tac[ld_run_enters] >>
  `0 < n /\ n <= n` by decide_tac >>
  drule_all ld_root_simulation >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`m`, `fn'`] >> simp[] >>
  metis_tac[ld_take_length]
QED
