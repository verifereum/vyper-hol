(* Source PARAM progress, conditional on the source call-arity boundary. *)
Theory fmpStageCoverBackParam
Ancestors
  fmpStageOpBase fmpStageRel o1PassContract ptrDiscipline contextCodegenRel
  venomExecSemantics venomExecProofs venomInstProofs callLayoutDefs
  venomWf unitShapeDefs list rich_list words finite_map
  passSimulationDefs stackPlanTypes fmpAnalysisProps simplifyCfgMergeRuns
  fnFrameBoundaryInvoke

Theorem frame_param_bounds[local]:
  !vs C stk PG G tn fn inst s.
  frame_reachable vs C stk PG G tn fn inst s ==>
  o1_ctx_shape C /\
  (!stk0 PG0 G0 tn0 caller inv st name ops callee.
    frame_reachable vs C stk0 PG0 G0 tn0 caller inv st /\
    active_inst caller inv st /\ inv.inst_opcode = INVOKE /\
    inv.inst_operands = Label name::ops /\
    lookup_function name C.ctx_functions = SOME callee ==>
    LENGTH (fn_user_param_insts callee) <= LENGTH ops) ==>
  LENGTH (fn_user_param_insts fn) <= LENGTH s.vs_params /\
  EVERY (\f. LENGTH (fn_user_param_insts f.cf_fn) <=
             LENGTH f.cf_state.vs_params) stk
Proof
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac
  >- (rpt strip_tac >> simp[] >>
      `o1_fn_shape C fn /\ fn.fn_name = name` by
        (fs[o1_ctx_shape_def, EVERY_MEM] >>
         metis_tac[venomInstTheory.lookup_function_MEM, fmpAnalysisPropsTheory.lookup_function_name]) >>
      `entry_fn_no_params fn` by fs[o1_fn_shape_def] >>
      `fn_user_param_insts fn = []` suffices_by simp[] >>
      fs[fn_user_param_insts_def, FILTER_EQ_NIL, EVERY_MEM,
         entry_fn_no_params_def, fn_entry_insts_def, venomInstTheory.fn_insts_def,
         fn_insts_blocks_MEM, venomInstTheory.is_param_opcode_def,
         venomInstTheory.entry_block_def] >>
      Cases_on `fn.fn_blocks` >> gvs[] >>
      metis_tac[venomInstTheory.is_param_opcode_def])
  >- (rpt strip_tac >> drule_all step_preserves_params >> strip_tac >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      drule_all scfg_terminator_jump >> strip_tac >>
      fs[enters_block_def] >>
      drule eval_phis_only_updates_vs_vars >> strip_tac >>
      `s_phi.vs_params = s'.vs_params` by
        (qpat_x_assum `s_phi = _` (mp_tac o Q.AP_TERM `\x:venom_state. x.vs_params`) >> simp[]) >>
      `s'.vs_params = s.vs_params` by
        (qpat_x_assum `s' = _` (mp_tac o Q.AP_TERM `\x:venom_state. x.vs_params`) >>
         simp[venomStateTheory.jump_to_def]) >>
      gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      `inst.inst_operands = Label nm::ops` by
        gvs[decode_invoke_def, AllCaseEqs()] >>
      `LENGTH (fn_user_param_insts fn') <= LENGTH ops` by metis_tac[] >>
      drule setup_callee_frame >> strip_tac >>
      `LENGTH args = LENGTH ops` by
        metis_tac[eval_operands_some_length] >>
      fs[enters_block_def] >>
      drule eval_phis_only_updates_vs_vars >> strip_tac >>
      `s_phi.vs_params = cs.vs_params` by
        (qpat_x_assum `s_phi = _` (mp_tac o Q.AP_TERM `\x:venom_state. x.vs_params`) >> simp[]) >>
      gvs[] >> metis_tac[])
  >> rpt strip_tac >>
  drule invoke_bind_frame_fields >>
  disch_then (mp_tac o Q.AP_TERM `\x:venom_state. x.vs_params`) >>
  simp[adopt_return_fmp_def, merge_callee_state_def, AllCaseEqs()] >>
  Cases_on `ret.iret_adopt_fmp` >> simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem stage_source_canonical[local]:
  fmp_stage_lowered infos ctx runner fn fn' ==> canonical_param_prefix fn
Proof
  rw[fmp_stage_lowered_def] >>
  Cases_on `fn.fn_fmp_signature` >>
  gvs[fmpLowerDefsTheory.fmp_lower_function_with_info_def,
      fmpLowerDefsTheory.fmp_lower_input_def,
      fmpWfDefsTheory.fmp_signature_matches_fn_def,
      fmpWfDefsTheory.fmp_signature_syntax_wf_def, AllCaseEqs()]
QED

Theorem canonical_user_param_index[local]:
  canonical_param_prefix fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = PARAM ==>
  ?j. inst.inst_operands = [Lit (n2w j)] /\
      j < LENGTH (fn_user_param_insts fn) /\ LENGTH inst.inst_outputs = 1
Proof
  strip_tac >>
  drule (iffLR canonical_param_prefix_iff) >> strip_tac >>
  `fn_user_param_insts fn = users` by
    metis_tac[canonical_param_prefix_queries] >>
  `MEM inst users` by
    (gvs[venomInstTheory.fn_insts_def, fn_insts_blocks_MEM,
         no_param_insts_def, EVERY_MEM, MEM_APPEND,
         venomInstTheory.is_param_opcode_def] >>
     metis_tac[venomInstTheory.is_param_opcode_def]) >>
  fs[param_insts_from_append] >>
  qpat_x_assum `MEM inst users` mp_tac >>
  rewrite_tac[MEM_EL] >> strip_tac >>
  drule_all fnFrameBoundaryEntryParamsTheory.param_insts_from_el >>
  simp[param_inst_at_def] >> strip_tac >>
  qexists_tac `n` >> simp[]
QED

Theorem fmp_stage_back_param_conditional:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  terminates (step_inst k' C' inst t) /\ inst.inst_opcode = PARAM /\
  (!stk0 PG0 G0 tn0 caller inv st name args callee.
    frame_reachable vs C stk0 PG0 G0 tn0 caller inv st /\
    active_inst caller inv st /\ inv.inst_opcode = INVOKE /\
    inv.inst_operands = Label name::args /\
    lookup_function name C.ctx_functions = SOME callee ==>
    LENGTH (fn_user_param_insts callee) <= LENGTH args) ==>
  terminates (step_inst k C inst s)
Proof
  strip_tac >>
  `o1_ctx_shape C` by fs[fmp_stage_ctx_def] >>
  `LENGTH (fn_user_param_insts fn) <= LENGTH s.vs_params` by
    metis_tac[frame_param_bounds] >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `canonical_param_prefix fn` by
    (fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
     metis_tac[stage_source_canonical]) >>
  drule_all canonical_user_param_index >> strip_tac >>
  `w2n (n2w j : bytes32) < LENGTH s.vs_params` by
    (mp_tac (Q.SPEC `j` (INST_TYPE [alpha |-> ``:256``] word_n2w_le2)) >> decide_tac) >>
  `fnFrameBoundaryEntryParams$entry_param_shape s inst` by
    (simp[fnFrameBoundaryEntryParamsTheory.entry_param_shape_def] >>
     Cases_on `inst.inst_outputs` >> gvs[LENGTH_EQ_NUM_compute]) >>
  drule fnFrameBoundaryEntryParamsTheory.entry_param_step >>
  simp[terminates_def]
QED
