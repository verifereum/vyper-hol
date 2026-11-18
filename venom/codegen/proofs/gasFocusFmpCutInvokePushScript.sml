(* Static ABI and actual callee entry at a restored bounded INVOKE. *)
Theory gasFocusFmpCutInvokePush
Ancestors
  gasFocusFmpCutInvokeSite fmpStageFmpStepsInvokePosition
  fmpStageFmpStepsCallAbi fmpStageRel fmpLowerDefs fmpAnalysisDefs
  fmpAnalysisProps fcgBridge fcgDefs concretizeStageLookup fmpStepBridge
  venomPassSchedule venomFnScheduleRunner venomFnScheduleRunnerProps
  dftGasToListReachBoundary venomInstIdsProps venomExecProofs
  venomInst venomExecSemantics venomWf o1PassContract unitShapeDefs
  finite_map list words arithmetic

Theorem collect_selected_invoke[local]:
  !insts targets ivk nm ops.
    fmp_collect_invokes insts = SOME targets /\ MEM ivk insts /\
    ivk.inst_opcode = INVOKE /\ decode_invoke ivk = SOME (nm,ops) ==>
    MEM nm targets
Proof
  Induct >> simp[fmp_collect_invokes_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  gvs[fmp_invoke_target_def, decode_invoke_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem selected_invoke_resolves[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\ fn.fn_fmp_signature = NONE /\
  MEM ivk (fn_insts fn) /\ ivk.inst_opcode = INVOKE ==>
  ?callee info args. fmp_resolve_invoke infos ctx ivk = SOME (callee,info,args) /\
    MEM fn ctx.ctx_functions
Proof
  simp[fmp_stage_lowered_def] >> rpt strip_tac >>
  `fmp_lower_input infos ctx fn` by
    gvs[fmp_lower_function_with_info_def, AllCaseEqs()] >>
  `fmp_lower_inst_shape infos ctx ivk` by
    (fs[fmp_lower_input_def, fmp_lower_blocks_shape_def,
        fmp_lower_insts_shape_def, fn_insts_def, fn_insts_blocks_MEM, EVERY_MEM] >>
     metis_tac[]) >>
  `IS_SOME (fmp_resolve_invoke infos ctx ivk)` by
    gvs[fmp_lower_inst_shape_def] >>
  Cases_on `fmp_resolve_invoke infos ctx ivk` >> gvs[] >>
  PairCases_on `x` >> simp[] >>
  metis_tac[fmp_lower_input_def, lookup_function_MEM]
QED

Theorem selected_invoke_needs_root[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\ fn.fn_fmp_signature = NONE /\
  MEM fn ctx.ctx_functions /\ MEM ivk (fn_insts fn) /\
  ivk.inst_opcode = INVOKE /\ decode_invoke ivk = SOME (nm,ops) /\
  FLOOKUP infos nm = SOME ci /\ ci.fi_needs_fmp ==>
  IS_SOME (fmp_stage_root infos ctx fn)
Proof
  strip_tac >>
  `analyze_fmp_context ctx = SOME infos` by fs[fmp_stage_lowered_def] >>
  drule analyze_fmp_context_valid >> simp[fmp_info_valid_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `MEM nm targets` by
    (gvs[fmp_function_targets_def, AllCaseEqs()] >>
     metis_tac[collect_selected_invoke]) >>
  drule fmp_join_target_info_needs_iff >> strip_tac >>
  `info.fi_needs_fmp` by metis_tac[] >>
  drule_all fmp_stage_root_exists >> strip_tac >> simp[]
QED

(* Compare lowering witnesses by their selected instruction, not their
   analysis environments. Distinct target IDs pin the instruction. *)
Theorem selected_invoke_lowering[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\ ALL_DISTINCT (fn_labels fn) /\
  fn_inst_ids_distinct fn' /\ active_inst fn ivk s /\ ivk.inst_opcode = INVOKE /\
  MEM j (fn_insts fn') /\ j.inst_id = ivk.inst_id ==>
  (fmp_stage_root infos ctx fn = NONE /\ j = ivk) \/
  ?sp sp'. fmp_lower_inst infos ctx runner sp ivk = SOME ([j],sp')
Proof
  strip_tac >> drule_all active_inst_lookup_distinct >>
  simp[get_instruction_def, AllCaseEqs()] >> strip_tac >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `!b p. MEM b fn'.fn_blocks /\ p < LENGTH b.bb_instructions /\
         (EL p b.bb_instructions).inst_id = ivk.inst_id ==>
         EL p b.bb_instructions = j` by
    (rpt strip_tac >> irule fn_inst_ids_distinct_inj >>
     conj_tac >- simp[] >>
     qexists `fn'` >> simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
     metis_tac[EL_MEM]) >>
  ` (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = INVOKE` by simp[] >>
  drule_all fmp_stage_invoke_at >> strip_tac
  >- (disj1_tac >> gvs[] >> metis_tac[lookup_block_MEM]) >>
  disj2_tac >> gvs[] >> drule_all fmp_lower_invoke_inst >> strip_tac >>
  fs[] >>
  rename1 `lookup_block s.vs_current_bb fn'.fn_blocks = SOME tb` >>
  qmatch_asmsub_abbrev_tac `pos < LENGTH tb.bb_instructions` >>
  `MEM tb fn'.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `EL pos tb.bb_instructions = j` by
    (qpat_x_assum `!b p. _` (qspecl_then [`tb`,`pos`] mp_tac) >> simp[]) >>
  metis_tac[]
QED

Theorem selected_invoke_decode[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\ fn.fn_fmp_signature = NONE /\
  MEM ivk (fn_insts fn) /\ ivk.inst_opcode = INVOKE /\
  decode_invoke ivk = SOME (nm,ops) /\
  ((fmp_stage_root infos ctx fn = NONE /\ j = ivk) \/
   (?sp sp'. fmp_lower_inst infos ctx runner sp ivk = SOME ([j],sp'))) ==>
  ?callee sig.
    lookup_function nm ctx.ctx_functions = SOME callee /\
    callee.fn_fmp_signature = SOME sig /\
    decode_invoke j = SOME (nm,ops ++ if sig.fms_has_fmp_param then [Var runner] else []) /\
    (sig.fms_has_fmp_param ==> IS_SOME (fmp_stage_root infos ctx fn))
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  drule_all selected_invoke_resolves >> strip_tac >>
  drule fmp_resolve_invoke_some >> strip_tac >> fs[decode_invoke_def] >>
  `sig.fms_has_fmp_param ==> IS_SOME (fmp_stage_root infos ctx fn)` by
    (strip_tac >> irule selected_invoke_needs_root >> simp[] >>
     conj_tac
     >- (qexistsl [`fmp_info_of_signature sig`,`ivk`,`name`,`args`] >>
         simp[fmp_info_of_signature_def, decode_invoke_def]) >>
     metis_tac[]) >>
  qexistsl [`callee`,`sig`] >> gvs[] >>
  drule_all fmp_lower_invoke_inst >> strip_tac >>
  gvs[decode_invoke_def, fmp_info_of_signature_def] >>
  metis_tac[lookup_function_name]
QED

Theorem selected_invoke_frame_decode[local]:
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tv s t /\
  ALL_DISTINCT (fn_labels fn) /\ fn_inst_ids_distinct fn' /\
  fn.fn_fmp_signature = NONE /\ active_inst fn ivk s /\
  MEM ivk (fn_insts fn) /\ ivk.inst_opcode = INVOKE /\
  decode_invoke ivk = SOME (nm,ops) /\
  MEM j (fn_insts fn') /\ j.inst_id = ivk.inst_id ==>
  ?runner has.
    decode_invoke j = SOME (nm,ops ++ if has then [Var runner] else []) /\
    (has ==> lookup_var runner t = SOME (n2w lo))
Proof
  strip_tac >> drule_all active_inst_lookup_distinct >>
  simp[get_instruction_def, AllCaseEqs()] >> strip_tac >>
  qhdtm_x_assum `fmp_frame_rel` mp_tac >> simp[fmp_frame_rel_def] >>
  disch_then (qx_choose_then `infos` (qx_choose_then `ctx`
    (qx_choose_then `runner` strip_assume_tac))) >>
  drule_all selected_invoke_lowering >> disch_then assume_tac >>
  drule_all selected_invoke_decode >> strip_tac >>
  qexistsl [`runner`,`sig.fms_has_fmp_param`] >> simp[] >> strip_tac >>
  `IS_SOME (fmp_stage_root infos ctx fn)` by simp[] >>
  Cases_on `fmp_stage_root infos ctx fn` >> gvs[] >> PairCases_on `x` >> gvs[] >>
  `~(t.vs_current_bb = x0 /\ s.vs_inst_idx < x1)` by
    (strip_tac >>
     `~MEM (EL s.vs_inst_idx bb.bb_instructions).inst_opcode
          [PARAM; RETPC_PARAM; FMP_PARAM]` by simp[] >>
     `lookup_block x0 fn.fn_blocks = SOME bb` by metis_tac[] >>
     `x1 <= s.vs_inst_idx` by metis_tac[fmp_stage_past_root] >>
     decide_tac) >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[]
QED

(* The sealed-callee signature in the scheduled caller's view determines
   the ABI of the actual C4 callee, even if the frame used another view. *)
Theorem selected_invoke_scheduled_abi[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C3 C4 /\
  lookup_function fn.fn_name C3.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C4.ctx_functions = SOME fn' /\
  lookup_function nm C4.ctx_functions = SOME callee' /\
  ALL_DISTINCT (fn_labels fn) /\ fn_inst_ids_distinct fn' /\
  fn.fn_fmp_signature = NONE /\ active_inst fn ivk s /\
  MEM ivk (fn_insts fn) /\ ivk.inst_opcode = INVOKE /\
  decode_invoke ivk = SOME (nm,ops) /\
  MEM j (fn_insts fn') /\ j.inst_id = ivk.inst_id ==>
  ?sig runner. callee'.fn_fmp_signature = SOME sig /\
    decode_invoke j = SOME (nm,ops ++ if sig.fms_has_fmp_param then [Var runner] else [])
Proof
  strip_tac >>
  `?observed sp out. fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) observed sp fn out /\
    out.fpo_function = fn' /\ o1_walk_view rpolicy 3 C4 fn observed` by
    (drule_all ctx_pass_stage_lookup >> strip_tac >> gvs[] >> metis_tac[]) >>
  `?infos runner. fmp_stage_lowered infos observed.cu_context runner fn fn'` by
    (`ir_supply_covers_fn sp fn` by
       (irule ir_supply_covers_unit_member >> qexists `observed` >>
        gvs[fn_pass_step_def] >> metis_tac[lookup_unique_function_member]) >>
     drule fmp_fn_pass_step_result >> strip_tac >>
     gvs[fmp_lower_function_def, AllCaseEqs(), fmp_stage_lowered_def] >>
     metis_tac[]) >>
  `MEM nm (fn_invoke_targets fn)` by
    (simp[fn_invoke_targets_def, fcg_scan_function_def, mem_get_invoke_targets] >>
     gvs[decode_invoke_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all fmp_call_walk_signature >> strip_tac >>
  drule_all selected_invoke_lowering >> disch_then assume_tac >>
  drule_all selected_invoke_decode >> strip_tac >>
  qexistsl [`sig`,`runner`] >> gvs[]
QED
