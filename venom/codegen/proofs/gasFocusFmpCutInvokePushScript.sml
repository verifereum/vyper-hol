(* Static ABI and actual callee entry at a restored bounded INVOKE. *)
Theory gasFocusFmpCutInvokePush
Ancestors fmpStageCallArity[qualified]
  gasFocusFmpCutInvokeSite fmpStageFmpStepsInvokePosition
  fmpStageFmpStepsCallAbi fmpStageRel fmpLowerDefs fmpAnalysisDefs
  fmpAnalysisProps fcgBridge fcgDefs concretizeStageLookup fmpStepBridge
  venomPassSchedule venomFnScheduleRunner venomFnScheduleRunnerProps
  dftGasToListReachBoundary venomInstIdsProps venomExecProofs
  venomInst venomExecSemantics venomWf o1PassContract unitShapeDefs
  fmpStageOpBase fmpStageFmpStepsCallArgs fmpStageFmpStepsCallEntry
  fmpStageFmpStepsCallPush ptrDiscipline o1LowerDloadJointInternalEffects
  tupleLoadProps venomState fmpStepLayout
  o1MakeSsaRows o1ContractMakeSsaReplay o1ContractSimplifyCfg
  o1ContractSimplifyCfgParams o1ContractSue o1ContractSueStep o1DftStep
  o1ContractCfgNorm o1ContractCfgNormStep
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
    LENGTH ops = LENGTH (fn_user_param_insts callee) /\
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
    decode_invoke j = SOME (nm,ops ++ if sig.fms_has_fmp_param then [Var runner] else []) /\
    LENGTH ops = LENGTH (fn_user_param_insts callee')
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
  `?g. lookup_function nm observed.cu_context.ctx_functions = SOME g /\
       fn_steps_from (\m h. o1_fn_shape C4 h /\ o1_fn_row m h) rpolicy 4
         (DROP 4 o1_fn_passes) callee' g` by
    (qpat_assum `o1_walk_view rpolicy 3 C4 fn observed`
       (mp_tac o REWRITE_RULE [o1_walk_view_def,walk_view_def]) >>
     disch_then (qspecl_then [`nm`,`callee'`] mp_tac) >> simp[]) >>
  drule fmpStageCallArityTheory.o1_walk_suffix_user_param_count >> strip_tac >>
  qexistsl [`sig`,`runner`] >> gvs[]
QED

(* Compare the two decoded suffix lengths to recover the actual ABI bit. *)
Theorem selected_invoke_abi[local]:
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tv s t /\
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C3 C4 /\
  lookup_function fn.fn_name C3.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C4.ctx_functions = SOME fn' /\
  lookup_function nm C3.ctx_functions = SOME callee /\
  lookup_function nm C4.ctx_functions = SOME callee' /\
  fmp_stage_lowered ci cc cr callee callee' /\
  callee.fn_fmp_signature = NONE /\ ~fn_is_context_entry cc callee /\
  ALL_DISTINCT (fn_labels fn) /\ fn_inst_ids_distinct fn' /\
  fn.fn_fmp_signature = NONE /\ active_inst fn ivk s /\
  MEM ivk (fn_insts fn) /\ ivk.inst_opcode = INVOKE /\
  decode_invoke ivk = SOME (nm,ops) /\
  MEM j (fn_insts fn') /\ j.inst_id = ivk.inst_id ==>
  ?r extra. decode_invoke j = SOME (nm,ops ++ extra) /\
    extra = (if IS_SOME (fmp_stage_root ci cc callee) then [Var r] else []) /\
    (IS_SOME (fmp_stage_root ci cc callee) ==> lookup_var r t = SOME (n2w lo)) /\
    LENGTH ops = LENGTH (fn_user_param_insts callee)
Proof
  strip_tac >>
  `LENGTH (fn_user_param_insts callee') = LENGTH (fn_user_param_insts callee)` by
    (qpat_assum `lookup_function nm C3.ctx_functions = SOME callee`
       (mp_then (Pos (el 2)) mp_tac ctx_pass_stage_lookup) >>
     disch_then drule >> simp[] >> strip_tac >>
     drule fmp_fn_pass_step_result >> strip_tac >>
     drule fmp_lower_function_user_param_count >> gvs[]) >>
  drule_all selected_invoke_frame_decode >>
  disch_then (qx_choose_then `r` (qx_choose_then `has` strip_assume_tac)) >>
  drule_all selected_invoke_scheduled_abi >> strip_tac >>
  drule_all fmp_call_lowered_signature_root >> strip_tac >> gvs[] >>
  `has <=> IS_SOME (fmp_stage_root ci cc callee)` by
    (Cases_on `has` >> Cases_on `IS_SOME (fmp_stage_root ci cc callee)` >> gvs[]) >>
  qexists `r` >> gvs[]
QED

Theorem selected_invoke_arguments[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\
  active_inst fn ivk s /\ ivk.inst_opcode = INVOKE /\
  ivk.inst_operands = Label nm :: ops /\ taint_ok fn tn ivk s /\
  eval_operands ops s = SOME args /\
  fmp_stage_rel D C4 sm fmp0 raw0 eom T stk PG G tn fn s lo t ts ==>
  ?ys. eval_operands ops t = SOME ys /\ LENGTH ys = LENGTH args /\
    LENGTH args = LENGTH ops /\
    (!k. k < LENGTH args ==>
       fmp_value_rel sm (EL k (MAP (op_prov G) ops)) {} (EL k args) (EL k ys))
Proof
  strip_tac >>
  `!op x. MEM op ops /\ eval_operand op s = SOME x ==>
     ?y. eval_operand op t = SOME y /\ fmp_value_rel sm (op_prov G op) {} x y` by
    (rpt strip_tac >>
     `MEM op ivk.inst_operands /\ ivk.inst_opcode <> PHI` by simp[] >>
     `!v. op = Var v ==> ~retpc_var fn v` by
       (rpt strip_tac >> spose_not_then assume_tac >>
        `retpc_use_ok ivk v` by
          metis_tac[opaque_use_ok_retpc_use, allocaFrontierBoundTheory.active_inst_mem_fn_insts] >>
        gvs[retpc_use_ok_def]) >>
     drule_all taint_ok_invoke_operand >> strip_tac >>
     drule_all fmp_stage_operand_point >> simp[]) >>
  `EVERY (\op. IS_SOME (eval_operand op s)) ops` by
    metis_tac[ld_eval_operands_defined, optionTheory.IS_SOME_DEF] >>
  `IS_SOME (eval_operands ops t)` by
    (simp[ld_eval_operands_defined, EVERY_MEM] >> fs[EVERY_MEM] >>
     metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  fs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `eval_operands ops t = SOME ys` >>
  `LENGTH ys = LENGTH ops /\ LENGTH args = LENGTH ops` by
    metis_tac[tupleLoadPropsTheory.eval_operands_length] >>
  simp[EL_MAP] >> rpt strip_tac >>
  `k < LENGTH ops` by simp[] >>
  `eval_operand (EL k ops) s = SOME (EL k args) /\
   eval_operand (EL k ops) t = SOME (EL k ys)` by
    metis_tac[eval_operands_index] >>
  metis_tac[EL_MEM, optionTheory.SOME_11]
QED

(* Enter with independently evaluated argument lists. Only the appended
   runner word, if present, is fixed by the target ABI. *)
Theorem selected_invoke_entry[local]:
  fmp_stage_rel D C4 sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function callee.fn_name C4.ctx_functions = SOME callee' /\
  fmp_stage_lowered ci cc cr callee callee' /\ ~fn_is_context_entry cc callee /\
  wf_function callee /\ first_block_no_phi callee /\ ~s.vs_halted /\
  setup_callee callee args s = SOME cs /\ enters_block callee cs s1 /\
  LENGTH args = LENGTH (fn_user_param_insts callee) /\
  eval_operands ops t = SOME ys /\ LENGTH ys = LENGTH args /\
  LENGTH args = LENGTH ops /\
  (!k. k < LENGTH args ==>
       fmp_value_rel sm (EL k (MAP (op_prov G) ops)) {} (EL k args) (EL k ys)) /\
  extra = (if IS_SOME (fmp_stage_root ci cc callee) then [Var r] else []) /\
  (IS_SOME (fmp_stage_root ci cc callee) ==> lookup_var r t = SOME (n2w lo)) ==>
  ?args' cs'. eval_operands (ops ++ extra) t = SOME args' /\
    setup_callee callee' args' t = SOME cs' /\ enters_block callee' cs' cs' /\
    fmp_stage_rel D C4 sm fmp0 raw0 eom F
      (<|cf_fn := fn; cf_inst := ivk; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY)
      callee s1 lo cs' ((t,lo)::ts)
Proof
  strip_tac >>
  drule_all fmpStageRunnerFactsTheory.fmp_stage_lowered_shape >> strip_tac >>
  `first_block_no_phi callee'` by metis_tac[] >>
  `?zs. eval_operands extra t = SOME zs /\
    (!rl rp. fmp_stage_root ci cc callee = SOME (rl,rp) ==> zs = [n2w lo])` by
    (Cases_on `fmp_stage_root ci cc callee` >> gvs[eval_operands_def,eval_operand_def]) >>
  `eval_operands (ops ++ extra) t = SOME (ys ++ zs)` by
    simp[venomOperandPropsTheory.eval_operands_append] >>
  `?ct. setup_callee callee' (ys ++ zs) t = SOME ct` by
    (Cases_on `callee'.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def, setup_callee_def] >>
     Cases_on `callee.fn_blocks` >> gvs[entry_block_def,setup_callee_def]) >>
  `enters_block callee' ct ct` by metis_tac[fmp_call_setup_entry] >>
  `fmp_params_rel sm (MAP (op_prov G) ops) cs ct` by
    (irule fmp_params_rel_append >> simp[] >> metis_tac[setup_callee_frame]) >>
  `!rl rp. fmp_stage_root ci cc callee = SOME (rl,rp) ==>
     LENGTH args < LENGTH (ys ++ zs) /\ EL (LENGTH args) (ys ++ zs) = n2w lo` by
    (rpt strip_tac >> `zs = [n2w lo]` by metis_tac[] >> simp[EL_APPEND_EQN]) >>
  `fmp_frame_rel sm fmp0 raw0 (w2n s.vs_fmp) lo lo F
    callee callee' (MAP (op_prov G) ops) FEMPTY FEMPTY s1 ct` by
    (irule fmp_call_frame_entry >>
     gvs[fmp_stage_rel_def] >>
     qhdtm_assum `fmp_frame_rel` (irule_at Any) >>
     goal_assum $ drule_at Any >> goal_assum $ drule_at Any >>
     goal_assum $ drule_at Any >> simp[] >>
     qhdtm_assum `fmp_stage_lowered` (irule_at Any) >>
     goal_assum $ drule_at Any >> simp[]) >>
  qexistsl [`ys ++ zs`,`ct`] >> simp[] >> irule fmp_stage_call_push >>
  `s1 = cs` by metis_tac[fmp_call_setup_entry] >>
  `~t.vs_halted` by fs[fmp_stage_rel_def] >>
  gvs[setup_callee_def]
QED

Theorem focus_fmp_cut_invoke_push:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C3 C4 /\
  o1_ctx_shape C3 /\ o1_ctx_shape C4 /\ o1_pre 3 C3 C4 /\
  lookup_function fn.fn_name C3.ctx_functions = SOME fn /\
  lookup_function nm C3.ctx_functions = SOME callee /\ C3.ctx_entry <> SOME nm /\
  fn.fn_fmp_signature = NONE /\ callee.fn_fmp_signature = NONE /\
  active_inst fn ivk s /\ ~s.vs_halted /\ ivk.inst_opcode = INVOKE /\
  decode_invoke ivk = SOME (nm,ops) /\ taint_ok fn tn ivk s /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\
  fmp_stage_rel D C4 sm fmp0 raw0 eom T stk PG G tn fn s lo t ts ==>
  fmp_saved_rel C4 sm fmp0 raw0
    (<|cf_fn := fn; cf_inst := ivk; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk) ((t,lo)::ts) /\
  ?fn' bb bb' ivk' infos ctx runner callee' ci cc cr extra r args' cs' t1.
    lookup_function fn.fn_name C4.ctx_functions = SOME fn' /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    fmp_stage_lowered infos ctx runner fn fn' /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx =
      fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
        s.vs_current_bb bb.bb_instructions s.vs_inst_idx +
      (if (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
       then 1 else 0) /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    t.vs_inst_idx < LENGTH bb'.bb_instructions /\
    EL t.vs_inst_idx bb'.bb_instructions = ivk' /\
    active_inst fn' ivk' t /\ ivk'.inst_opcode = INVOKE /\ ivk'.inst_id = ivk.inst_id /\
    lookup_function nm C4.ctx_functions = SOME callee' /\
    fn_entry_label callee' = fn_entry_label callee /\
    fmp_stage_lowered ci cc cr callee callee' /\ ~fn_is_context_entry cc callee /\
    decode_invoke ivk' = SOME (nm,ops ++ extra) /\
    extra = (if IS_SOME (fmp_stage_root ci cc callee) then [Var r] else []) /\
    (IS_SOME (fmp_stage_root ci cc callee) ==> lookup_var r t = SOME (n2w lo)) /\
    eval_operands (ops ++ extra) t = SOME args' /\
    setup_callee callee' args' t = SOME cs' /\ enters_block callee' cs' t1 /\
    fmp_stage_rel D C4 sm fmp0 raw0 eom F
      (<|cf_fn := fn; cf_inst := ivk; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY)
      callee s1 lo t1 ((t,lo)::ts)
Proof
  strip_tac >> drule_all focus_fmp_cut_invoke_saved_site >> strip_tac >>
  rename1 `active_inst fn' ivk' t` >>
  rename1 `lookup_function nm C4.ctx_functions = SOME callee'` >>
  rename1 `fmp_stage_lowered ci cc cr callee callee'` >>
  `MEM fn C3.ctx_functions /\ MEM callee C3.ctx_functions /\
   MEM fn' C4.ctx_functions /\ callee.fn_name = nm` by
    metis_tac[lookup_function_MEM, lookup_function_name] >>
  `wf_function fn /\ wf_function fn' /\ wf_function callee /\
   first_block_no_phi callee /\ opaque_use_ok fn` by
    (fs[o1_ctx_shape_def,EVERY_MEM] >> metis_tac[o1_fn_shape_def,fn_shape_ok_def]) >>
  `make_ssa_input_ok fn` by
    (fs[o1_pre_def, EVERY_MEM] >> metis_tac[o1_fn_row_def, DECIDE ``3 <= 4``]) >>
  `ALL_DISTINCT (fn_labels fn) /\ fn_inst_ids_distinct fn'` by
    (fs[wf_function_def, o1_ctx_shape_def, fn_inst_ids_distinct_def] >>
     metis_tac[allocaFrontierBoundTheory.ctx_inst_ids_distinct_fn]) >>
  `MEM ivk (fn_insts fn)` by metis_tac[allocaFrontierBoundTheory.active_inst_mem_fn_insts] >>
  `?eb elo. fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tn.t_var s t` by
    (fs[fmp_stage_rel_def] >> metis_tac[optionTheory.SOME_11]) >>
  pop_assum strip_assume_tac >>
  `~fn_is_context_entry cc callee` by simp[] >>
  drule_all selected_invoke_abi >> strip_tac >>
  `ivk.inst_operands = Label nm :: ops` by gvs[decode_invoke_def,AllCaseEqs()] >>
  drule_all selected_invoke_arguments >> strip_tac >>
  `LENGTH args = LENGTH (fn_user_param_insts callee)` by simp[] >>
  `lookup_function callee.fn_name C4.ctx_functions = SOME callee'` by simp[] >>
  drule_all selected_invoke_entry >> disch_then (qspec_then `ivk` strip_assume_tac) >>
  conj_tac >- simp[] >>
  qexistsl [`fn'`,`bb`,`bb'`,`ivk'`,`infos`,`ctx`,`runner`,`callee'`,`ci`,`cc`,`cr`,
            `extra`,`r`,`args'`,`cs'`,`cs'`] >> simp[]
QED
