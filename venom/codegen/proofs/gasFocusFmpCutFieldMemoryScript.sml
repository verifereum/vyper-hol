(* Backward coverage for memory observations at the actual C4 gas cut. *)
Theory gasFocusFmpCutFieldMemory
Ancestors
  gasFocusFmpCutEntryStatic gasFocusFmpStagePin o1LowerDloadSourceEntry
  fmpStageCoverInv fmpStageCoverMem fmpStageRel fmpLowerDefs fmpStepLayout
  fmpStepStructural fmpAnalysisProps fmpStageFmpStepsEntryLayout
  o1PassContract o1SafeUpto unitMemInv unitTransformDefs ptrDiscipline
  ctxLookupAgreeHelpers gasFocusFmpCutResidual concretizeLayoutCutSafe
  contextCodegenRel venomWf venomExecSemantics venomState venomInst
  lowerDloadSafetyAmbient o1LowerDloadPtrDiscipline lowerDloadPtrSupport
  o1ContractSimplifyCfgSrcFrame simplifyCfgAvailability ptrStaticDiscipline
  allocaFrontierBound finite_map words list arithmetic
  fmpStageControl fmpStageCallArity fmpStageCoverBackParam
  fmpStageCoverBackKeptOps fmpCoverInvokeIndex lowerDloadPtrRawReachable
  gasFocusFmpCutSites gasFocusFmpCutSegments gasFocusFmpCutRestorePrefix
  fmpStageFmpStepsRestoreControl fmpStepReclaim analysisSimDefs
  gasFocusFmpCutForwardLayout gasFocusFmpRetpcPoint
  lowerDloadNormalDispatch o1LowerDloadJointRetpc gasFocusFmpCutSourceJump
  gasFocusFmpCutJumpEntry gasFocusFmpJumpPoint fmpStageRunnerFacts
  gasFocusFmpCutSourceCall gasFocusFmpCutInvokePush gasFocusFmpCutInvokeOutputs
  gasFocusFmpCutSourceReturn gasFocusFmpCutInvokePop gasFocusFmpCutPointMemory
  concretizePtrCoverageStaticMemReachability

Theorem cut_source_entry:
  wf_function fn /\ first_block_no_phi fn /\ fn_entry_label fn = SOME lbl ==>
  ?inst. active_inst fn inst
    (root with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
Proof
  Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >>
  strip_tac >> rename1 `fn.fn_blocks = bb::bbs` >>
  `bb.bb_instructions <> []` by metis_tac[wf_function_def, bb_well_formed_def, MEM] >>
  Cases_on `bb.bb_instructions` >>
  gvs[active_inst_def, get_instruction_def, lookup_block_def, FIND_thm] >>
  qexists_tac `bb` >> simp[]
QED

Theorem cut_target_entry[local]:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  C3.ctx_entry = SOME name /\ lookup_function name C3.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\ wf_function fn /\ entry_fn_no_params fn /\
  first_block_no_phi fn /\ fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn /\
  o1_initial_state_ok v /\ v.vs_fmp = v.vs_initial_fmp /\ code_layout_valid v /\
  w2n v.vs_initial_fmp <= w2n fmp ==>
  ?fn' bb p u inst.
    lookup_function name C4.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl /\ first_block_no_phi fn' /\
    lookup_block lbl fn'.fn_blocks = SOME bb /\
    ?s. s = (v with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                       vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
    ?t. t = (v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
      frame_reachable (v with <|vs_fmp := fmp; vs_initial_fmp := fmp|>)
        C3 [] [] FEMPTY entry_taint fn inst s /\ active_inst fn inst s /\ ~s.vs_halted /\
      fmp_stage_rel D C4 FEMPTY (w2n v.vs_initial_fmp) (w2n fmp) eom F
        [] [] FEMPTY entry_taint fn s (w2n v.vs_initial_fmp) u [] /\
      u.vs_current_bb = lbl /\ u.vs_inst_idx = p /\
      u.vs_gas_readings = v.vs_gas_readings /\
      (!k. fmp_target_run k C4 name t p u) /\
      (!i. i < p ==> i < LENGTH bb.bb_instructions /\
                       fmp_inserted_op (EL i bb.bb_instructions).inst_opcode)
Proof
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_THM2)) >>
  strip_tac >> drule_all focus_fmp_selected_root_pin >> strip_tac >>
  `?ctx1 sp sp'. fmp_lower_function ctx1 sp fn = SOME (fn',sp')` by
    (fs[fmp_stage_lowered_def] >>
     rename1 `fmp_lower_function_with_info info0 ctx0 supply fn = SOME (fn',supply')` >>
     qexistsl [`ctx0`, `supply`, `supply'`] >> simp[fmp_lower_function_def]) >>
  `first_block_no_phi fn'` by metis_tac[fmp_lower_function_first_block_no_phi] >>
  `?bb. lookup_block lbl fn'.fn_blocks = SOME bb` by
    metis_tac[fmp_entry_target_block] >>
  qabbrev_tac `root = v with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  qabbrev_tac `s = root with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` >>
  `enters_block fn s s` by
    (simp[Abbr `s`] >> metis_tac[dload_no_phi_entry]) >>
  `?inst. active_inst fn inst s` by
    (simp[Abbr `s`] >> metis_tac[cut_source_entry]) >>
  `frame_reachable root C3 [] [] FEMPTY entry_taint fn inst s` by
    (irule frame_reachable_entry >> metis_tac[Abbr `s`]) >>
  mp_tac (Q.INST [`u` |-> `root`, `s` |-> `s`, `v` |-> `v`,
                   `rpolicy` |-> `rp`, `D` |-> `D`, `eom` |-> `eom`]
                 focus_fmp_cut_entry_static) >>
  impl_tac >- (simp[Abbr `root`] >> metis_tac[Abbr `s`]) >>
  disch_then (qx_choose_then `f4` (qx_choose_then `p` (qx_choose_then `u4` strip_assume_tac))) >>
  qexistsl [`f4`, `bb`, `p`, `u4`, `inst`] >>
  gvs[Abbr `root`, Abbr `s`, o1_initial_state_ok_def, fmp_inserted_op_def,
      update_var_def, mk_inst_def]
QED

(* The first disjunct of the frame induction: the observed state is in
   an inserted slice leading to a related, cut-reachable source fetch. *)
val cut_matched = ``
  ?stk PG G tn fn inst s sm lo u ts restored bb.
    frame_reachable root3 C3 stk PG G tn fn inst s /\
    active_inst fn inst s /\ ~s.vs_halted /\ gas_cut n root3 s /\
    (restored ==> MEM inst.inst_opcode [DALLOCA; INVOKE] \/
                  is_terminator inst.inst_opcode) /\
    fmp_stage_rel D C4 sm (w2n root4.vs_initial_fmp) (w2n (fmp:256 word)) eom restored
      stk PG G tn fn s lo u ts /\
    lookup_function fn.fn_name C4.ctx_functions = SOME fn' /\
    fmp_cov_stack C4 stk ts stk' /\
    LIST_REL (\f g. g.cf_inst.inst_outputs = f.cf_inst.inst_outputs) stk stk' /\
    t.vs_current_bb = u.vs_current_bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
    t.vs_inst_idx <= u.vs_inst_idx /\
    s.vs_gas_readings = u.vs_gas_readings /\ u.vs_gas_readings = t.vs_gas_readings /\
    (!k. fmp_target_run k C4 fn.fn_name t (u.vs_inst_idx - t.vs_inst_idx) u) /\
    (!i. t.vs_inst_idx <= i /\ i < u.vs_inst_idx ==>
         i < LENGTH bb.bb_instructions /\
         fmp_inserted_op (EL i bb.bb_instructions).inst_opcode)``;

Theorem cut_matched_entry[local]:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  C3.ctx_entry = SOME name /\ lookup_function name C3.ctx_functions = SOME src /\
  fn_entry_label src = SOME src_lbl /\ o1_ctx_shape C3 /\ fmp_free_ctx C3 /\
  o1_initial_state_ok root4 /\ root4.vs_fmp = root4.vs_initial_fmp /\
  code_layout_valid root4 /\ w2n root4.vs_initial_fmp <= w2n fmp /\
  root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  C4.ctx_entry = SOME name' /\ lookup_function name' C4.ctx_functions = SOME fn' /\
  fn_entry_label fn' = SOME lbl /\
  enters_block fn' (root4 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  gas_cut n root4 t ==>
  ^(subst [``stk':call_frame list`` |-> ``[]:call_frame list``] cut_matched)
Proof
  strip_tac >>
  `name' = name` by fs[ctx_pass_stage_def] >>
  `MEM src C3.ctx_functions /\ src.fn_name = name` by
    metis_tac[lookup_function_MEM, lookup_function_selected_name] >>
  `wf_function src /\ first_block_no_phi src /\ entry_fn_no_params src /\
   src.fn_fmp_signature = NONE /\ pre_fmp_ops src` by
    (fs[o1_ctx_shape_def, fmp_free_ctx_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  drule_all cut_target_entry >>
  disch_then (qspecl_then [`eom`, `D`] strip_assume_tac) >> gvs[] >>
  qpat_x_assum `enters_block _ _ _` mp_tac >> simp[dload_no_phi_entry] >>
  disch_then SUBST_ALL_TAC >>
  qexistsl [`[]`, `FEMPTY`, `entry_taint`, `src`, `inst`,
    `root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp; vs_prev_bb := NONE;
                  vs_current_bb := u.vs_current_bb; vs_inst_idx := 0|>`,
    `FEMPTY`, `w2n root4.vs_initial_fmp`, `u`, `[]`, `F`] >>
  gvs[fmp_cov_stack_def, gas_cut_def]
QED

val cut_tail = ``
  ?bb p j. ALL_DISTINCT (fn_labels fn') /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
    revert_forward_pair bb p j /\ p < t.vs_inst_idx /\ t.vs_inst_idx <= j``;

val cut_fields = ``
  !stk PG G tn fn inst s.
    frame_reachable root3 C3 stk PG G tn fn inst s /\ gas_cut n root3 s ==>
    access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
    allocas_from eom s /\ (ctx_has_dalloca C3 ==> allocas_below_fmp s) /\
    (?P. fn_static_ptr_ok P fn /\ ptr_use_static_ok P (fn_pv P fn) inst /\
         FDOM G SUBSET fn_pv P fn)``;

Theorem cut_source_points:
  o1_ctx_shape C3 /\ EVERY (o1_fn_row 3) C3.ctx_functions /\
  fmp_free_ctx C3 /\ root3.vs_vars = FEMPTY /\ ~root3.vs_halted /\
  frame_reachable root3 C3 stk PG G tn fn inst s /\ active_inst fn inst s /\
  ^cut_fields /\ gas_cut n root3 s ==>
  lookup_function fn.fn_name C3.ctx_functions = SOME fn /\
  o1_fn_shape C3 fn /\ o1_fn_row 3 fn /\ fn_inst_wf fn /\ wf_function fn /\
  make_ssa_input_ok fn /\ pre_fmp_ops fn /\ fn.fn_fmp_signature = NONE /\
  (!v. inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
       IS_SOME (lookup_var v s)) /\
  access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
  allocas_from eom s /\ (ctx_has_dalloca C3 ==> allocas_below_fmp s) /\
  (?P. fn_static_ptr_ok P fn /\ ptr_use_static_ok P (fn_pv P fn) inst /\
       FDOM G SUBSET fn_pv P fn)
Proof
  strip_tac >>
  `!nm f. lookup_function nm C3.ctx_functions = SOME f ==> wf_function f` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  drule_all scfg_frame_reachable_entry_root >> strip_tac >>
  `lookup_function fn.fn_name C3.ctx_functions = SOME fn` by
    (drule_all scfg_frame_reachable_rooted >>
     disch_then (strip_assume_tac o MATCH_MP scfg_rooted_elim) >>
     metis_tac[lookup_function_selected_name]) >>
  `MEM fn C3.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `o1_fn_shape C3 fn /\ o1_fn_row 3 fn /\ fn.fn_fmp_signature = NONE` by
    (fs[o1_ctx_shape_def, fmp_free_ctx_def, EVERY_MEM] >> metis_tac[]) >>
  `wf_function fn /\ fn_inst_wf fn /\ make_ssa_input_ok fn /\ pre_fmp_ops fn` by
    fs[o1_fn_shape_def, o1_fn_row_def] >>
  `!v. inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
       IS_SOME (lookup_var v s)` by
    (fs[make_ssa_input_ok_def] >> metis_tac[scfg_frame_operand_defined]) >>
  qpat_assum `!stk PG G tn fn inst s. frame_reachable _ _ _ _ _ _ _ _ _ /\ _ ==> _`
    drule_all >> simp[]
QED

Theorem cut_source_call_arity:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  o1_ctx_shape C3 /\ fmp_free_ctx C3 ==>
  !stk PG G tn caller ivk st nm args callee.
    frame_reachable vs C3 stk PG G tn caller ivk st /\
    active_inst caller ivk st /\ ivk.inst_opcode = INVOKE /\
    ivk.inst_operands = Label nm::args /\
    lookup_function nm C3.ctx_functions = SOME callee ==>
    LENGTH (fn_user_param_insts callee) <= LENGTH args
Proof
  rpt strip_tac >>
  `MEM caller C3.ctx_functions` by metis_tac[frame_reachable_raw_certificate] >>
  `caller.fn_fmp_signature = NONE` by fs[fmp_free_ctx_def, EVERY_MEM] >>
  `lookup_function caller.fn_name C3.ctx_functions = SOME caller` by
    (irule fmpLowerPropsTheory.fmp_lookup_function_self >>
     fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  `MEM ivk (fn_insts caller)` by metis_tac[active_inst_mem_fn_insts] >>
  `decode_invoke ivk = SOME (nm,args)` by simp[decode_invoke_def] >>
  drule_all fmp_stage_invoke_arity_static >> simp[]
QED

Theorem cut_aligned_layout:
  wf_function fn /\ ALL_DISTINCT (fn_labels fn') /\
  active_inst fn inst s /\ active_inst fn' ti t /\
  fmp_stage_rel D C4 sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C4.ctx_functions = SOME fn' ==>
  ?infos ctx runner bs bt.
    fmp_stage_lowered infos ctx runner fn fn' /\
    t.vs_current_bb = s.vs_current_bb /\ w2n t.vs_initial_fmp = fmp0 /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bs /\
    s.vs_inst_idx < LENGTH bs.bb_instructions /\
    inst = EL s.vs_inst_idx bs.bb_instructions /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
    get_instruction bt t.vs_inst_idx = SOME ti /\
    t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) s.vs_current_bb bs.bb_instructions s.vs_inst_idx +
      (if restored /\ (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
       then 1 else 0)
Proof
  strip_tac >> drule_all fmp_cov_frame_pos >> strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  `?bs. lookup_block s.vs_current_bb fn.fn_blocks = SOME bs /\
        get_instruction bs s.vs_inst_idx = SOME inst` by
    metis_tac[active_inst_block_lookup] >>
  `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
        get_instruction bt t.vs_inst_idx = SOME ti` by
    metis_tac[active_inst_block_lookup] >>
  first_x_assum drule >> strip_tac >>
  qexistsl [`infos`, `ctx`, `runner`, `bs`, `bt`] >> fs[get_instruction_def]
QED

(* The induction stays on the observed C4 history. Each earlier source
   frame in its motive is independently reached from root3. *)
Theorem cut_frame_coverage:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  o1_pre 3 C3 C4 /\ o1_ctx_shape C3 /\ o1_ctx_shape C4 /\
  EVERY (o1_fn_row 3) C3.ctx_functions /\ EVERY ssa_form C3.ctx_functions /\
  C3.ctx_entry = SOME name /\ lookup_function name C3.ctx_functions = SOME src /\
  fn_entry_label src = SOME src_lbl /\
  o1_initial_state_ok root4 /\ root4.vs_fmp = root4.vs_initial_fmp /\
  code_layout_valid root4 /\ w2n root4.vs_initial_fmp <= w2n fmp /\
  root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  dead_wf D /\ fmp_free_ctx C3 /\ taint_within_upto D n C3 root3 /\
  (!g i v. raw_reachable root3 C3 g i v /\ gas_cut n root3 v ==> dalloca_no_wrap i v) /\
  ^cut_fields /\
  eom <= w2n root4.vs_initial_fmp /\ fmp_variant_room (SOME fmp) C4 root4 /\
  callee_first names C3.ctx_functions ==>
  !stk' PG' G' tn' fn' ti t.
    frame_reachable root4 C4 stk' PG' G' tn' fn' ti t /\ gas_cut n root4 t ==>
    ^cut_matched \/ ^cut_tail
Proof
  strip_tac >>
  `!vs ctx stk' PG' G' tn' fn' ti t.
     frame_reachable vs ctx stk' PG' G' tn' fn' ti t ==>
     vs = root4 /\ ctx = C4 /\ gas_cut n root4 t ==> ^cut_matched \/ ^cut_tail`
    suffices_by
      (disch_then (qspecl_then [`root4`, `C4`] mp_tac) >>
       rewrite_tac[] >> disch_then (fn th => rpt gen_tac >> strip_tac >>
         drule th >> simp[]) >> simp[]) >>
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac >>
  rpt strip_tac >> gvs[]
  >- (disj1_tac >>
      irule (SRULE [] (Q.INST
        [`root3` |-> `root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>`]
        cut_matched_entry)) >> metis_tac[])
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume cut_frame_coverage[next]:
  `gas_cut n root4 t` by
    (irule gas_cut_readings_mono >> qexists `s'` >>
     conj_tac >- metis_tac[step_inst_noninvoke_readings_le] >>
     fs[gas_cut_def]) >>
  qpat_x_assum `gas_cut n root4 t ==> _` drule >>
  reverse (disch_then strip_assume_tac)
  >- (disj2_tac >> drule_all focus_fmp_cut_tail_observation >>
      disch_then (qspecl_then [`eom`, `C4`] strip_assume_tac) >>
      first_x_assum drule_all >> simp[] >> strip_tac >>
      qexistsl [`p`, `j`] >> simp[] >> decide_tac) >>
  `ALL_DISTINCT (fn_labels fn')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  Cases_on `t.vs_inst_idx < u.vs_inst_idx`
  >- (disj1_tac >> drule_all focus_fmp_cut_inserted_residual >> strip_tac >>
      first_x_assum drule >> simp[] >> strip_tac >>
      qexistsl [`stk`, `PG`, `G`, `tn`, `fn`, `inst`, `s`, `sm`, `lo`, `u`, `ts`,
                `restored`, `bb`] >> gvs[] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `u = t` by
    (`u.vs_inst_idx - t.vs_inst_idx = 0` by decide_tac >>
     metis_tac[fmp_target_run_zero]) >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  `(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_vars = FEMPTY /\
   ~(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_halted` by
    fs[o1_initial_state_ok_def] >>
  drule_all cut_source_points >> strip_tac >>
  drule_all cut_aligned_layout >> strip_tac >>
  `opaque_use_ok fn /\ all_reachable fn` by
    fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def, make_ssa_input_ok_def] >>
  `ssa_form fn` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  qabbrev_tac `root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `w2n root3.vs_fmp = w2n fmp` by simp[Abbr `root3`] >>
  `inst.inst_opcode = DALLOCA ==> ?post. step_inst fuel C3 inst s = OK post` by
    (strip_tac >>
     `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
     `MEM bs fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
     `MEM inst bs.bb_instructions` by
       (simp[MEM_EL] >> qexists `s.vs_inst_idx` >> simp[]) >>
     `inst_wf inst` by
       (qpat_assum `fn_inst_wf fn` (mp_tac o REWRITE_RULE [fn_inst_wf_def]) >>
        disch_then (qspecl_then [`bs`, `inst`] mp_tac) >> simp[]) >>
     `inst_shape_ok inst` by
       fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def, EVERY_MEM] >>
     qpat_x_assum `inst_wf inst` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> strip_tac >>
     rename1 `_.inst_operands = [szop]` >>
     `?sz. eval_operand szop s = SOME sz` by
       (Cases_on `szop` >> gvs[eval_operand_def, unitShapeDefsTheory.inst_shape_ok_def,
          unitShapeDefsTheory.label_positions_ok_def, stackPlanTypesTheory.is_label_operand_def] >>
        metis_tac[optionTheory.IS_SOME_EXISTS]) >>
     metis_tac[lowerDloadPtrDallocaTheory.dalloca_step_success]) >>
  Cases_on `inst.inst_opcode = DALLOCA /\
    ?m l. fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n fmp) eom T stk PG G tn fn s l t ts`
  >- (qpat_x_assum `inst.inst_opcode = DALLOCA /\ _` strip_assume_tac >>
      rename1 `fmp_stage_rel D C4 m _ _ eom T stk PG G tn fn s l t ts` >>
      qpat_x_assum `inst.inst_opcode = DALLOCA ==> _` drule >>
      disch_then (qx_choose_then `post` assume_tac) >>
      `terminates (OK post)` by simp[passSimulationDefsTheory.terminates_def] >>
      `w2n fmp = w2n root3.vs_fmp` by simp[NoAsms, Abbr `root3`] >>
      qpat_assum `fmp_stage_rel D C4 m _ _ eom T stk PG G tn fn s l t ts`
        (mp_then Any drule_all focus_fmp_cut_dalloca_segment) >>
      disch_then (qx_choosel_then [`s1`, `t1`, `m1`, `sz`, `seg_fn`, `seg_bb`, `code`, `tail`,
        `op`, `out`, `runner'`, `plus31`, `mask`, `aligned`, `ai`, `ni`, `mi`, `bi`]
        (strip_assume_tac o SRULE [LET_THM])) >>
      `s1 = post /\ seg_fn = fn' /\ seg_bb = bb` by metis_tac[optionTheory.SOME_11] >>
      qpat_x_assum `s1 = post` SUBST_ALL_TAC >>
      qpat_x_assum `seg_bb = bb` SUBST_ALL_TAC >>
      `t1.vs_inst_idx = t.vs_inst_idx + 4` by
        (qpat_assum `!k. fmp_target_run k C4 _ t 4 t1`
           (qspec_then `fuel` mp_tac) >> simp[NoAsms, fmp_target_run_def] >>
         strip_tac >> simp[]) >>
      `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\ ~is_terminator inst.inst_opcode` by
        simp[is_terminator_def] >>
      `post.vs_current_bb = s.vs_current_bb /\
       post.vs_gas_readings = s.vs_gas_readings /\ ~post.vs_halted` by
        (`step_inst_base inst s = OK post` by
           (qpat_assum `step_inst fuel C3 inst s = OK post` mp_tac >>
            qpat_assum `inst.inst_opcode <> INVOKE`
              (fn th => simp[NoAsms, step_inst_non_invoke, th])) >>
         drule venomExecPropsTheory.step_inst_OK_preserves_halted >>
         drule_all venomInstPropsTheory.step_preserves_control_flow >>
         drule_all oracleExecPropsTheory.step_inst_noninvoke_gas_readings >> simp[]) >>
      `t1.vs_current_bb = t.vs_current_bb /\ post.vs_gas_readings = t1.vs_gas_readings` by
        (qpat_assum `fmp_stage_rel _ _ m1 _ _ _ F _ _ _ _ _ _ _ t1 _` mp_tac >>
         simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def,
              o1LowerDloadSharedTheory.ld_shared_agree_def] >>
         strip_tac >> metis_tac[]) >>
      `!i. t.vs_inst_idx <= i /\ i < t1.vs_inst_idx ==>
           i < LENGTH bb.bb_instructions /\
           fmp_inserted_op (EL i bb.bb_instructions).inst_opcode` by
        (qx_gen_tac `i` >> strip_tac >>
         `i - t.vs_inst_idx < 4 /\ i - t.vs_inst_idx + t.vs_inst_idx = i` by decide_tac >>
         `DROP t.vs_inst_idx bb.bb_instructions =
            mk_inst ai ADD [op; Lit 31w] [plus31]::mk_inst ni NOT [Lit 31w] [mask]::
            mk_inst mi AND [Var plus31; Var mask] [aligned]::
            mk_inst bi BUMP [Var runner'; Var aligned] [out; runner']::tail` by simp[] >>
         `i < LENGTH bb.bb_instructions` by
           (pop_assum (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
            simp[NoAsms, LENGTH_DROP] >> decide_tac) >>
         `EL i bb.bb_instructions = EL (i - t.vs_inst_idx) (DROP t.vs_inst_idx bb.bb_instructions)` by
           (qpat_assum `i - t.vs_inst_idx + t.vs_inst_idx = i` (fn idx =>
              qpat_assum `i < LENGTH bb.bb_instructions` (fn bound =>
                simp[NoAsms, EL_DROP, idx, bound]))) >>
         qpat_x_assum `EL i bb.bb_instructions = _` SUBST1_TAC >>
         `i - t.vs_inst_idx = 0 \/ i - t.vs_inst_idx = 1 \/
          i - t.vs_inst_idx = 2 \/ i - t.vs_inst_idx = 3` by decide_tac >>
         simp[fmp_inserted_op_def, mk_inst_def]) >>
      `t1.vs_inst_idx - t.vs_inst_idx = 4 /\ t.vs_inst_idx < t1.vs_inst_idx` by decide_tac >>
      `t.vs_current_bb = t1.vs_current_bb /\
       (!k. fmp_target_run k C4 fn.fn_name t (t1.vs_inst_idx - t.vs_inst_idx) t1)` by
        (conj_tac >- metis_tac[] >>
         qpat_assum `t1.vs_inst_idx - t.vs_inst_idx = 4` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      drule_all (Q.INST [`u` |-> `t1`] focus_fmp_cut_inserted_residual) >>
      strip_tac >> first_x_assum drule >>
      disch_then (strip_assume_tac o SRULE [LET_THM]) >>
      drule_all o1LowerDloadReadinessTheory.ld_nonterminator_successor >>
      disch_then (qx_choose_then `next` assume_tac) >>
      `gas_cut n root3 (post with vs_inst_idx := SUC s.vs_inst_idx)` by
        (qpat_assum `gas_cut n root3 s` mp_tac >>
         qpat_assum `post.vs_gas_readings = s.vs_gas_readings`
           (fn th => simp[NoAsms, gas_cut_def, th])) >>
      `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME bb /\
       t1.vs_gas_readings = s'.vs_gas_readings` by metis_tac[] >>
      disj1_tac >>
      qexistsl [`stk`, `PG`, `step_prov PG G inst post`, `step_taint inst s post tn`,
        `fn`, `next`, `post with vs_inst_idx := SUC s.vs_inst_idx`, `m1`,
        `l + venomLayout$ceil32 (w2n sz)`, `t1`, `ts`, `F`, `bb`] >>
      conj_tac >- (irule frame_reachable_next >> metis_tac[]) >>
      rpt conj_tac >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  reverse (Cases_on `restored`)
  >- (gvs[] >>
      drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`]
                             focus_fmp_cut_restore_prefix)) >>
      disch_then (qx_choosel_then
        [`rest_fn`, `rest_src`, `rest_bb`, `rest_infos`, `rest_ctx`,
         `rest_runner`, `rest_len`, `rest_post`, `rest_cut`] strip_assume_tac) >>
      (* Dispatch on the layout returned by this run certificate. *)
      reverse (Cases_on `FLOOKUP (fmp_stage_plan rest_infos rest_ctx fn)
                                    (s.vs_current_bb,s.vs_inst_idx)`) >>
      PRED_ASSUM (can optionSyntax.dest_option_case) mp_tac >> simp[] >> strip_tac
      >- (`rest_src = bs /\ rest_fn = fn' /\ rest_bb = bb` by
            metis_tac[optionTheory.SOME_11] >>
          `(s.vs_current_bb,s.vs_inst_idx) IN FDOM
             (fmp_stage_plan rest_infos rest_ctx fn)` by fs[FLOOKUP_DEF] >>
          `fmp_is_reclaim_point rest_infos (EL s.vs_inst_idx bs.bb_instructions)` by
            metis_tac[fmp_stage_plan_point] >>
          (SUBGOAL_THEN
             ``MEM (EL s.vs_inst_idx bs.bb_instructions).inst_opcode [DALLOCA; INVOKE] \/
               is_terminator (EL s.vs_inst_idx bs.bb_instructions).inst_opcode`` assume_tac >-
           (drule fmp_reclaim_point_opcodes >> simp[] >> strip_tac >> simp[is_terminator_def])) >>
          `rest_post = s' with vs_inst_idx := SUC t.vs_inst_idx` by
            (qpat_assum `!k. fmp_target_run k _ _ t _ rest_post`
              (qspec_then `fuel` mp_tac) >>
             gvs[fmp_target_run_def, TAKE1_DROP, run_insts_def, get_instruction_def,
                 arithmeticTheory.ADD1]) >>
          `s'.vs_current_bb = t.vs_current_bb /\ s'.vs_gas_readings = t.vs_gas_readings` by
            (qpat_assum `rest_post = update_var _ _ _ with vs_inst_idx := _`
               (mp_tac o AP_TERM ``\v:venom_state. (v.vs_current_bb,v.vs_gas_readings)``) >>
             qpat_assum `rest_post = s' with vs_inst_idx := _`
               (mp_tac o AP_TERM ``\v:venom_state. (v.vs_current_bb,v.vs_gas_readings)``) >>
             simp[NoAsms, update_var_def]) >>
          `!k. fmp_target_run k C4 fn.fn_name rest_post 0 rest_post` by
            (irule fmp_restore_target_run_zero >> metis_tac[]) >>
          disj1_tac >>
          qpat_assum `t.vs_inst_idx = fmp_stage_tidx _ _ _ _ _`
            (fn th => once_rewrite_tac [GSYM th]) >>
          qexistsl [`stk`, `PG`, `G`, `tn`, `fn`, `EL s.vs_inst_idx bs.bb_instructions`,
            `s`, `DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < rest_cut}`,
            `rest_cut`, `rest_post`, `ts`, `T`, `bb`] >>
          gvs[arithmeticTheory.ADD1]) >>
      `rest_src = bs /\ rest_fn = fn' /\ rest_bb = bb` by
        metis_tac[optionTheory.SOME_11] >>
      `~((s.vs_current_bb,s.vs_inst_idx) IN FDOM
            (fmp_stage_plan rest_infos rest_ctx fn))` by fs[FLOOKUP_DEF] >>
      `((EL s.vs_inst_idx bs.bb_instructions).inst_opcode <> INVOKE /\
        ~is_terminator (EL s.vs_inst_idx bs.bb_instructions).inst_opcode)` by
        (conj_tac
         >- (strip_tac >>
             drule_all (Q.INST [`infos` |-> `rest_infos`, `ctx` |-> `rest_ctx`,
                               `idx` |-> `s.vs_inst_idx`] fmp_stage_invoke_inst) >>
             gvs[get_instruction_def]) >>
         strip_tac >>
         `pre_fmp_opcode (EL s.vs_inst_idx bs.bb_instructions).inst_opcode` by
           (drule active_inst_mem_fn_insts >> disch_tac >>
            qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
            simp[]) >>
         `~MEM (EL s.vs_inst_idx bs.bb_instructions).inst_opcode
                [DALLOCA; INVOKE; RETPC_PARAM]` by
           (simp[] >> rpt conj_tac >> strip_tac >> fs[is_terminator_def]) >>
         `?bt. lookup_block s.vs_current_bb fn'.fn_blocks = SOME bt /\
                get_instruction bt t.vs_inst_idx = SOME (EL s.vs_inst_idx bs.bb_instructions)` by
           (mp_tac (Q.INST
              [`infos` |-> `rest_infos`, `ctx` |-> `rest_ctx`, `runner` |-> `rest_runner`,
               `lbl` |-> `s.vs_current_bb`, `idx` |-> `s.vs_inst_idx`, `bb` |-> `bs`,
               `inst` |-> `EL s.vs_inst_idx bs.bb_instructions`] fmp_stage_kept_inst) >>
            simp[get_instruction_def] >> metis_tac[]) >>
         `ti = EL s.vs_inst_idx bs.bb_instructions` by
           metis_tac[optionTheory.SOME_11] >> fs[]) >>
      Cases_on `(EL s.vs_inst_idx bs.bb_instructions).inst_opcode = DALLOCA`
      >- (qpat_x_assum `rest_post = t` SUBST_ALL_TAC >>
          qpat_x_assum `rest_cut = lo` SUBST_ALL_TAC >>
          gvs[]) >>
      rename1 `active_inst fn (EL s.vs_inst_idx bs.bb_instructions) s` >>
      qabbrev_tac `si = EL s.vs_inst_idx bs.bb_instructions` >>
      reverse (Cases_on `si.inst_opcode = RETPC_PARAM`)
      >- (`pre_fmp_opcode si.inst_opcode` by
            (drule active_inst_mem_fn_insts >> disch_tac >>
             qpat_assum `pre_fmp_ops fn`
               (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >> simp[]) >>
          `~MEM si.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by simp[] >>
          `si = EL s.vs_inst_idx bs.bb_instructions` by simp[Abbr `si`] >>
          drule_all (Q.INST [`infos` |-> `rest_infos`, `ctx` |-> `rest_ctx`,
                             `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
          disch_then (qx_choose_then `kept_bb` strip_assume_tac) >>
          `kept_bb = bb` by metis_tac[optionTheory.SOME_11] >>
          qpat_x_assum `kept_bb = bb` SUBST_ALL_TAC >>
          `get_instruction bb t.vs_inst_idx = SOME si` by
            ((qpat_assum `~(_ IN FDOM (fmp_stage_plan rest_infos rest_ctx fn))` (fn absent =>
             qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan rest_infos rest_ctx fn) _ _ _ _`
              (fn idx =>
               qpat_x_assum `_ < LENGTH bb.bb_instructions` (mp_tac o SRULE [NoAsms, absent, GSYM idx]) >>
               qpat_x_assum `EL _ bb.bb_instructions = si` (mp_tac o SRULE [NoAsms, absent, GSYM idx]) >>
               simp[NoAsms, get_instruction_def]))) >> (metis_tac[NoAsms, get_instruction_def])) >>
          `ti = si` by metis_tac[optionTheory.SOME_11] >>
          qpat_x_assum `ti = si` SUBST_ALL_TAC >>
          `s'.vs_current_bb = t.vs_current_bb` by
            metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
          Cases_on `in_revert_forward fn s`
          >- (`?j. revert_forward_pair bs s.vs_inst_idx j` by
                (`get_instruction bs s.vs_inst_idx = SOME si` by
                   simp[get_instruction_def, Abbr `si`] >>
                 qpat_assum `in_revert_forward fn s` (mp_tac o REWRITE_RULE [in_revert_forward_def]) >>
                 disch_then (qx_choose_then `fwd_bb` strip_assume_tac) >>
                 `fwd_bb = bs` by metis_tac[optionTheory.SOME_11] >>
                 qpat_x_assum `fwd_bb = bs` SUBST_ALL_TAC >>
                 qpat_x_assum `revert_forward_at bs _`
                   (qx_choose_then `j` strip_assume_tac o REWRITE_RULE [revert_forward_at_def])
                 >- (qexists `j` >> first_assum ACCEPT_TAC) >>
                 qpat_x_assum `revert_forward_pair bs j _` mp_tac >>
                 simp[NoAsms, revert_forward_pair_def] >> strip_tac >>
                 `inst2 = si` by metis_tac[optionTheory.SOME_11] >> fs[is_terminator_def]) >>
              drule_all (SRULE [LET_THM] (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                                `p` |-> `s.vs_inst_idx`]
       (CONV_RULE (TOP_DEPTH_CONV Unwind.UNWIND_FORALL_CONV)
          focus_fmp_cut_forward_layout))) >>
              disch_then (qx_choose_then `target_fwd` strip_assume_tac) >>
              `s.vs_inst_idx < j` by metis_tac[revert_forward_pair_def] >>
              `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME target_fwd` by metis_tac[] >>
              `revert_forward_pair target_fwd t.vs_inst_idx (t.vs_inst_idx + (j - s.vs_inst_idx))` by
                metis_tac[] >>
              disj2_tac >>
              qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn) _ _ _ _`
                (SUBST1_TAC o SYM) >>
              qexistsl [`target_fwd`, `t.vs_inst_idx`, `t.vs_inst_idx + (j - s.vs_inst_idx)`] >>
              conj_tac >- first_assum ACCEPT_TAC >>
              conj_tac >- first_assum ACCEPT_TAC >> decide_tac) >>
          `si.inst_opcode <> PHI` by
            (strip_tac >>
             qpat_assum `si.inst_opcode = PHI` (fn opc =>
               qpat_assum `step_inst fuel C4 si t = OK s'`
                 (mp_tac o SRULE [NoAsms, opc, step_inst_non_invoke,
                                  step_inst_base_opcode_eqs])) >> simp[]) >>
          `MEM si (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
          `inst_wf si /\ inst_shape_ok si` by
            (conj_tac >- metis_tac[fn_inst_wf_def, fn_insts_def,
                                   unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
             qpat_assum `o1_fn_shape C3 fn`
               (mp_tac o REWRITE_RULE [o1_fn_shape_def,
                                       unitShapeDefsTheory.fn_shape_ok_def, EVERY_MEM]) >>
             strip_tac >>
             qpat_assum `!i. MEM i (fn_insts fn) ==> inst_shape_ok i` irule >>
             first_assum ACCEPT_TAC) >>
          `s.vs_labels = t.vs_labels` by
            (qpat_assum `fmp_stage_rel _ _ sm _ _ _ F _ _ _ _ _ _ _ t _` mp_tac >>
             simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def] >>
             strip_tac >> first_assum ACCEPT_TAC) >>
          `terminates (step_inst fuel C4 si t)` by simp[passSimulationDefsTheory.terminates_def] >>
          `terminates (step_inst fuel C3 si s)` by
            (Cases_on `si.inst_opcode = PARAM`
             >- (mp_tac (Q.INST [`vs` |-> `root3`] cut_source_call_arity) >>
                 (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
                 disch_then assume_tac >>
                 drule_all fmp_stage_back_param_point >> simp[NoAsms]) >>
             `~MEM si.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI; PARAM]` by simp[] >>
             `!v. MEM (Var v) si.inst_operands ==> IS_SOME (lookup_var v s)` by
               (rpt strip_tac >> qpat_assum `!v. _ /\ _ ==> IS_SOME (lookup_var v s)` irule >>
                conj_tac >> first_assum ACCEPT_TAC) >>
             drule_all fmp_stage_back_kept_nonparam_point >> simp[NoAsms]) >>
          drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_frame_sites_upto)) >>
          strip_tac >>
          `~MEM si.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI]` by simp[] >>
          `step_inst fuel C3 si s = step_inst fuel C3 si s` by simp[] >>
          drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_ordinary_segment)) >>
          disch_then (qx_choose_then `target_fn` (qx_choose_then `source_bb`
            (qx_choose_then `target_bb` (qx_choose_then `tail`
              (qx_choose_then `r` strip_assume_tac))))) >>
          `r = OK s'` by
            (qpat_assum `!k. step_inst k C4 si t = r` (qspec_then `fuel` mp_tac) >>
             simp[]) >>
          qpat_x_assum `r = OK s'` SUBST_ALL_TAC >>
          qpat_x_assum `(case step_inst fuel C3 si s of OK _ => _ | Halt _ => _ |
                         Abort _ _ => _ | IntRet _ _ => _ | Error _ => _)` mp_tac >>
          Cases_on `step_inst fuel C3 si s` >>
          simp[NoAsms, dead_result_rel_def] >>
          disch_then strip_assume_tac >>
          rename1 `step_inst fuel C3 si s = OK post` >>
          `post.vs_current_bb = s.vs_current_bb /\ ~post.vs_halted` by
            (drule_all venomInstPropsTheory.step_preserves_control_flow >> strip_tac >>
             `step_inst_base si s = OK post` by
               (qpat_assum `si.inst_opcode <> INVOKE` (fn opc =>
                qpat_assum `step_inst fuel C3 si s = OK post` mp_tac >>
                simp[NoAsms, step_inst_non_invoke, opc])) >>
             drule venomExecPropsTheory.step_inst_OK_preserves_halted >> simp[]) >>
          drule_all o1LowerDloadReadinessTheory.ld_nonterminator_successor >>
          disch_then (qx_choose_then `next` assume_tac) >>
          `post.vs_gas_readings = s'.vs_gas_readings` by
            (qpat_assum `fmp_stage_rel _ _ sm _ _ _ F _ _ _ _ _
                         (post with vs_inst_idx := _) lo (s' with vs_inst_idx := _) ts` mp_tac >>
             simp[NoAsms, fmp_stage_rel_def, o1LowerDloadSharedTheory.ld_shared_agree_def]) >>
          `root3.vs_gas_readings = root4.vs_gas_readings` by simp[NoAsms, Abbr `root3`] >>
          `gas_cut n root3 (post with vs_inst_idx := SUC s.vs_inst_idx)` by
            (qpat_assum `gas_cut n root4 (s' with vs_inst_idx := _)` mp_tac >>
             qpat_assum `post.vs_gas_readings = _` (fn readings =>
             qpat_assum `root3.vs_gas_readings = _` (fn roots =>
               simp[NoAsms, gas_cut_def, readings, roots]))) >>
          `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME bb` by metis_tac[] >>
          `!k. fmp_target_run k C4 fn.fn_name
                     (s' with vs_inst_idx := SUC t.vs_inst_idx) 0
                     (s' with vs_inst_idx := SUC t.vs_inst_idx)` by
            (`SUC t.vs_inst_idx < LENGTH bb.bb_instructions` by
               (qpat_assum `active_inst fn' ti' (s' with vs_inst_idx := _)` mp_tac >>
                qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn) _ _ _ _`
                  (fn idx => once_rewrite_tac [GSYM idx]) >>
                disch_tac >> drule_all active_inst_block_lookup >> strip_tac >>
                `bb' = bb` by
                  (qpat_assum `lookup_block (s' with vs_inst_idx := _).vs_current_bb fn'.fn_blocks = SOME bb'` mp_tac >>
                   qpat_assum `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME bb`
                     (fn fetch => simp[NoAsms, fetch])) >>
                qpat_assum `get_instruction bb' _ = SOME ti'` mp_tac >>
                qpat_assum `bb' = bb` (fn eq => simp[NoAsms, eq, get_instruction_def]) >>
                rw[]) >>
             irule fmp_restore_target_run_zero >>
             simp[NoAsms] >> qexistsl [`bb`, `fn'`] >>
             conj_tac
             >- (qpat_assum `SUC t.vs_inst_idx < LENGTH bb.bb_instructions` mp_tac >> decide_tac) >>
             conj_tac >> first_assum ACCEPT_TAC) >>
          disj1_tac >>
          qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn) _ _ _ _`
            (SUBST1_TAC o SYM) >>
          qexistsl [`stk`, `PG`, `step_prov PG G si post`, `step_taint si s post tn`, `fn`,
                    `next`, `post with vs_inst_idx := SUC s.vs_inst_idx`, `sm`, `lo`,
                    `s' with vs_inst_idx := SUC t.vs_inst_idx`, `ts`, `F`, `bb`] >>
          conj_tac >- (irule frame_reachable_next >> metis_tac[]) >>
          rpt conj_tac >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
      `!k. ?post. step_inst k C3 si s = OK post` by
        (`inst_wf si` by
           (qpat_assum `active_inst fn si s` (mp_tac o MATCH_MP active_inst_mem_fn_insts) >>
            REWRITE_TAC[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
            disch_then (qx_choose_then `b0` strip_assume_tac) >>
            qpat_assum `fn_inst_wf fn`
              (qspecl_then [`b0`, `si`] irule o REWRITE_RULE [fn_inst_wf_def]) >>
            qexists `b0` >> conj_tac >> first_assum ACCEPT_TAC) >>
         `MEM si.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM]` by simp[] >>
         drule_all ld_normal_parameter_shape >> strip_tac >>
         simp[ld_retpc_success_iff]) >>
      pop_assum (qspec_then `fuel` (qx_choose_then `post` assume_tac)) >>
      drule_all focus_fmp_retpc_point >>
      disch_then (qx_choosel_then [`len`, `t1`, `ret_fn`, `ret_bb`]
        (map_every assume_tac o CONJUNCTS)) >>
      `ret_fn = fn' /\ ret_bb = bb` by metis_tac[optionTheory.SOME_11] >>
      qpat_x_assum `ret_fn = fn'` SUBST_ALL_TAC >>
      qpat_x_assum `ret_bb = bb` SUBST_ALL_TAC >>
      `t1.vs_inst_idx = t.vs_inst_idx + len /\
       t.vs_inst_idx + len <= LENGTH bb.bb_instructions` by
        (qpat_assum `!k. fmp_target_run k C4 _ t len t1`
           (qspec_then `fuel` mp_tac) >> simp[NoAsms, fmp_target_run_def] >>
         disch_then (qx_choosel_then [`run_fn`, `run_bb`, `run_post`] strip_assume_tac) >>
         `run_fn = fn' /\ run_bb = bb` by metis_tac[optionTheory.SOME_11] >>
         qpat_x_assum `run_bb = bb` SUBST_ALL_TAC >>
         conj_tac
         >- (qpat_assum `t1 = run_post with vs_inst_idx := _` (fn th => simp[NoAsms, th, ADD_COMM])) >>
         qpat_assum `_ <= LENGTH bb.bb_instructions`
           (fn th => simp[NoAsms, ADD_COMM, th])) >>
      `EVERY (\i. fmp_inserted_op i.inst_opcode)
         (TAKE len (DROP t.vs_inst_idx bb.bb_instructions))` by
        (qpat_x_assum `len = 1 \/ len = 2` strip_assume_tac >>
         qpat_assum `if len = 1 then _ else _` mp_tac >>
         qpat_assum `len = _` (fn th => simp[NoAsms, th, Excl "TAKE1_DROP"]) >>
         strip_tac >> simp[fmp_inserted_op_def, mk_inst_def, set_param_index_def]) >>
      `!i. t.vs_inst_idx <= i /\ i < t1.vs_inst_idx ==>
           i < LENGTH bb.bb_instructions /\
           fmp_inserted_op (EL i bb.bb_instructions).inst_opcode` by
        (qx_gen_tac `i` >> strip_tac >>
         `i < LENGTH bb.bb_instructions /\ i - t.vs_inst_idx < len /\
          i - t.vs_inst_idx + t.vs_inst_idx = i` by decide_tac >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qpat_assum `EVERY _ (TAKE len _)`
           (qspec_then `i - t.vs_inst_idx` mp_tac o REWRITE_RULE [EVERY_EL]) >>
         `len <= LENGTH (DROP t.vs_inst_idx bb.bb_instructions)` by
           (simp[NoAsms, LENGTH_DROP] >> decide_tac) >>
         qpat_assum `len <= LENGTH (DROP _ _)` (fn lim =>
           qpat_assum `i - t.vs_inst_idx < len` (fn off =>
           qpat_assum `i - t.vs_inst_idx + t.vs_inst_idx = i` (fn idx =>
           qpat_assum `i < LENGTH bb.bb_instructions` (fn hi =>
             simp[NoAsms, lim, off, idx, hi, LENGTH_TAKE, EL_TAKE, EL_DROP]))))) >>
      `post.vs_current_bb = s.vs_current_bb /\
       post.vs_gas_readings = s.vs_gas_readings /\ ~post.vs_halted` by
        (`step_inst_base si s = OK post` by
           (qpat_assum `step_inst fuel C3 si s = OK post` mp_tac >>
            qpat_assum `si.inst_opcode <> INVOKE`
              (fn th => simp[NoAsms, step_inst_non_invoke, th])) >>
         `si.inst_opcode <> GAS` by simp[] >>
         drule venomExecPropsTheory.step_inst_OK_preserves_halted >>
         drule_all venomInstPropsTheory.step_preserves_control_flow >>
         drule_all oracleExecPropsTheory.step_inst_noninvoke_gas_readings >>
         simp[NoAsms] >> metis_tac[]) >>
      `t1.vs_current_bb = t.vs_current_bb /\ post.vs_gas_readings = t1.vs_gas_readings` by
        (qpat_assum `fmp_stage_rel _ _ sm _ _ _ F _ _ _ _ _
                     (post with vs_inst_idx := _) lo t1 ts` mp_tac >>
         simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def,
              o1LowerDloadSharedTheory.ld_shared_agree_def] >>
         strip_tac >> metis_tac[]) >>
      `t1.vs_inst_idx - t.vs_inst_idx = len /\ t.vs_inst_idx < t1.vs_inst_idx` by
        (qpat_assum `len = 1 \/ len = 2` strip_assume_tac >> decide_tac) >>
      `t.vs_current_bb = t1.vs_current_bb /\
       (!k. fmp_target_run k C4 fn.fn_name t (t1.vs_inst_idx - t.vs_inst_idx) t1)` by
        (conj_tac >- metis_tac[] >>
         qpat_assum `t1.vs_inst_idx - t.vs_inst_idx = len` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      drule_all (Q.INST [`u` |-> `t1`] focus_fmp_cut_inserted_residual) >>
      strip_tac >> first_x_assum drule >>
      disch_then (strip_assume_tac o SRULE [LET_THM]) >>
      drule_all o1LowerDloadReadinessTheory.ld_nonterminator_successor >>
      disch_then (qx_choose_then `next` assume_tac) >>
      `gas_cut n root3 (post with vs_inst_idx := SUC s.vs_inst_idx)` by
        (qpat_assum `gas_cut n root3 s` mp_tac >>
         qpat_assum `post.vs_gas_readings = s.vs_gas_readings`
           (fn th => simp[NoAsms, gas_cut_def, th])) >>
      `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME bb /\
       t1.vs_gas_readings = s'.vs_gas_readings` by metis_tac[] >>
      disj1_tac >>
      qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn) _ _ _ _`
        (SUBST1_TAC o SYM) >>
      qexistsl [`stk`, `PG`, `step_prov PG G si post`, `step_taint si s post tn`,
                `fn`, `next`, `post with vs_inst_idx := SUC s.vs_inst_idx`,
                `sm`, `lo`, `t1`, `ts`, `F`, `bb`] >>
      conj_tac >- (irule frame_reachable_next >> metis_tac[]) >>
      rpt conj_tac >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  reverse (Cases_on `inst.inst_opcode = DALLOCA`)
  >- (Cases_on `inst.inst_opcode = INVOKE`
      >- (`(EL s.vs_inst_idx bs.bb_instructions).inst_opcode = INVOKE` by metis_tac[] >>
          drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                            `idx` |-> `s.vs_inst_idx`] fmp_stage_invoke_inst) >>
          gvs[get_instruction_def]) >>
      `is_terminator inst.inst_opcode` by fs[] >>
      `pre_fmp_opcode inst.inst_opcode` by
        (drule active_inst_mem_fn_insts >> disch_tac >>
         qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
         metis_tac[]) >>
      `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by
        (simp[NoAsms] >> rpt strip_tac >> fs[is_terminator_def]) >>
      drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                        `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
      gvs[get_instruction_def] >> disch_then SUBST_ALL_TAC >> fs[]) >>
  qpat_x_assum `~(inst.inst_opcode = DALLOCA /\ _)` mp_tac >>
  simp[] >> disch_then (qspecl_then [`sm`, `lo`] mp_tac) >> simp[]
QED

Resume cut_frame_coverage[block]:
  `MEM ti.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[fnBlockBodyHelpersTheory.step_ok_terminator_jump, MEM] >>
  `ti.inst_opcode <> INVOKE` by (fs[MEM] >> simp[]) >>
  `gas_cut n root4 t` by
    (irule gas_cut_readings_mono >> first_assum (irule_at Any) >>
     drule enters_block_readings >> strip_tac >> simp[] >>
     irule step_inst_noninvoke_readings_le >> metis_tac[]) >>
  qpat_x_assum `gas_cut n root4 t ==> _` drule >>
  reverse (disch_then (DISJ_CASES_THEN strip_assume_tac))
  >- (drule_all (Q.INST [`eom` |-> `eom`, `C4` |-> `C4`] focus_fmp_cut_tail_observation) >>
      strip_tac >> gvs[MEM]) >>
  `ALL_DISTINCT (fn_labels fn')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  `get_instruction bb t.vs_inst_idx = SOME ti` by
    (qpat_assum `active_inst fn' ti t` (mp_then Any drule_all active_inst_block_lookup) >>
     strip_tac >> metis_tac[optionTheory.SOME_11]) >>
  `u = t` by
    (Cases_on `t.vs_inst_idx < u.vs_inst_idx`
     >- (qpat_assum `!i. _ <= i /\ _ ==> _` (qspec_then `t.vs_inst_idx` mp_tac) >>
         gvs[get_instruction_def, fmp_inserted_op_def, MEM]) >>
     `u.vs_inst_idx - t.vs_inst_idx = 0` by decide_tac >>
     metis_tac[fmp_target_run_zero]) >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  `(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_vars = FEMPTY /\
   ~(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_halted` by
    fs[o1_initial_state_ok_def] >>
  drule_all cut_source_points >> strip_tac >>
  `ssa_form fn` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  qabbrev_tac `root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `w2n root3.vs_fmp = w2n fmp` by simp[Abbr `root3`] >>
  `?m l. fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n fmp) eom T
           stk PG G tn fn s l t ts` by
    (`ti.inst_opcode <> ASSIGN` by (fs[MEM] >> simp[]) >>
     qpat_x_assum `MEM ti.inst_opcode _` kall_tac >>
     Cases_on `restored` >- metis_tac[] >> gvs[] >>
     drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_restore_prefix)) >>
     disch_then (qx_choosel_then
       [`rest_fn`, `rest_src`, `rest_bb`, `rest_infos`, `rest_ctx`,
        `rest_runner`, `rest_len`, `rest_post`, `rest_cut`] strip_assume_tac) >>
     Cases_on `FLOOKUP (fmp_stage_plan rest_infos rest_ctx fn) (s.vs_current_bb,s.vs_inst_idx)`
     >- (gvs[] >> metis_tac[]) >>
     gvs[get_instruction_def, mk_inst_def]) >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ restored _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_all cut_aligned_layout >> strip_tac >>
  `pre_fmp_opcode inst.inst_opcode` by
    (qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
     metis_tac[active_inst_mem_fn_insts]) >>
  `inst = ti` by
    (Cases_on `MEM inst.inst_opcode [DALLOCA; RETPC_PARAM]`
     >- (qabbrev_tac `plan = fmp_stage_plan infos ctx fn` >>
         qabbrev_tac `rt = fmp_stage_root infos ctx fn` >>
         qabbrev_tac `idx = s.vs_inst_idx` >>
         qabbrev_tac `lab = s.vs_current_bb` >>
         `fmp_stage_tidx plan rt lab bs.bb_instructions idx +
            (if (lab,idx) IN FDOM plan then 1 else 0) <
          fmp_stage_tidx plan rt lab bs.bb_instructions (SUC idx)` by
           (simp[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
            Cases_on `rt` >> simp[]
            >- (IF_CASES_TAC >> simp[]) >>
            rename1 `SOME r = fmp_stage_root _ _ _` >> PairCases_on `r` >> simp[] >>
            rpt (IF_CASES_TAC >> simp[]) >> decide_tac) >>
         mp_tac (Q.INST [`P` |-> `fmp_inserted_op`, `infos` |-> `infos`,
                         `ctx` |-> `ctx`, `runner` |-> `runner`, `fn` |-> `fn`,
                         `fn'` |-> `fn'`, `lbl` |-> `lab`, `bb` |-> `bs`,
                         `idx` |-> `idx`, `i` |-> `t.vs_inst_idx`]
             fmpStageCoverMemAssembleTheory.fmp_cover_inserted_from_root_structural) >>
         (impl_tac >- (simp[fmp_inserted_op_def, Abbr `rt`, Abbr `plan`] >>
                       rw[] >> gvs[MEM])) >>
         strip_tac >> gvs[get_instruction_def, fmp_inserted_op_def, MEM]) >>
     Cases_on `inst.inst_opcode = INVOKE`
     >- (`(EL s.vs_inst_idx bs.bb_instructions).inst_opcode = INVOKE` by metis_tac[] >>
         drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                           `idx` |-> `s.vs_inst_idx`] fmp_stage_invoke_inst) >>
         strip_tac >> gvs[get_instruction_def]) >>
     `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by fs[MEM] >>
     drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                       `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
     strip_tac >> gvs[get_instruction_def]) >>
  qpat_x_assum `inst = ti` SUBST_ALL_TAC >>
  `inst_wf ti /\ inst_shape_ok ti /\ opaque_use_ok fn /\ first_block_no_preds fn /\
   (C3.ctx_entry = SOME fn.fn_name ==> entry_fn_no_params fn)` by
    (`MEM ti (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
     conj_tac >- metis_tac[fn_inst_wf_def, fn_insts_def,
                            unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def, EVERY_MEM]) >>
  `s.vs_labels = t.vs_labels` by
    (qpat_assum `fmp_stage_rel _ _ m _ _ _ T _ _ _ _ _ _ _ t _` mp_tac >>
     simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `~MEM ti.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI; PARAM] /\
   ti.inst_opcode <> PHI` by (fs[MEM] >> simp[]) >>
  `!v. MEM (Var v) ti.inst_operands ==> IS_SOME (lookup_var v s)` by simp[] >>
  `terminates (step_inst fuel C4 ti t)` by simp[passSimulationDefsTheory.terminates_def] >>
  `terminates (step_inst fuel C3 ti s)` by
    (drule_all fmp_stage_back_kept_nonparam_point >> simp[NoAsms]) >>
  `step_inst fuel C3 ti s = step_inst fuel C3 ti s` by simp[] >>
  drule_all focus_fmp_jump_point >>
  disch_then (CONJUNCTS_THEN2 (K ALL_TAC) (qx_choose_then `dst` strip_assume_tac)) >>
  `s' = jump_to dst t` by metis_tac[exec_result_11] >>
  qpat_x_assum `s' = jump_to dst t` SUBST_ALL_TAC >>
  `fn_labels fn' = fn_labels fn` by metis_tac[fmp_stage_lowered_shape] >>
  `MEM dst (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (`?b. lookup_block dst fn'.fn_blocks = SOME b` by fs[enters_block_def, jump_to_def] >>
     drule stackPlanGenTheory.lookup_block_mem_fn_labels >>
     fs[fn_labels_def]) >>
  drule_all focus_fmp_cut_source_jump_entry >>
  disch_then (qx_choosel_then [`s1`, `si1`] strip_assume_tac) >>
  drule_all focus_fmp_cut_jump_entry >>
  disch_then (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (qx_choose_then `t1` strip_assume_tac))) >>
  `t1 = t'` by (fs[enters_block_def] >> gvs[]) >>
  qpat_x_assum `t1 = t'` SUBST_ALL_TAC >>
  `frame_reachable root3 C3 stk PG (entry_prov fn (jump_to dst s) G)
      (entry_taint_vars fn (jump_to dst s) tn) fn si1 s1` by
    (irule (cj 3 frame_reachable_rules) >>
     goal_assum (drule_at Any) >>
     `~(jump_to dst s).vs_halted` by simp[jump_to_def] >>
     simp[] >> qexistsl [`fuel`, `ti`, `s`] >> simp[]) >>
  `s1.vs_gas_readings = s.vs_gas_readings /\ ~s1.vs_halted` by
    (qpat_assum `enters_block fn _ s1` (mp_then Any assume_tac enters_block_readings) >>
     qpat_assum `enters_block fn _ s1`
       (mp_then Any assume_tac o1LowerDloadRunnerBoundaryTheory.ld_enters_block_halted) >>
     fs[jump_to_def]) >>
  qpat_assum `active_inst fn' ti' t'` (mp_then Any drule_all active_inst_block_lookup) >>
  disch_then (qx_choose_then `bb1` strip_assume_tac) >>
  `s1.vs_gas_readings = t'.vs_gas_readings` by
    (qpat_assum `enters_block fn' _ t'` (mp_then Any assume_tac enters_block_readings) >>
     fs[jump_to_def]) >>
  disj1_tac >>
  qexistsl [`stk`, `PG`, `entry_prov fn (jump_to dst s) G`,
    `entry_taint_vars fn (jump_to dst s) tn`, `fn`, `si1`, `s1`, `m`, `l`, `t'`, `ts`, `F`, `bb1`] >>
  simp[] >> conj_tac
  >- (irule gas_cut_readings_mono >>
      qpat_assum `gas_cut n root3 s` (irule_at Any) >>
      gvs[]) >>
  fs[fmp_target_run_def, run_insts_def, get_instruction_def]
  >> (gvs[])
QED

Resume cut_frame_coverage[call]:
  `gas_cut n root4 t` by
    (irule gas_cut_readings_mono >>
     qpat_assum `gas_cut n root4 t'` (irule_at Any) >>
     drule enters_block_readings >>
     drule o1LowerDloadSharedTheory.ld_setup_callee_gas_readings >> simp[]) >>
  qpat_x_assum `gas_cut n root4 t ==> _` drule >>
  reverse (disch_then (DISJ_CASES_THEN strip_assume_tac))
  >- (drule_all (Q.INST [`eom` |-> `eom`, `C4` |-> `C4`] focus_fmp_cut_tail_observation) >>
      strip_tac >> gvs[MEM]) >>
  `ALL_DISTINCT (fn_labels fn')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  `get_instruction bb t.vs_inst_idx = SOME ti` by
    (qpat_assum `active_inst fn' ti t` (mp_then Any drule_all active_inst_block_lookup) >>
     strip_tac >> metis_tac[optionTheory.SOME_11]) >>
  `u = t` by
    (Cases_on `t.vs_inst_idx < u.vs_inst_idx`
     >- (qpat_assum `!i. _ <= i /\ _ ==> _` (qspec_then `t.vs_inst_idx` mp_tac) >>
         gvs[get_instruction_def, fmp_inserted_op_def]) >>
     `u.vs_inst_idx - t.vs_inst_idx = 0` by decide_tac >>
     metis_tac[fmp_target_run_zero]) >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  `(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_vars = FEMPTY /\
   ~(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_halted` by
    fs[o1_initial_state_ok_def] >>
  drule_all cut_source_points >> strip_tac >>
  `ssa_form fn` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  qabbrev_tac `root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `w2n root3.vs_fmp = w2n fmp` by simp[Abbr `root3`] >>
  `?m l. fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n fmp) eom T
           stk PG G tn fn s l t ts` by
    (Cases_on `restored` >- metis_tac[] >> gvs[] >>
     drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_restore_prefix)) >>
     disch_then (qx_choosel_then
       [`rest_fn`, `rest_src`, `rest_bb`, `rest_infos`, `rest_ctx`,
        `rest_runner`, `rest_len`, `rest_post`, `rest_cut`] strip_assume_tac) >>
     Cases_on `FLOOKUP (fmp_stage_plan rest_infos rest_ctx fn) (s.vs_current_bb,s.vs_inst_idx)`
     >- (gvs[] >> metis_tac[]) >>
     gvs[get_instruction_def, mk_inst_def]) >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ restored _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_all cut_aligned_layout >> strip_tac >>
  `pre_fmp_opcode inst.inst_opcode` by
    (qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
     metis_tac[active_inst_mem_fn_insts]) >>
  `inst.inst_opcode = INVOKE` by
    (CCONTR_TAC >>
     Cases_on `MEM inst.inst_opcode [DALLOCA; RETPC_PARAM]`
     >- (qabbrev_tac `plan = fmp_stage_plan infos ctx fn` >>
         qabbrev_tac `rt = fmp_stage_root infos ctx fn` >>
         qabbrev_tac `idx = s.vs_inst_idx` >>
         qabbrev_tac `lab = s.vs_current_bb` >>
         `fmp_stage_tidx plan rt lab bs.bb_instructions idx +
            (if (lab,idx) IN FDOM plan then 1 else 0) <
          fmp_stage_tidx plan rt lab bs.bb_instructions (SUC idx)` by
           (simp[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
            Cases_on `rt` >> simp[]
            >- (IF_CASES_TAC >> simp[]) >>
            rename1 `SOME r = fmp_stage_root _ _ _` >> PairCases_on `r` >> simp[] >>
            rpt (IF_CASES_TAC >> simp[]) >> decide_tac) >>
         mp_tac (Q.INST [`P` |-> `fmp_inserted_op`, `infos` |-> `infos`,
                         `ctx` |-> `ctx`, `runner` |-> `runner`, `fn` |-> `fn`,
                         `fn'` |-> `fn'`, `lbl` |-> `lab`, `bb` |-> `bs`,
                         `idx` |-> `idx`, `i` |-> `t.vs_inst_idx`]
             fmpStageCoverMemAssembleTheory.fmp_cover_inserted_from_root_structural) >>
         (impl_tac >- (simp[fmp_inserted_op_def, Abbr `rt`, Abbr `plan`] >>
                       rw[] >> gvs[MEM])) >>
         strip_tac >> gvs[get_instruction_def, fmp_inserted_op_def]) >>
     `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by fs[MEM] >>
     drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                       `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
     strip_tac >> gvs[get_instruction_def]) >>
  drule_all focus_fmp_cut_source_call_entry >>
  disch_then (qx_choosel_then [`snm`, `sops`, `callee`, `sargs`, `scs`, `si1`]
    strip_assume_tac) >>
  `C3.ctx_entry <> SOME snm` by (drule_all fmp_invoke_not_entry >> simp[]) >>
  `callee.fn_fmp_signature = NONE` by
    (fs[fmp_free_ctx_def, EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
  drule_all focus_fmp_cut_invoke_push >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`tf`, `sb`, `tb`, `tj`, `ti0`, `tc0`, `tr0`, `tf1`,
      `si0`, `sc0`, `sr0`, `extra`, `rr`, `args1`, `cs1`, `t1`] strip_assume_tac)) >>
  `tf = fn'` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tf = fn'` SUBST_ALL_TAC >>
  `tj = ti` by metis_tac[fmpStageBlockSimCodeTheory.active_inst_unique] >>
  qpat_x_assum `tj = ti` SUBST_ALL_TAC >>
  `snm = nm /\ sops ++ extra = ops /\ tf1 = fn'' /\ cs1 = cs /\ t1 = t'` by
    (gvs[enters_block_def] >> metis_tac[]) >>
  qpat_x_assum `t1 = t'` SUBST_ALL_TAC >>
  `callee.fn_name = snm` by metis_tac[lookup_function_selected_name] >>
  `fn_inst_ids_distinct fn` by
    (pure_rewrite_tac [algebraicOptSupplyProofsTheory.ao_fn_inst_ids_distinct_alt] >>
     irule ctx_inst_ids_distinct_fn >>
     qexists `C3` >> fs[o1_ctx_shape_def] >> metis_tac[lookup_function_MEM]) >>
  `MEM inst (fn_insts fn) /\ MEM ti (fn_insts fn')` by
    metis_tac[active_inst_mem_fn_insts] >>
  `ti.inst_outputs = inst.inst_outputs` by
    (qpat_assum `ti.inst_id = inst.inst_id` (mp_then Any drule_all focus_fmp_cut_invoke_outputs) >>
     simp[]) >>
  qabbrev_tac `f = <|cf_fn := fn; cf_inst := inst; cf_state := s;
                     cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>` >>
  `frame_reachable root3 C3 (f::stk) (MAP (op_prov G) sops) FEMPTY
        (tn with t_var := FEMPTY) callee si1 scs` by
    (simp[Abbr `f`] >> irule frame_reachable_call >> metis_tac[]) >>
  `~scs.vs_halted /\ scs.vs_gas_readings = s.vs_gas_readings /\
   t'.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[ld_setup_callee_not_halted, o1LowerDloadSharedTheory.ld_setup_callee_gas_readings,
              enters_block_readings] >>
  `gas_cut n root3 scs` by
    (irule gas_cut_readings_mono >> qpat_assum `gas_cut n root3 s` (irule_at Any) >> gvs[]) >>
  `ALL_DISTINCT (fn_labels fn'')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  qpat_assum `active_inst fn'' ti' t'` (mp_then Any drule_all active_inst_block_lookup) >>
  disch_then (qx_choose_then `bb1` strip_assume_tac) >>
  disj1_tac >>
  qexistsl [`f::stk`, `MAP (op_prov G) sops`, `FEMPTY`, `tn with t_var := FEMPTY`,
    `callee`, `si1`, `scs`, `m`, `l`, `t'`, `(t,l)::ts`, `F`, `bb1`] >>
  simp[Abbr `f`, fmp_cov_stack_def] >>
  gvs[fmp_target_run_def, run_insts_def, get_instruction_def]
QED

Resume cut_frame_coverage[ret]:
  `MEM ti.inst_opcode [RET; RETFMP; DRET]` by metis_tac[step_inst_intret_opcodes] >>
  `gas_cut n root4 t` by
    (irule gas_cut_readings_mono >>
     qpat_assum `gas_cut n root4 (_ with vs_inst_idx := _)` (irule_at Any) >>
     simp[] >> metis_tac[return_readings_le]) >>
  qpat_x_assum `gas_cut n root4 t ==> _` drule >>
  reverse (disch_then (DISJ_CASES_THEN strip_assume_tac))
  >- (drule_all (Q.INST [`eom` |-> `eom`, `C4` |-> `C4`] focus_fmp_cut_tail_observation) >>
      strip_tac >> gvs[MEM]) >>
  `ALL_DISTINCT (fn_labels fn')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  `get_instruction bb t.vs_inst_idx = SOME ti` by
    (qpat_assum `active_inst fn' ti t` (mp_then Any drule_all active_inst_block_lookup) >>
     strip_tac >> metis_tac[optionTheory.SOME_11]) >>
  `u = t` by
    (Cases_on `t.vs_inst_idx < u.vs_inst_idx`
     >- (qpat_assum `!i. _ <= i /\ _ ==> _` (qspec_then `t.vs_inst_idx` mp_tac) >>
         gvs[get_instruction_def, fmp_inserted_op_def, MEM]) >>
     `u.vs_inst_idx - t.vs_inst_idx = 0` by decide_tac >>
     metis_tac[fmp_target_run_zero]) >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  `(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_vars = FEMPTY /\
   ~(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_halted` by
    fs[o1_initial_state_ok_def] >>
  drule_all cut_source_points >> strip_tac >>
  `ssa_form fn` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  qabbrev_tac `root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `w2n root3.vs_fmp = w2n fmp` by simp[Abbr `root3`] >>
  `?m l. fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n fmp) eom T
           stk PG G tn fn s l t ts` by
    ((Cases_on `restored` >- metis_tac[] >> gvs[] >>
     drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_restore_prefix)) >>
     disch_then (qx_choosel_then
       [`rest_fn`, `rest_src`, `rest_bb`, `rest_infos`, `rest_ctx`,
        `rest_runner`, `rest_len`, `rest_post`, `rest_cut`] strip_assume_tac) >>
     Cases_on `FLOOKUP (fmp_stage_plan rest_infos rest_ctx fn) (s.vs_current_bb,s.vs_inst_idx)`
     >- (qexistsl [`DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < rest_cut}`,
                   `rest_cut`] >> gvs[]) >>
     gvs[get_instruction_def, mk_inst_def, MEM] >> (metis_tac[get_instruction_def, mk_inst_def, MEM, SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_restore_prefix)]))) >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ restored _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_all cut_aligned_layout >> strip_tac >>
  `pre_fmp_opcode inst.inst_opcode` by
    (qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
     metis_tac[active_inst_mem_fn_insts]) >>
  `inst = ti` by
    (Cases_on `MEM inst.inst_opcode [DALLOCA; RETPC_PARAM]`
     >- (mp_tac (Q.INST [`P` |-> `fmp_inserted_op`, `infos` |-> `infos`,
                         `ctx` |-> `ctx`, `runner` |-> `runner`, `fn` |-> `fn`,
                         `fn'` |-> `fn'`, `lbl` |-> `s.vs_current_bb`, `bb` |-> `bs`,
                         `idx` |-> `s.vs_inst_idx`, `i` |-> `t.vs_inst_idx`]
             fmpStageCoverMemAssembleTheory.fmp_cover_inserted_from_root_structural) >>
         (impl_tac >- (simp[fmp_inserted_op_def, fmp_cov_tidx_lt] >>
                       rw[] >> gvs[MEM] >>
                       metis_tac[SRULE [] fmp_cov_tidx_lt])) >>
         strip_tac >> gvs[get_instruction_def, fmp_inserted_op_def, MEM]) >>
     Cases_on `inst.inst_opcode = INVOKE`
     >- (qpat_x_assum `inst = EL _ _` SUBST_ALL_TAC >>
         drule_all fmp_stage_invoke_inst >> strip_tac >>
         gvs[get_instruction_def, MEM]) >>
     `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by fs[MEM] >>
     drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                       `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
     strip_tac >> gvs[get_instruction_def]) >>
  `inst.inst_opcode = RET` by fs[pre_fmp_opcode_def, MEM] >>
  qpat_x_assum `inst = ti` SUBST_ALL_TAC >>
  qpat_x_assum `stk = f'::xs` SUBST_ALL_TAC >>
  Cases_on `ts` >- fs[fmp_cov_stack_def] >>
  rename1 `fmp_cov_stack C4 (f'::xs) (p::ps) (f::stk')` >>
  PairCases_on `p` >>
  qpat_x_assum `fmp_cov_stack C4 (f'::xs) _ _`
    (strip_assume_tac o REWRITE_RULE [fmp_cov_stack_def]) >>
  qpat_x_assum `ti = EL _ _` kall_tac >>
  `s.vs_labels = t.vs_labels` by
    (qpat_assum `fmp_stage_rel _ _ m _ _ _ T _ _ _ _ _ _ _ t _` mp_tac >>
     simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!v. MEM (Var v) ti.inst_operands ==> IS_SOME (lookup_var v s)` by fs[] >>
  `opaque_use_ok fn` by fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
  drule_all focus_fmp_cut_source_return >>
  disch_then (qspec_then `fuel`
    (qx_choosel_then [`sr`, `se`, `sb`, `si`] strip_assume_tac)) >>
  `fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n root3.vs_fmp) eom T
     (f'::xs) PG G tn fn s l t ((p0,p1)::ps)` by simp[] >>
  drule_at (Pat `step_inst _ _ _ _ = IntRet _ _`) focus_fmp_cut_invoke_pop >>
  disch_then (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ T _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `taint_ok _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_use_static_ok _ _ _`)) >>
  disch_then (drule_at (Pat `bind_outputs _ _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `active_inst _ _ (_ with vs_inst_idx := _)`)) >>
  disch_then (qspecl_then [`rp`, `n`, `fn'`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> simp[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`jr`, `j`, `t1`] strip_assume_tac))) >>
  qpat_x_assum `!k. step_inst k C4 ti t = _` (qspec_then `fuel` assume_tac) >>
  `ALL_DISTINCT (fn_labels f.cf_fn)` by
    (gs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  `j = f.cf_inst` by metis_tac[active_inst_block_lookup, optionTheory.SOME_11] >>
  gvs[] >>
  qabbrev_tac `b3 = sb with vs_inst_idx := SUC f'.cf_state.vs_inst_idx` >>
  qabbrev_tac `b4 = s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx` >>
  `frame_reachable root3 C3 xs f'.cf_params
       (DRESTRICT f'.cf_prov (COMPL (set f'.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f'.cf_tvar (COMPL (set f'.cf_inst.inst_outputs)))
       f'.cf_fn si b3` by
    (simp[Abbr `b3`] >> irule frame_reachable_ret >> metis_tac[]) >>
  `!nm g. lookup_function nm C3.ctx_functions = SOME g ==> wf_function g` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  `~b3.vs_halted` by
    (qpat_assum `frame_reachable root3 C3 xs _ _ _ _ _ b3`
        (mp_then Any drule_all scfg_frame_reachable_entry_root) >> strip_tac >>
     drule o1PassLiftTheory.supply_frame_reach_not_halted >> fs[o1PassLiftTheory.fn_entry_state_def]) >>
  `b3.vs_gas_readings = b4.vs_gas_readings` by
    (qpat_assum `fmp_stage_rel _ _ _ _ _ _ F xs _ _ _ _ b3 _ b4 _` mp_tac >>
     simp[NoAsms, fmp_stage_rel_def, o1LowerDloadSharedTheory.ld_shared_agree_def]) >>
  `gas_cut n root3 b3` by
    (`root3.vs_gas_readings = root4.vs_gas_readings` by simp[Abbr `root3`] >>
     fs[gas_cut_def, Abbr `b4`]) >>
  qpat_assum `active_inst f.cf_fn ti' b4` (mp_then Any drule_all active_inst_block_lookup) >>
  disch_then (qx_choose_then `bb1` strip_assume_tac) >>
  disj1_tac >>
  qexistsl [`xs`, `f'.cf_params`, `DRESTRICT f'.cf_prov (COMPL (set f'.cf_inst.inst_outputs))`,
    `tn with t_var := DRESTRICT f'.cf_tvar (COMPL (set f'.cf_inst.inst_outputs))`,
    `f'.cf_fn`, `si`, `b3`, `DRESTRICT m {key | FST key < w2n f'.cf_state.vs_fmp}`,
    `p1`, `b4`, `ps`, `F`, `bb1`] >>
  gvs[Abbr `b4`, fmp_target_run_def, run_insts_def, get_instruction_def]
QED

Finalise cut_frame_coverage

Theorem focus_fmp_cut_target_memory_fields:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  o1_pre 3 C3 C4 /\ o1_ctx_shape C3 /\ o1_ctx_shape C4 /\
  EVERY (o1_fn_row 3) C3.ctx_functions /\ EVERY ssa_form C3.ctx_functions /\
  C3.ctx_entry = SOME name /\ lookup_function name C3.ctx_functions = SOME src /\
  fn_entry_label src = SOME src_lbl /\
  o1_initial_state_ok root4 /\ root4.vs_fmp = root4.vs_initial_fmp /\
  code_layout_valid root4 /\ w2n root4.vs_initial_fmp <= w2n fmp /\
  root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  dead_wf D /\ fmp_free_ctx C3 /\ taint_within_upto D n C3 root3 /\
  (!g i v. raw_reachable root3 C3 g i v /\ gas_cut n root3 v ==> dalloca_no_wrap i v) /\
  ^cut_fields /\
  eom <= w2n root4.vs_initial_fmp /\ fmp_variant_room (SOME fmp) C4 root4 /\
  callee_first names C3.ctx_functions ==>
  mem_inv (\ctx fn inst t. gas_cut n root4 t ==> lowered_mem_fact eom ctx fn inst t)
    C4 root4
Proof
  strip_tac >>
  rewrite_tac[mem_inv_raw_reachable] >> conj_tac
  >- (`src.fn_fmp_signature = NONE /\ pre_fmp_ops src` by
        (fs[fmp_free_ctx_def, EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
      drule_all focus_fmp_selected_root_pin >> strip_tac >>
      `C4.ctx_entry = SOME name` by fs[ctx_pass_stage_def] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> rename1 `raw_reachable root4 C4 fn' ti t` >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  `active_inst fn' ti t` by metis_tac[scfg_frame_reachable_active] >>
  drule_all cut_frame_coverage >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (`ALL_DISTINCT (fn_labels fn')` by
        (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
         metis_tac[lookup_function_MEM]) >>
      Cases_on `t.vs_inst_idx < u.vs_inst_idx`
      >- (`fmp_inserted_op ti.inst_opcode` by
            (drule_all focus_fmp_cut_inserted_residual >> simp[]) >>
          gvs[fmp_inserted_op_def, lowered_mem_fact_def, lowered_mem_ok_def,
              inst_mem_ranges_def, source_memory_read_ranges_def,
              codegenRelTheory.source_memory_write_ranges_def]) >>
      `t = u` by
        (`u.vs_inst_idx - t.vs_inst_idx = 0` by decide_tac >>
         metis_tac[fmp_target_run_zero]) >>
      qpat_x_assum `t = u` SUBST_ALL_TAC >>
      `root3.vs_vars = FEMPTY /\ ~root3.vs_halted` by fs[o1_initial_state_ok_def] >>
      drule_all cut_source_points >> strip_tac >>
      drule_all focus_fmp_cut_point_memory >> simp[]) >>
  drule_all focus_fmp_cut_tail_observation >> simp[]
QED
