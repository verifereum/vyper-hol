Theory fmpStageFmpStepsDallocaExec
Ancestors
  fmpStageRel fmpStageOpBase fmpStageReclaimSound fmpStageControl
  fmpStageFmpStepsDallocaCode
  fmpLowerSequenceExec ptrStaticDiscipline unitMemInv frameViewFacts
  venomExecSemantics venomState words list finite_map passSimulationDefs

Theorem fmp_dalloca_source:
  inst.inst_opcode = DALLOCA /\ dalloca_no_wrap inst s /\
  step_inst k C inst s = r /\ terminates r ==>
  ?size_op sz out s1.
    inst.inst_operands = [size_op] /\ inst.inst_outputs = [out] /\
    eval_operand size_op s = SOME sz /\ r = OK s1 /\
    s1 = update_var out s.vs_fmp
      (s with vs_fmp := n2w (w2n s.vs_fmp + ceil32 (w2n sz))) /\
    w2n s.vs_fmp + ceil32 (w2n sz) < dimword (:256)
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(), terminates_def] >>
  gvs[dalloca_no_wrap_def] >>
  simp[GSYM word_add_n2w, WORD_ADD_COMM]
QED

Theorem fmp_dalloca_operand_untainted:
  taint_ok fn tn inst s /\ inst.inst_opcode = DALLOCA /\
  MEM op inst.inst_operands ==> op_taint tn op = {}
Proof
  strip_tac >> gvs[ptrDisciplineTheory.taint_ok_def] >>
  first_x_assum (qspec_then `op` mp_tac) >> simp[]
QED

Theorem fmp_dalloca_operand_noprov:
  ptr_use_static_ok P pv inst /\ FDOM G SUBSET pv /\
  inst.inst_opcode = DALLOCA /\ MEM op inst.inst_operands ==>
  op_prov G op = NONE
Proof
  strip_tac >> Cases_on `op` >> simp[ptrDisciplineTheory.op_prov_def] >>
  gvs[ptr_use_static_ok_def, pointerConfinedDefsTheory.is_pointer_preserving_op_def,
      memLocDefsTheory.mem_write_ops_def, memLocDefsTheory.mem_read_ops_def] >>
  metis_tac[finite_mapTheory.FLOOKUP_DEF, pred_setTheory.SUBSET_DEF]
QED

Theorem fmp_dalloca_size_agree:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode = DALLOCA /\ MEM op inst.inst_operands /\
  eval_operand op s = SOME sz ==> eval_operand op t = SOME sz
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `op_taint tn op = {}` by metis_tac[fmp_dalloca_operand_untainted] >>
  `FDOM G SUBSET fn_pv P fn` by metis_tac[fmp_stage_prov_support] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    (gvs[EVERY_MEM, fn_static_ptr_ok_def] >> metis_tac[]) >>
  `op_prov G op = NONE` by metis_tac[fmp_dalloca_operand_noprov] >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (gen_tac >> disch_tac >>
     irule ordinary_operand_not_retpc >>
     conj_tac >- gvs[o1PassContractTheory.o1_fn_shape_def,
                     unitShapeDefsTheory.fn_shape_ok_def] >>
     qexists_tac `inst` >> gvs[]) >>
  `inst.inst_opcode <> PHI` by simp[] >>
  drule_all fmp_stage_operand >> simp[] >> strip_tac >>
  gvs[fmp_value_rel_def,
      o1LowerDloadRelocationKernelTheory.ld_value_agree_def] >>
  metis_tac[frameRelocationGuardedValuesTheory.word_agree_except_empty]
QED

Theorem fmp_dalloca_scan_needs[local]:
  !insts. MEM inst insts /\ inst.inst_opcode = DALLOCA ==>
  (fmp_scan_insts insts).fi_needs_fmp
Proof
  Induct >> simp[fmpAnalysisDefsTheory.fmp_scan_insts_def,
    fmpAnalysisDefsTheory.fmp_info_join_def,
    fmpAnalysisDefsTheory.fmp_opcode_needs_fmp_def] >> metis_tac[]
QED

Theorem fmp_dalloca_lowered_needs:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = DALLOCA ==>
  ?info. FLOOKUP infos fn.fn_name = SOME info /\ info.fi_needs_fmp
Proof
  strip_tac >>
  `fmp_info_valid ctx infos /\ fmp_lower_input infos ctx fn` by
    gvs[fmp_stage_lowered_def, fmpLowerDefsTheory.fmp_lower_function_with_info_def,
        AllCaseEqs()] >>
  `MEM fn ctx.ctx_functions` by
    (gvs[fmpLowerDefsTheory.fmp_lower_input_def] >>
     metis_tac[venomInstTheory.lookup_function_MEM]) >>
  `?targets info. fmp_function_targets ctx fn = SOME targets /\
    FLOOKUP infos fn.fn_name = SOME info /\
    fmp_join_target_info infos targets (fmp_direct_info fn) = SOME info` by
      metis_tac[fmpAnalysisDefsTheory.fmp_info_valid_def] >>
  drule fmpAnalysisPropsTheory.fmp_join_target_info_needs_iff >>
  simp[fmpAnalysisDefsTheory.fmp_direct_info_def] >>
  metis_tac[fmp_dalloca_scan_needs]
QED

Theorem fmp_dalloca_root_exists:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\ FLOOKUP infos fn.fn_name = SOME info /\
  info.fi_needs_fmp ==>
  ?rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp)
Proof
  strip_tac >>
  `IS_SOME (split_fmp_entry fn)` by
    gvs[fmp_stage_lowered_def, fmpLowerDefsTheory.fmp_lower_function_with_info_def,
        fmpLowerDefsTheory.fmp_lower_input_def, AllCaseEqs(), optionTheory.IS_SOME_EXISTS] >>
  Cases_on `split_fmp_entry fn` >> gvs[] >> Cases_on `x` >>
  drule fmpStepLayoutTheory.split_fmp_entry_reconstruct >> strip_tac >>
  simp[fmp_stage_root_def] >> Cases_on `fn_is_context_entry ctx fn` >> simp[]
QED

Theorem fmp_dalloca_past_root:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  lookup_block rl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = DALLOCA ==>
  rp <= idx
Proof
  strip_tac >>
  gvs[fmp_stage_root_def, AllCaseEqs()] >>
  drule fmpStepLayoutTheory.split_fmp_entry_reconstruct >> strip_tac >>
  drule fmpStepLayoutTheory.split_fmp_entry_parameter_prefix >> strip_tac >>
  gvs[venomInstTheory.lookup_block_def, listTheory.FIND_thm] >>
  `~fn_is_context_entry ctx fn ==> retpc <> NONE` by
    (gvs[fmp_stage_lowered_def,
         fmpLowerDefsTheory.fmp_lower_function_with_info_def,
         fmpLowerDefsTheory.fmp_make_root_layout_def, AllCaseEqs()] >>
     Cases_on `retpc` >> gvs[]) >>
  `LENGTH (users ++ option_CASE retpc [] (\i. [i])) <= idx` suffices_by
    (Cases_on `retpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  CCONTR_TAC >>
  `idx < LENGTH (users ++ option_CASE retpc [] (\i. [i]))` by decide_tac >>
  gvs[EL_APPEND_EQN, EVERY_EL] >>
  (Cases_on `idx < LENGTH users`
  >- (gvs[] >>
      qpat_x_assum `!n. n < LENGTH users ==> _`
        (qspec_then `idx` mp_tac) >> simp[]) >>
  gvs[] >>
  `idx - LENGTH users < LENGTH (option_CASE retpc [] (\i. [i]))` by decide_tac >>
  qpat_x_assum `!n. n < LENGTH (option_CASE retpc [] (\i. [i])) ==> _`
    (qspec_then `idx - LENGTH users` mp_tac) >> simp[])
QED

Theorem fmp_dalloca_not_before_root:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = DALLOCA ==>
  ~(s.vs_current_bb = rl /\ s.vs_inst_idx < rp)
Proof
  strip_tac >> Cases_on `s.vs_current_bb = rl` >> gvs[] >>
  drule_all fmp_dalloca_past_root >> simp[]
QED

Theorem fmp_dalloca_frame_witness:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = DALLOCA /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts ==>
  ?fn' infos ctx runner bb info rl rp env states st regions.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    fmp_stage_lowered infos ctx runner fn fn' /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = inst /\
    fn.fn_fmp_signature = NONE /\
    FLOOKUP infos fn.fn_name = SOME info /\ info.fi_needs_fmp /\
    fmp_stage_root infos ctx fn = SOME (rl,rp) /\
    ~(s.vs_current_bb = rl /\ s.vs_inst_idx < rp) /\
    lookup_var runner t = SOME (n2w lo) /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions s.vs_inst_idx +
      (if (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
       then 1 else 0) /\
    fmp_frontier_rel fmp0 raw0 lo s.vs_fmp /\
    fmp_base_analyze (fn_insts fn) = SOME env /\
    fmp_reclaim_states infos fn = SOME states /\
    df_at NONE states s.vs_current_bb s.vs_inst_idx = SOME st /\
    MAP (\r. r.fr_mark) regions = SND (fmp_pop_at infos fn
      (liveness_analyze fn) env (s.vs_current_bb,s.vs_inst_idx) inst st) /\
    fmp_ledger_ok (fn_insts fn) env t lo regions /\
    EVERY (\r. fmp_frame_lo fmp0 ts <= r.fr_lo) regions /\
    fmp_ledger_link sm (fmp_frame_base raw0 stk) lo regions /\
    fmp_frame_covers sm env (fmp_frame_base raw0 stk) lo G /\
    (!i. MEM i (fn_insts fn) ==> ~MEM runner i.inst_outputs)
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        s.vs_inst_idx < LENGTH bb.bb_instructions /\
        EL s.vs_inst_idx bb.bb_instructions = inst` by
    (`o1_ctx_shape C` by gvs[fmp_stage_ctx_def] >>
     drule_all lowerDloadPtrRawReachableTheory.o1_ctx_shape_active_lookup >> strip_tac >>
     gvs[venomInstTheory.get_instruction_def]) >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    (fs[venomInstTheory.lookup_block_def] >>
     drule venomInstTheory.FIND_MEM >>
     drule venomInstTheory.FIND_P >> simp[]) >>
  gvs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  drule_all fmp_dalloca_lowered_needs >> strip_tac >>
  drule_all fmp_dalloca_root_exists >> strip_tac >>
  `~(s.vs_current_bb = rl /\ s.vs_inst_idx < rp)` by
    metis_tac[fmp_dalloca_not_before_root] >>
  Cases_on `s.vs_current_bb = rl` >> gvs[] >>
  drule_all fmp_stage_witness_pin >> strip_tac >>
  qexistsl [`infos`, `ctx`, `runner`] >> simp[] >>
  metis_tac[]
QED

Theorem fmp_dalloca_target_run:
  lookup_function name C.ctx_functions = SOME fn /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  DROP t.vs_inst_idx bb.bb_instructions = code ++ tail /\
  LENGTH code = n /\ 0 < n /\ run_insts k C code t = OK u ==>
  fmp_target_run k C name t n (u with vs_inst_idx := t.vs_inst_idx+n)
Proof
  strip_tac >>
  `t.vs_inst_idx + n <= LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[] >> decide_tac) >>
  simp[fmp_target_run_def] >>
  qexists_tac `u` >>
  qpat_x_assum `LENGTH code = n` (SUBST_ALL_TAC o SYM) >>
  simp[rich_listTheory.TAKE_APPEND]
QED

Theorem fmp_dalloca_control_advance:
  (EL idx insts).inst_opcode = DALLOCA /\
  root = SOME (rl,rp) /\ ~(lbl = rl /\ idx < rp) ==>
  fmp_stage_tidx plan root lbl insts (SUC idx) =
    fmp_stage_tidx plan root lbl insts idx +
      (if (lbl,idx) IN FDOM plan then 1 else 0) + 4
Proof
  strip_tac >> simp[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
  Cases_on `lbl = rl` >> gvs[]
QED

Theorem fmp_dalloca_runner_fresh:
  fmp_stage_lowered infos ctx runner fn fn' ==> ~MEM runner (fn_ir_vars fn)
Proof
  strip_tac >> gvs[fmp_stage_lowered_def] >>
  Cases_on `fresh_ir_var sp` >> gvs[] >>
  drule irSupplyTheory.fresh_ir_var_contract >>
  gvs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
      venomFnScheduleRunnerTheory.list_subset_def, EVERY_MEM] >> metis_tac[]
QED

Theorem fmp_dalloca_execution_from_suffix:
  (!inst size_op out runner sp vars restores (lbl:string) idx plan infos ctx insts code leftover sp'.
    inst.inst_opcode = DALLOCA /\ inst.inst_operands = [size_op] /\
    inst.inst_outputs = [out] /\ MEM runner sp.irs_used_vars /\
    list_subset vars sp.irs_used_vars /\ MEM out vars /\ runner <> out /\
    ALL_DISTINCT (MAP FST restores) /\
    (!j b. MEM ((lbl,j),b) restores <=> idx <= j /\ FLOOKUP plan (lbl,j) = SOME b) /\
    fmp_lower_indexed infos ctx runner lbl idx sp restores (inst::insts) =
      SOME (code,leftover,sp') ==>
    ?plus31 mask aligned ai ni mi bi tail.
      DROP (if (lbl,idx) IN FDOM plan then 1 else 0) code =
        [mk_inst ai ADD [Lit 31w;size_op] [plus31];
         mk_inst ni NOT [Lit 31w] [mask];
         mk_inst mi AND [Var plus31;Var mask] [aligned];
         mk_inst bi BUMP [Var runner;Var aligned] [out;runner]] ++ tail /\
      ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
      ~MEM plus31 vars /\ ~MEM mask vars /\ ~MEM aligned vars) /\
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ inst.inst_opcode = DALLOCA /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?out size_op sz z runner plus31 mask aligned s1 t1 fn' infos ctx bb
    rl rp env states st regions.
    z = ceil32 (w2n sz) /\ r = OK s1 /\
    inst.inst_operands = [size_op] /\ inst.inst_outputs = [out] /\
    eval_operand size_op s = SOME sz /\ eval_operand size_op t = SOME sz /\
    s1 = update_var out s.vs_fmp (s with vs_fmp := n2w (w2n s.vs_fmp+z)) /\
    t1 = (update_var runner (n2w (lo+z))
      (update_var out (n2w lo) (update_var aligned (n2w z)
       (update_var mask (~31w) (update_var plus31 (sz+31w) t)))))
      with vs_inst_idx := t.vs_inst_idx+4 /\
    (!k'. fmp_target_run k' C' fn.fn_name t 4 t1) /\
    w2n s.vs_fmp+z < dimword (:256) /\ lo+z < dimword (:256) /\
    fmp_frontier_rel fmp0 raw0 (lo+z) s1.vs_fmp /\
    ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
    EVERY (\v. ~MEM v (fn_ir_vars fn)) [plus31;mask;aligned;runner] /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    fmp_stage_lowered infos ctx runner fn fn' /\
    fmp_stage_root infos ctx fn = SOME (rl,rp) /\
    ~(s.vs_current_bb = rl /\ s.vs_inst_idx < rp) /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    fmp_base_analyze (fn_insts fn) = SOME env /\
    fmp_reclaim_states infos fn = SOME states /\
    df_at NONE states s.vs_current_bb s.vs_inst_idx = SOME st /\
    MAP (\r. r.fr_mark) regions = SND (fmp_pop_at infos fn
      (liveness_analyze fn) env (s.vs_current_bb,s.vs_inst_idx) inst st) /\
    fmp_ledger_ok (fn_insts fn) env t lo regions /\
    EVERY (\r. fmp_frame_lo fmp0 ts <= r.fr_lo) regions /\
    fmp_ledger_link sm (fmp_frame_base raw0 stk) lo regions /\
    fmp_frame_covers sm env (fmp_frame_base raw0 stk) lo G /\
    t.vs_inst_idx+4 = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions
      (SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all fmp_source_memory >> strip_tac >>
  drule_all fmp_dalloca_source >> strip_tac >>
  drule_all fmp_dalloca_frame_witness >> strip_tac >>
  `eval_operand size_op t = SOME sz` by
    (irule fmp_dalloca_size_agree >> metis_tac[MEM]) >>
  `~MEM runner (fn_ir_vars fn)` by metis_tac[fmp_dalloca_runner_fresh] >>
  `MEM out (fn_ir_vars fn)` by
    (simp[fmpStepSupplyTheory.fn_ir_vars_member] >>
     qexistsl [`bb`, `inst`] >> simp[MEM_EL] >> metis_tac[]) >>
  `runner <> out` by metis_tac[] >>
  `s.vs_inst_idx <= LENGTH bb.bb_instructions` by decide_tac >>
  `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
     bb.bb_label = rl ==> rp <= s.vs_inst_idx` by (rpt strip_tac >> gvs[] >> decide_tac) >>
  drule fmp_stage_tidx_code >>
  disch_then (qspecl_then [`s.vs_inst_idx`, `bb`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  `DROP s.vs_inst_idx bb.bb_instructions = inst::DROP (SUC s.vs_inst_idx) bb.bb_instructions`
    by metis_tac[rich_listTheory.DROP_CONS_EL] >>
  `?plus31 mask aligned ai ni mi bi tail.
     DROP (if (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
           then 1 else 0) code =
       [mk_inst ai ADD [Lit 31w;size_op] [plus31];
        mk_inst ni NOT [Lit 31w] [mask];
        mk_inst mi AND [Var plus31;Var mask] [aligned];
        mk_inst bi BUMP [Var runner;Var aligned] [out;runner]] ++ tail /\
     ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
     ~MEM plus31 (fn_ir_vars fn) /\ ~MEM mask (fn_ir_vars fn) /\
     ~MEM aligned (fn_ir_vars fn)` by
    (first_x_assum irule >> simp[] >>
     qexistsl [`ctx`, `infos`, `inst`, `DROP (SUC s.vs_inst_idx) bb.bb_instructions`,
               `leftover`, `restores`, `sp`, `sp'`] >> gvs[]) >>
  drule_all dalloca_relocate_exec >> strip_tac >>
  qmatch_asmsub_abbrev_tac `DROP _ code = seq ++ tail` >>
  `DROP t.vs_inst_idx bb'.bb_instructions = seq ++ tail` by
    (qpat_x_assum `DROP _ code = _` mp_tac >>
     qpat_x_assum `DROP _ bb'.bb_instructions = code` (SUBST_ALL_TAC o SYM) >>
     simp[rich_listTheory.DROP_DROP_T]) >>
  qpat_x_assum `!inst size_op out runner sp vars restores lbl idx plan infos ctx insts code leftover sp'. _` kall_tac >>
  qexistsl [`out`, `size_op`, `sz`, `ceil32 (w2n sz)`, `runner`, `plus31`, `mask`,
    `aligned`, `s1`, `(update_var runner (n2w (lo+ceil32 (w2n sz)))
      (update_var out (n2w lo) (update_var aligned (n2w (ceil32 (w2n sz)))
       (update_var mask (~31w) (update_var plus31 (sz+31w) t)))))
      with vs_inst_idx := t.vs_inst_idx+4`] >>
  qexistsl [`fn'`, `infos`, `ctx`, `bb`, `rl`, `rp`, `env`, `states`, `st`, `regions`] >>
  fs[FORALL_AND_THM, IgnAsm `t.vs_inst_idx = _`] >>
  simp[fmpRestorePropsTheory.fmp_restore_frame, IgnAsm `t.vs_inst_idx = _`] >>
  reverse conj_tac >- gvs[fmp_dalloca_control_advance] >>
  gen_tac >> irule fmp_dalloca_target_run >> simp[] >>
  qexistsl [`bb'`, `seq`, `tail`] >> simp[Abbr `seq`] >> gvs[]
QED

Theorem fmp_dalloca_execution:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ inst.inst_opcode = DALLOCA /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?out size_op sz z runner plus31 mask aligned s1 t1 fn' infos ctx bb
    rl rp env states st regions.
    z = ceil32 (w2n sz) /\ r = OK s1 /\
    inst.inst_operands = [size_op] /\ inst.inst_outputs = [out] /\
    eval_operand size_op s = SOME sz /\ eval_operand size_op t = SOME sz /\
    s1 = update_var out s.vs_fmp (s with vs_fmp := n2w (w2n s.vs_fmp+z)) /\
    t1 = (update_var runner (n2w (lo+z))
      (update_var out (n2w lo) (update_var aligned (n2w z)
       (update_var mask (~31w) (update_var plus31 (sz+31w) t)))))
      with vs_inst_idx := t.vs_inst_idx+4 /\
    (!k'. fmp_target_run k' C' fn.fn_name t 4 t1) /\
    w2n s.vs_fmp+z < dimword (:256) /\ lo+z < dimword (:256) /\
    fmp_frontier_rel fmp0 raw0 (lo+z) s1.vs_fmp /\
    ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
    EVERY (\v. ~MEM v (fn_ir_vars fn)) [plus31;mask;aligned;runner] /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    fmp_stage_lowered infos ctx runner fn fn' /\
    fmp_stage_root infos ctx fn = SOME (rl,rp) /\
    ~(s.vs_current_bb = rl /\ s.vs_inst_idx < rp) /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    fmp_base_analyze (fn_insts fn) = SOME env /\
    fmp_reclaim_states infos fn = SOME states /\
    df_at NONE states s.vs_current_bb s.vs_inst_idx = SOME st /\
    MAP (\r. r.fr_mark) regions = SND (fmp_pop_at infos fn
      (liveness_analyze fn) env (s.vs_current_bb,s.vs_inst_idx) inst st) /\
    fmp_ledger_ok (fn_insts fn) env t lo regions /\
    EVERY (\r. fmp_frame_lo fmp0 ts <= r.fr_lo) regions /\
    fmp_ledger_link sm (fmp_frame_base raw0 stk) lo regions /\
    fmp_frame_covers sm env (fmp_frame_base raw0 stk) lo G /\
    t.vs_inst_idx+4 = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions
      (SUC s.vs_inst_idx)
Proof
  strip_tac >> mp_tac fmp_dalloca_execution_from_suffix >>
  impl_tac >- (conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC fmp_dalloca_indexed_suffix) >>
               asm_rewrite_tac[]) >> simp[]
QED
