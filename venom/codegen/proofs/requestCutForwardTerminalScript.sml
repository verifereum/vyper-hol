Theory requestCutForwardTerminal
Ancestors
  fnFramePrefixDriver fnFramePrefix fnBlockBodySteps fnBlockBodyClasses contextCodegenRel
  o1LowerDloadRequestForward blockSimHelpers codegenRel asmSem venomExecSemantics
  venomInst rich_list list fnFrameSymbolicPrefix symFrameControl
  fnBlockBodyHelpers fnBlockBody unitShapeDefs asmSymSem codegenSymRel
  fnFrameSymbolicReady requestCutTerminalPrefix requestCutForwardReady
  o1ContractCfgNormJointCursors finalizerContract asmOptimizer
  asmDataEnv codegenEntryRel o1PassContract asmFrameRel vfmExecution
  symControlForwardDischargeOwn codegenSymbolicTerminalOwn
  fnPlanPlaceRevertPostamble finalizerContractOwn asmRelocDataEnv

val forward_plan_facts_tac =
  drule body_plan_inv_facts_reloc >> strip_tac >>
  qhdtm_assum `body_plan_inv_reloc`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_reloc_def]) >>
  rename1 `non_param_insts planned = _` >>
  `planned = bb` by fs[] >>
  qpat_x_assum `planned = bb` SUBST_ALL_TAC >>
  `!j. ~revert_forward_pair bb j k` by
    (rpt strip_tac >>
     qpat_assum `!i j. revert_forward_pair bb i j ==> _`
       (qspecl_then [`j`, `k`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     qpat_x_assum `revert_forward_pair bb j k` mp_tac >>
     simp[revert_forward_pair_def]) >>
  `?j. revert_forward_pair bb k j` by
    (qpat_x_assum `in_revert_forward fn s` mp_tac >>
     fs[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
  `k < LENGTH bb.bb_instructions` by
    (qpat_x_assum `revert_forward_pair bb k j` mp_tac >>
     simp[revert_forward_pair_def, get_instruction_def] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `EL k bb.bb_instructions = EL k bb.bb_instructions` by simp[] >>
  drule_all body_plan_inv_static_reloc >> strip_tac >>
  `DROP (k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb) =
     DROP k bb.bb_instructions` by simp[DROP_DROP_T] >>
  `!off. ~MEM (SORestore off) rest_ops /\ ~MEM (SOSpill off) rest_ops` by
    (qpat_x_assum `!j. revert_forward_pair bb k j ==> !ops ps_end. _`
       drule >> disch_then (qspecl_then [`rest_ops`, `ps_after`] mp_tac) >>
     gvs[])

Theorem active_frame_forward_abort_reloc:
  active_frame_plan_reloc lo rp unit cpl prog fn s ast ra rest mem0 /\
  in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel unit.cu_context bb s = Abort reason t ==>
  ?n out.
    (asm_steps lo (build_offset_to_pc prog) prog n ast = AsmRevert out \/
     asm_steps lo (build_offset_to_pc prog) prog n ast = AsmFault out) /\
    out.as_requests = s.vs_requests
Proof
  pure_rewrite_tac[active_frame_plan_reloc_def] >> strip_tac >>
  forward_plan_facts_tac >>
  drule_all body_plan_revert_step_reloc >>
  disch_then (qspec_then `fuel` mp_tac) >> simp[body_result_simple_def, body_result_def] >>
  strip_tac >>
  `t.vs_requests = s.vs_requests` by
    (qpat_x_assum `revert_forward_pair bb k j` mp_tac >>
     simp[revert_forward_pair_def] >> strip_tac >>
     drule_at (Pat `exec_block _ _ _ _ = _`) copy_assign_suffix_abort_requests >>
     disch_then irule >> metis_tac[]) >>
  fs[venom_asm_terminal_rel_def] >> metis_tac[]
QED

Theorem normal_frame_forward_abort:
  normal_frame_plan rp unit cpl prog vs0 es
    (JointConfig stk PG G tn fn inst s oms om hs h) ast /\
  active_inst fn inst s /\ ~is_param_opcode inst.inst_opcode /\
  in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel unit.cu_context bb s = Abort reason t ==>
  ?n out.
    (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n ast = AsmRevert out \/
     asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n ast = AsmFault out) /\
    out.as_requests = s.vs_requests
Proof
  strip_tac >> drule_all normal_frame_plan_active >>
  disch_then (qx_choosel_then [`m`, `mid`, `saved`, `ra`, `rest`, `mem0`]
    strip_assume_tac) >>
  qpat_x_assum `active_frame_plan _ _ _ _ _ _ _ _ _ _`
    (assume_tac o REWRITE_RULE [GSYM active_frame_plan_reloc_specialize]) >>
  drule_all active_frame_forward_abort_reloc >>
  disch_then (qx_choosel_then [`n`, `out`] strip_assume_tac) >>
  qexistsl_tac [`m + n`, `out`] >>
  metis_tac[asm_steps_compose_revert, asm_steps_compose_fault]
QED

Theorem active_frame_symbolic_forward_abort[local]:
  active_frame_symbolic_plan env rp unit cpl prog fn s ast ra rest mem0 ret srest labs0 ss /\
  focus_s7_symbolic_context unit prog /\
  in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel unit.cu_context bb s = Abort reason t ==>
  ?n out.
    (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n ast = AsmRevert out \/
     asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n ast = AsmFault out) /\
    sym_terminal (sym_steps prog env n ss) /\
    out.as_requests = s.vs_requests
Proof
  pure_rewrite_tac[active_frame_symbolic_plan_def, focus_s7_symbolic_context_def,
    body_plan_inv_reloc_specialize] >> strip_tac >>
  forward_plan_facts_tac >>
  `fn_shape_ok fn` by fs[unit_shape_ok_def, EVERY_MEM] >>
  `!inst. MEM inst bb.bb_instructions ==> inst_shape_ok inst` by
    (rpt strip_tac >> drule_all body_inst_ready >> fs[EVERY_MEM]) >>
  drule_all rf_pair_no_labels >> strip_tac >>
  `asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp rest_ops)` by
    (qspecl_then [`prog`, `pc0`, `cpl.cp_initial_fmp`, `bb.bb_label`,
                  `prefix_ops`, `rest_ops`, `[]`] mp_tac block_ops_at >>
     REWRITE_TAC[APPEND_NIL] >>
     (impl_tac >-
       (qpat_assum `block_ops = _` (fn eq =>
          qpat_assum `asm_block_at prog pc0 _` (fn th =>
            ACCEPT_TAC (REWRITE_RULE [eq] th))))) >>
     qpat_assum `ast.as_pc = _` (fn eq => simp[eq])) >>
  `!name. MEM (AsmOp name) (execute_plan cpl.cp_initial_fmp rest_ops) ==>
           IS_SOME (evm_opcode_byte name)` by
    (rpt strip_tac >> drule_all body_placed_target_safe >> simp[]) >>
  qpat_x_assum `!j. revert_forward_pair bb k j ==> !i inst op. _` drule >>
  strip_tac >>
  qpat_assum `DROP (k - _) (non_param_insts bb) = _` (fn drop_eq =>
    qpat_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ ps = SOME (rest_ops,ps_after)`
      (assume_tac o REWRITE_RULE [drop_eq])) >>
  qspecl_then [`fuel`, `unit.cu_context`, `cpl`,
    `SND (compute_label_offsets prog)`, `build_offset_to_pc prog`, `prog`,
    `liveness`, `dfg`, `cfg`, `fn`, `bb`, `k`, `j`, `spill_base`,
    `ps`, `s`, `ast`, `rest_ops`, `ps_after`, `ra`, `rest`, `mem0`,
    `env`, `ret`, `srest`, `labs0`, `ss`] mp_tac sym_revert_forward_frame_sim_deep >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE asm_rewrite_tac[]))) >>
  disch_then (qspecl_then [`reason`, `t`] mp_tac) >> simp[] >> strip_tac >>
  `t.vs_requests = s.vs_requests` by
    (qpat_x_assum `revert_forward_pair bb k j` mp_tac >>
     simp[revert_forward_pair_def] >> strip_tac >>
     drule_at (Pat `exec_block _ _ _ _ = _`) copy_assign_suffix_abort_requests >>
     disch_then irule >> metis_tac[]) >>
  fs[venom_asm_terminal_rel_def] >> metis_tac[]
QED

Theorem normal_frame_symbolic_forward_abort:
  normal_frame_symbolic_plan env rp unit cpl prog vs0 es
    (JointConfig stk PG G tn fn inst s oms om hs h) ast ss /\
  focus_s7_symbolic_context unit prog /\
  active_inst fn inst s /\ ~is_param_opcode inst.inst_opcode /\
  in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel unit.cu_context bb s = Abort reason t ==>
  ?n out.
    (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n ast = AsmRevert out \/
     asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n ast = AsmFault out) /\
    sym_terminal (sym_steps prog env n ss) /\
    out.as_requests = s.vs_requests
Proof
  strip_tac >> drule_all normal_frame_symbolic_plan_active >>
  disch_then (qx_choosel_then [`m`, `mid`, `rss`, `ra`, `rest`, `mem0`,
    `ret`, `srest`, `labs0`] strip_assume_tac) >>
  drule_all active_frame_symbolic_forward_abort >>
  disch_then (qx_choosel_then [`n`, `out`] strip_assume_tac) >>
  qexistsl_tac [`m + n`, `out`] >>
  simp[sym_steps_add] >>
  metis_tac[asm_steps_compose_revert, asm_steps_compose_fault]
QED

Theorem forward_prefix_label_disciplined:
  sym_steps prog env prefix (sym_init a0) = SymOK ss /\
  normal_frame_symbolic_plan env rp unit cpl prog vs0 es
    (JointConfig stk PG G tn fn inst s oms om hs h) ast ss /\
  focus_s7_symbolic_context unit prog /\
  active_inst fn inst s /\ ~is_param_opcode inst.inst_opcode /\
  in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel unit.cu_context bb s = Abort reason t ==>
  label_disciplined env prog a0
Proof
  strip_tac >> drule_all normal_frame_symbolic_forward_abort >> strip_tac >>
  `sym_terminal (sym_steps prog env (prefix + n) (sym_init a0))` by
    simp[sym_steps_add] >>
  drule sym_steps_terminal_run >> disch_then (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  irule sym_terminal_disciplined >>
  fs[focus_s7_symbolic_context_def] >> qexists_tac `prefix + n` >> simp[]
QED

Theorem request_cut_stopped_forward_crossed:
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  asm_frame_prog_ok prog' /\ vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es
    ((entry_asm_state vs0 es) with as_code := assemble prog' ++ vs0.vs_data_section) es /\
  run_call es = SOME (result,final) /\ ~frame_resource_starved es result final /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog n (entry_asm_state vs0 es) = AsmOK ast /\
  q9 = JointConfig stk PG G tn fn9 inst9 s9 oms om hs hist /\
  cfg_norm_joint_cursors C8 unit.cu_context (schedules,(rounds,cells),saved) q8 q9 /\
  o1_ctx_shape unit.cu_context /\
  (fin = K SOME ==> normal_frame_plan rp unit cpl prog planner_base es q9 ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog (asm_data_env prog vs0.vs_code) n
      (sym_init (entry_asm_state vs0 es)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code)
      rp unit cpl prog vs0 es q9 ast ss /\ focus_s7_symbolic_context unit prog) /\
  active_inst fn9 inst9 s9 /\ ~is_param_opcode inst9.inst_opcode /\
  in_revert_forward fn9 s9 /\
  raw_variant fmp vs vs0 /\ raw_reachable vs C fn inst s /\
  inst.inst_opcode <> INVOKE /\ LENGTH s.vs_requests = k /\
  step_inst fuel C inst s = OK post /\ k < LENGTH post.vs_requests ==>
  k < LENGTH s9.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `q9 = _` SUBST_ALL_TAC >>
  drule_all (Q.INST [`fuel` |-> `0`] request_cut_stopped_forward_ready) >>
  strip_tac >>
  `fin = asm_opt_finalizer ==>
    label_disciplined (asm_data_env prog (assemble prog ++ vs0.vs_data_section))
      prog (entry_asm_state vs0 es)` by
    (strip_tac >>
     qpat_assum `vs0.vs_code = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     metis_tac[forward_prefix_label_disciplined]) >>
  `?m out.
    (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog m ast = AsmRevert out \/
     asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog m ast = AsmFault out) /\ out.as_requests = s9.vs_requests` by
    (Cases_on `fin = asm_opt_finalizer`
     >- metis_tac[normal_frame_symbolic_forward_abort] >>
     `fin = K SOME` by fs[accepted_finalizers_def] >>
     metis_tac[normal_frame_forward_abort]) >>
  mp_tac (Q.INST [`t` |-> `s9`] request_cut_terminal_prefix_crossed) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  simp[]
QED

Theorem active_frame_symbolic_forward_abort_own[local]:
  active_frame_symbolic_plan_own lo env own rp unit cpl prog fn s ast ra rest mem0 ret srest labs0 ss /\
  code_labels_agree prog lo /\ focus_s7_symbolic_context_own allow_own unit prog /\
  in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel unit.cu_context bb s = Abort reason t ==>
  ?n out.
    (asm_steps lo (build_offset_to_pc prog)
       prog n ast = AsmRevert out \/
     asm_steps lo (build_offset_to_pc prog)
       prog n ast = AsmFault out) /\
    sym_terminal (sym_steps_mode allow_own prog env own n ss) /\
    out.as_requests = s.vs_requests
Proof
  pure_rewrite_tac[active_frame_symbolic_plan_own_def, focus_s7_symbolic_context_own_def] >> strip_tac >>
  forward_plan_facts_tac >>
  `fn_shape_ok fn` by fs[unit_shape_ok_def, EVERY_MEM] >>
  `!inst. MEM inst bb.bb_instructions ==> inst_shape_ok inst` by
    (rpt strip_tac >> drule_all body_inst_ready >> fs[EVERY_MEM]) >>
  drule_all rf_pair_no_labels >> strip_tac >>
  `asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp rest_ops)` by
    (qspecl_then [`prog`, `pc0`, `cpl.cp_initial_fmp`, `bb.bb_label`,
                  `prefix_ops`, `rest_ops`, `[]`] mp_tac block_ops_at >>
     REWRITE_TAC[APPEND_NIL] >>
     (impl_tac >-
       (qpat_assum `block_ops = _` (fn eq =>
          qpat_assum `asm_block_at prog pc0 _` (fn th =>
            ACCEPT_TAC (REWRITE_RULE [eq] th))))) >>
     qpat_assum `ast.as_pc = _` (fn eq => simp[eq])) >>
  `!name. MEM (AsmOp name) (execute_plan cpl.cp_initial_fmp rest_ops) ==>
           IS_SOME (evm_opcode_byte name)` by
    (rpt strip_tac >> drule_all body_placed_target_safe >> simp[]) >>
  qpat_x_assum `!j. revert_forward_pair bb k j ==> !i inst op. _` drule >>
  strip_tac >>
  qpat_assum `DROP (k - _) (non_param_insts bb) = _` (fn drop_eq =>
    qpat_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ ps = SOME (rest_ops,ps_after)`
      (assume_tac o REWRITE_RULE [drop_eq])) >>
  qspecl_then [`allow_own`, `own`, `lo`, `prog`, `env`, `fuel`,
    `unit.cu_context`, `cpl`, `build_offset_to_pc prog`,
    `liveness`, `dfg`, `cfg`, `fn`, `bb`, `k`, `j`, `spill_base`,
    `ps`, `s`, `ast`, `rest_ops`, `ps_after`, `ra`, `rest`, `mem0`,
    `ret`, `srest`, `labs0`, `ss`] mp_tac sym_revert_forward_frame_sim_deep_own >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE asm_rewrite_tac[]))) >>
  disch_then (qspecl_then [`reason`, `t`] mp_tac) >> simp[] >> strip_tac >>
  `t.vs_requests = s.vs_requests` by
    (qpat_x_assum `revert_forward_pair bb k j` mp_tac >>
     simp[revert_forward_pair_def] >> strip_tac >>
     drule_at (Pat `exec_block _ _ _ _ = _`) copy_assign_suffix_abort_requests >>
     disch_then irule >> metis_tac[]) >>
  fs[venom_asm_terminal_rel_def] >> metis_tac[]
QED

Theorem normal_frame_symbolic_forward_abort_own:
  normal_frame_symbolic_plan_own allow_own lo env own rp unit cpl prog vs0 es
    (JointConfig stk PG G tn fn inst s oms om hs h) ast ss /\
  code_labels_agree prog lo /\ focus_s7_symbolic_context_own allow_own unit prog /\
  active_inst fn inst s /\ ~is_param_opcode inst.inst_opcode /\
  in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel unit.cu_context bb s = Abort reason t ==>
  ?n out.
    (asm_steps lo (build_offset_to_pc prog)
       prog n ast = AsmRevert out \/
     asm_steps lo (build_offset_to_pc prog)
       prog n ast = AsmFault out) /\
    sym_terminal (sym_steps_mode allow_own prog env own n ss) /\
    out.as_requests = s.vs_requests
Proof
  strip_tac >> drule_all normal_frame_symbolic_plan_active_own >>
  disch_then (qx_choosel_then [`m`, `mid`, `rss`, `ra`, `rest`, `mem0`,
    `ret`, `srest`, `labs0`] strip_assume_tac) >>
  drule_all active_frame_symbolic_forward_abort_own >>
  disch_then (qx_choosel_then [`n`, `out`] strip_assume_tac) >>
  qexistsl_tac [`m + n`, `out`] >>
  simp[sym_steps_mode_add] >>
  metis_tac[asm_steps_compose_revert, asm_steps_compose_fault]
QED

Theorem request_cut_stopped_forward_crossed_own:
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  asm_frame_prog_ok prog' /\ vs0.vs_code = assemble prog' ++ vs0.vs_data_section /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es
    (entry_asm_state vs0 es) es /\
  run_call es = SOME (result,final) /\ ~frame_resource_starved es result final /\
  asm_steps (lo_reloc prog prog') (build_offset_to_pc prog)
    prog n (entry_asm_state vs0 es) = AsmOK ast /\
  q9 = JointConfig stk PG G tn fn9 inst9 s9 oms om hs hist /\
  cfg_norm_joint_cursors C8 unit.cu_context (schedules,(rounds,cells),saved) q8 q9 /\
  o1_ctx_shape unit.cu_context /\
  (fin = K SOME ==> normal_frame_plan rp unit cpl prog planner_base es q9 ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps_mode T prog (asm_data_env prog' vs0.vs_code) vs0.vs_code n
      (sym_init (entry_asm_state vs0 es)) = SymOK ss /\
    normal_frame_symbolic_plan_own T (lo_reloc prog prog')
      (asm_data_env prog' vs0.vs_code) vs0.vs_code rp unit cpl prog vs0 es q9 ast ss /\
    focus_s7_symbolic_context_own T unit prog /\
    asm_data_env_lo_ok (lo_reloc prog prog') prog (asm_data_env prog' vs0.vs_code)
      vs0.vs_code) /\
  active_inst fn9 inst9 s9 /\ ~is_param_opcode inst9.inst_opcode /\
  in_revert_forward fn9 s9 /\
  raw_variant fmp vs vs0 /\ raw_reachable vs C fn inst s /\
  inst.inst_opcode <> INVOKE /\ LENGTH s.vs_requests = k /\
  step_inst fuel C inst s = OK post /\ k < LENGTH post.vs_requests ==>
  k < LENGTH s9.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `q9 = _` SUBST_ALL_TAC >>
  drule_all (Q.INST [`fuel` |-> `0`] request_cut_stopped_forward_ready) >>
  strip_tac >>
  `code_labels_agree prog (lo_reloc prog prog')` by simp[lo_reloc_code_labels_agree] >>
  `(?m out.
    (asm_steps (lo_reloc prog prog') (build_offset_to_pc prog) prog m ast = AsmRevert out \/
     asm_steps (lo_reloc prog prog') (build_offset_to_pc prog) prog m ast = AsmFault out) /\
    out.as_requests = s9.vs_requests) /\
   (fin = asm_opt_finalizer ==>
     asm_static_wf prog /\
     asm_data_env_lo_ok (lo_reloc prog prog') prog (asm_data_env prog' vs0.vs_code)
       vs0.vs_code /\
     label_disciplined_own (asm_data_env prog' vs0.vs_code) vs0.vs_code
       prog (entry_asm_state vs0 es))` by
    (Cases_on `fin = asm_opt_finalizer`
     >- (fs[] >>
         `asm_static_wf prog` by fs[focus_s7_symbolic_context_own_def] >>
         drule_all normal_frame_symbolic_forward_abort_own >>
         disch_then (qx_choosel_then [`m`, `out`] strip_assume_tac) >>
         `sym_terminal (sym_steps_mode T prog (asm_data_env prog' vs0.vs_code)
           vs0.vs_code (n + m) (sym_init (entry_asm_state vs0 es)))` by
           (qpat_assum `sym_steps_mode T prog _ _ n _ = SymOK ss`
              (fn prefix => simp_tac bool_ss [sym_steps_mode_add, prefix, sym_result_case_def]) >>
            first_assum ACCEPT_TAC) >>
         drule_all sym_steps_mode_terminal_disciplined >> simp[] >> metis_tac[]) >>
     `fin = K SOME` by fs[accepted_finalizers_def] >>
     gvs[combinTheory.K_THM, lo_reloc_refl] >>
     metis_tac[normal_frame_forward_abort]) >>
  mp_tac (Q.INST [`t` |-> `s9`] request_cut_terminal_prefix_crossed_own) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  simp[]
QED
