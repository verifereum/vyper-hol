(* Local packets on the existing joint execution; no completed callee run. *)
Theory fnFramePrefixDriver
Ancestors
  fnFramePrefix fnFramePrefixEntry fnFramePrefixStack
  fnBlockBodySteps fnBlockBodyClasses fnBlockBodyHelpers fnEntryParams
  frameJointTransition frameJointTrace frameJointRevert frameOriginHistory
  frameExecutionHistory
  frameRel codegenEntryRel codegenAsmProgOk contextCodegenRel unitMemInv unitShapeDefs stackPlanGen
  asmFrameRun asmFrameRel asmSem blockSimHelpers venomExecSemantics venomInst venomState
  list rich_list arithmetic finite_map

Definition normal_frame_plan_def:
  normal_frame_plan rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast <=>
  ?saved ra rest mem0.
    frame_stack_plan rpolicy unit cpl prog vs0 es0 stk fn saved ra rest mem0 /\
    (active_frame_plan rpolicy unit cpl prog fn s ast ra rest mem0 \/
     ?entry pc_ret.
       entry_frame_plan rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0)
End

Theorem active_frame_local_step:
  active_frame_plan rpolicy unit cpl prog fn s ast ra rest mem0 /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  source_memory_reads_disjoint cpl inst s /\
  context_source_memory_writes_disjoint cpl inst s /\
  step_inst fuel unit.cu_context inst s = OK post ==>
  ?n ast1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    active_frame_plan rpolicy unit cpl prog fn
      (post with vs_inst_idx := SUC s.vs_inst_idx) ast1 ra rest mem0
Proof
  strip_tac >> Cases_on `inst.inst_opcode = GAS`
  >- (drule_all active_frame_gas_step >> simp[]) >>
  drule_all active_frame_ordinary_step >> simp[]
QED

Theorem active_frame_rf_entry:
  active_frame_plan rpolicy unit cpl prog fn s ast ra rest mem0 /\
  in_revert_forward fn s ==>
  ?bb stopidx.
    ALL_DISTINCT (fn_labels fn) /\
    joint_revert_suffix fn bb s.vs_inst_idx stopidx
      (JointConfig stk PG G tn fn inst s oms om hs h)
Proof
  rw[active_frame_plan_def] >>
  drule body_plan_inv_facts >> strip_tac >>
  `(!i j. revert_forward_pair bb i j ==> k <= i \/ j < k) /\
   s.vs_inst_idx = k /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    fs[body_plan_inv_def] >>
  `ALL_DISTINCT (fn_labels fn)` by
    fs[codegen_ready_fn_def, venomWfTheory.wf_function_def] >>
  fs[in_revert_forward_def, revert_forward_at_def] >>
  qexistsl_tac [`bb`, `j`] >> simp[joint_revert_suffix_def] >>
  fs[revert_forward_pair_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL,
    arithmeticTheory.LESS_IMP_LESS_OR_EQ, arithmeticTheory.NOT_LESS_EQUAL]
QED

Theorem entry_frame_plan_nonparam:
  entry_frame_plan rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0 /\
  active_inst fn inst s /\ ~is_param_opcode inst.inst_opcode ==>
  ?n ast1.
    0 < n /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    active_frame_plan rpolicy unit cpl prog fn s ast1 ra rest mem0
Proof
  strip_tac >>
  `s.vs_inst_idx <= LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    fs[entry_frame_plan_def] >>
  `s.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    (spose_not_then assume_tac >>
     `s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
       decide_tac >>
     drule_all entry_frame_active_param >> simp[]) >>
  drule_all entry_frame_plan_ready >> simp[]
QED

Theorem normal_frame_plan_active:
  normal_frame_plan rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast /\
  active_inst fn inst s /\ ~is_param_opcode inst.inst_opcode ==>
  ?n ast1 saved ra rest mem0.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    frame_stack_plan rpolicy unit cpl prog vs0 es0 stk fn saved ra rest mem0 /\
    active_frame_plan rpolicy unit cpl prog fn s ast1 ra rest mem0
Proof
  rw[normal_frame_plan_def]
  >- (qexistsl_tac [`0`, `ast`, `saved`, `ra`, `rest`, `mem0`] >>
      simp[asm_steps_def]) >>
  drule_all entry_frame_plan_nonparam >> strip_tac >>
  qexistsl_tac [`n`, `ast1`, `saved`, `ra`, `rest`, `mem0`] >> simp[]
QED

Theorem normal_frame_next_step:
  normal_frame_plan rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  source_memory_reads_disjoint cpl inst s /\
  context_source_memory_writes_disjoint cpl inst s /\
  step_inst fuel unit.cu_context inst s = OK post ==>
  ?n ast1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    normal_frame_plan rpolicy unit cpl prog vs0 es0
      (JointConfig stk PG' G' tn' fn inst'
        (post with vs_inst_idx := SUC s.vs_inst_idx) oms' om' hs' h') ast1
Proof
  rw[normal_frame_plan_def]
  >- (drule_all active_frame_local_step >> strip_tac >>
      qexistsl_tac [`n`, `ast1`] >> conj_tac >- first_assum ACCEPT_TAC >>
      simp[normal_frame_plan_def] >> metis_tac[]) >>
  Cases_on `s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions)`
  >- (drule_all entry_frame_active_param >> strip_tac >>
      mp_tac (Q.INST [`fuel` |-> `fuel`, `rpolicy` |-> `rpolicy`,
        `unit` |-> `unit`, `cpl` |-> `cpl`, `prog` |-> `prog`,
        `fn` |-> `fn`, `entry` |-> `entry`, `s` |-> `s`, `ast` |-> `ast`,
        `ra` |-> `ra`, `pc_ret` |-> `pc_ret`, `rest` |-> `rest`, `mem0` |-> `mem0`]
        entry_frame_plan_next) >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >> gvs[] >>
      qexistsl_tac [`0`, `ast`] >> simp[asm_steps_def, normal_frame_plan_def] >>
      metis_tac[]) >>
  `s.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    (fs[entry_frame_plan_def] >> gvs[] >> decide_tac) >>
  drule_all entry_frame_plan_ready >>
  disch_then (qx_choosel_then [`m`, `ready`] strip_assume_tac) >>
  drule_all active_frame_local_step >>
  disch_then (qx_choosel_then [`n`, `next`] strip_assume_tac) >>
  qexistsl_tac [`m+n`, `next`] >> conj_tac
  >- (irule asm_steps_compose_ok >> qexists_tac `ready` >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  simp[normal_frame_plan_def] >> metis_tac[]
QED

Theorem normal_frame_gas_count_bound:
  normal_frame_plan rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast /\
  active_inst fn inst s /\ inst.inst_opcode = GAS /\
  asm_frame_prog_ok prog /\
  asm_frame_rel tail prog data es0 (entry_asm_state vs0 es0) es0 /\
  run_call es0 = SOME (result,final) /\ ~frame_resource_starved es0 result final /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog n (entry_asm_state vs0 es0) = AsmOK ast /\
  s.vs_gas_readings = DROP (k-1) vs0.vs_gas_readings /\ 0 < k ==>
  k <= LENGTH (gas_readings es0)
Proof
  strip_tac >>
  `~is_param_opcode inst.inst_opcode` by simp[is_param_opcode_def] >>
  drule_all normal_frame_plan_active >>
  disch_then (qx_choosel_then [`m`, `ready`, `saved`, `ra`, `rest`, `mem0`]
    strip_assume_tac) >>
  drule_all active_frame_gas_ready >> strip_tac >>
  `asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     prog (n+m) (entry_asm_state vs0 es0) = AsmOK ready` by
    (irule asm_steps_compose_ok >> qexists_tac `ast` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qspecl_then [`n+m`, `k`, `tail`, `prog`, `data`, `es0`,
    `entry_asm_state vs0 es0`, `es0`, `ready`, `result`, `final`]
    mp_tac asm_frame_prefix_gas_count_bound >>
  asm_simp_tac (srw_ss()) [entry_asm_state_def]
QED

Theorem normal_frame_initial:
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
  initial_ctx_rel_tail tail cpl prog unit.cu_context vs0 es0 /\
  joint_initial vs0 unit.cu_context q ==>
  normal_frame_plan rpolicy unit cpl prog vs0 es0 q (entry_asm_state vs0 es0)
Proof
  strip_tac >>
  drule_all entry_frame_plan_initial >>
  disch_then (qx_choosel_then [`root`, `others`, `lbl`, `entry`]
    strip_assume_tac) >>
  qpat_x_assum `joint_initial _ _ _` mp_tac >>
  simp[Once joint_initial_cases] >> rpt strip_tac >>
  gvs[lookup_function_def, FIND_thm] >>
  qabbrev_tac `start = vs0 with
    <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>` >>
  `entry_frame_plan rpolicy unit cpl prog fn start start
    (entry_asm_state vs0 es0) 0w 0 [] (entry_asm_state vs0 es0).as_memory` by
    fs[Abbr `start`] >>
  `codegen_ready_fn fn /\
   fn_entry_state_rel cpl fn start (entry_asm_state vs0 es0) 0w []` by
    (fs[entry_frame_plan_def] >> metis_tac[body_fn_shape]) >>
  `enters_block fn start (start with vs_inst_idx := 0)` by
    metis_tac[entry_prefix_enters] >>
  `s1 = start` by gvs[enters_block_def, Abbr `start`] >>
  `frame_stack_plan rpolicy unit cpl prog vs0 es0 [] fn
    (entry_asm_state vs0 es0) 0w [] (entry_asm_state vs0 es0).as_memory` by
    (fs[Abbr `start`] >> metis_tac[frame_stack_plan_entry]) >>
  simp[normal_frame_plan_def] >> metis_tac[]
QED

Theorem active_frame_call_entry:
  frame_stack_plan rpolicy unit cpl prog vs0 es0 stk fn saved ra rest mem0 /\
  frame_history vs0 unit.cu_context stk PG G tn fn inst s hs history /\
  active_frame_plan rpolicy unit cpl prog fn s ast ra rest mem0 /\
  active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\
  lookup_function nm unit.cu_context.ctx_functions = SOME callee /\
  eval_operands arg_ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\
  f.cf_fn = fn /\ f.cf_inst = inst /\ f.cf_state = s ==>
  ?n cas ret_off residual.
    0 < n /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK cas /\
    frame_stack_plan rpolicy unit cpl prog vs0 es0 (f::stk) callee cas
      (n2w ret_off) (residual ++ rest) cas.as_memory /\
    entry_frame_plan rpolicy unit cpl prog callee cs s1 cas (n2w ret_off)
      (ast.as_pc + n) (residual ++ rest) cas.as_memory
Proof
  strip_tac >>
  qpat_x_assum `active_frame_plan _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [active_frame_plan_def]) >>
  drule_all frame_stack_plan_push >>
  disch_then (qx_choosel_then [`n`, `cas`, `ret_off`, `residual`, `j`]
    strip_assume_tac) >>
  qpat_assum `body_plan_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_def]) >>
  `codegen_ready_fn callee` by
    (qspecl_then [`unit.cu_context`, `unit`, `\_ _ _ _. F`, `cpl`, `j`, `callee`]
       mp_tac body_fn_shape >> simp[]) >>
  `enters_block callee cs (cs with vs_inst_idx := 0)` by
    metis_tac[entry_prefix_enters] >>
  `s1 = cs with vs_inst_idx := 0` by gvs[enters_block_def] >>
  `!l. FLOOKUP cs.vs_labels l =
    OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    gvs[setup_callee_def, AllCaseEqs()] >>
  qexistsl_tac [`n`, `cas`, `ret_off`, `residual`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`i` |-> `j`, `r` |-> `EL j cpl.cp_regions`,
    `fn` |-> `callee`, `entry` |-> `cs`, `ast` |-> `cas`,
    `ra` |-> `n2w ret_off`, `pc_ret` |-> `ast.as_pc + n`,
    `rest` |-> `residual ++ rest`] (SPEC_ALL entry_frame_plan_start)) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  disch_then ACCEPT_TAC
QED

Theorem normal_frame_jump_step:
  normal_frame_plan rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel unit.cu_context inst s = OK post /\
  enters_block fn post s1 ==>
  ?n ast1.
    0 < n /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    normal_frame_plan rpolicy unit cpl prog vs0 es0
      (JointConfig stk PG' G' tn' fn inst' s1 oms' om' hs' h') ast1
Proof
  strip_tac >>
  `~is_param_opcode inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def, is_param_opcode_def]) >>
  drule_all normal_frame_plan_active >>
  disch_then (qx_choosel_then [`m`, `ready`, `saved`, `ra`, `rest`, `mem0`]
    strip_assume_tac) >>
  drule_all active_frame_jump_step >>
  disch_then (qx_choosel_then [`n`, `next`] strip_assume_tac) >>
  qexistsl_tac [`m+n`, `next`] >> rpt conj_tac >> TRY decide_tac
  >- (irule asm_steps_compose_ok >> qexists_tac `ready` >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  simp[normal_frame_plan_def] >> metis_tac[]
QED

Theorem normal_frame_return_step:
  normal_frame_plan rpolicy unit cpl prog vs0 es0
    (JointConfig (f::stk) PG G tn fn inst s oms om hs h) ast /\
  joint_config_reachable vs0 unit.cu_context
    (JointConfig (f::stk) PG G tn fn inst s oms om hs h) /\
  active_inst fn inst s /\
  step_inst fuel unit.cu_context inst s = IntRet ret send /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state send)) = SOME post ==>
  ?n ast1.
    0 < n /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    normal_frame_plan rpolicy unit cpl prog vs0 es0
      (JointConfig stk PG' G' tn' f.cf_fn inst'
        (post with vs_inst_idx := SUC f.cf_state.vs_inst_idx) oms' om' hs' h') ast1
Proof
  strip_tac >>
  `frame_history vs0 unit.cu_context (f::stk) PG G tn fn inst s
    (MAP origin_observations hs) (origin_observations h)` by
    (fs[joint_config_reachable_def] >>
     drule joint_origin_history_projection >> simp[]) >>
  `~is_param_opcode inst.inst_opcode` by
    (spose_not_then assume_tac >> fs[is_param_opcode_iff] >>
     gvs[step_inst_def, step_inst_base_opcode_eqs, AllCaseEqs()]) >>
  drule_all normal_frame_plan_active >>
  disch_then (qx_choosel_then [`m`, `ready`, `saved`, `ra`, `rest`, `mem0`]
    strip_assume_tac) >>
  `inst.inst_opcode = RET` by
    (qpat_assum `active_frame_plan _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [active_frame_plan_def]) >>
     drule_all body_plan_active_inst >> strip_tac >>
     drule_all body_plan_inv_inst >> strip_tac >>
     metis_tac[codegen_ready_intret_opcode]) >>
  drule_all frame_stack_plan_ret >>
  disch_then (qx_choosel_then [`nr`, `asr`] strip_assume_tac) >>
  drule_all frame_stack_plan_pop >>
  disch_then (qx_choosel_then [`nc`, `fin`, `caller_saved`, `caller_ra`,
    `caller_rest`, `caller_mem0`] strip_assume_tac) >>
  qexistsl_tac [`m + (nr + nc)`, `fin`] >> rpt conj_tac >> TRY decide_tac
  >- (irule asm_steps_compose_ok >> qexists_tac `ready` >> conj_tac
      >- first_assum ACCEPT_TAC >>
      irule asm_steps_compose_ok >> qexists_tac `asr` >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  simp[normal_frame_plan_def] >> metis_tac[]
QED

Theorem normal_frame_call_progress:
  normal_frame_plan rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn callinst s oms om hs h) ast /\
  joint_config_reachable vs0 unit.cu_context
    (JointConfig stk PG G tn fn callinst s oms om hs h) /\
  active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
  callinst.inst_operands = Label nm :: arg_ops /\
  lookup_function nm unit.cu_context.ctx_functions = SOME callee /\
  eval_operands arg_ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\
  f.cf_fn = fn /\ f.cf_inst = callinst /\ f.cf_state = s ==>
  ?n ast1.
    0 < n /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    normal_frame_plan rpolicy unit cpl prog vs0 es0
      (JointConfig (f::stk) PG' G' tn' callee inst' s1 oms' om' hs' h') ast1
Proof
  strip_tac >>
  `frame_history vs0 unit.cu_context stk PG G tn fn callinst s
    (MAP origin_observations hs) (origin_observations h)` by
    (fs[joint_config_reachable_def] >>
     drule joint_origin_history_projection >> simp[]) >>
  `~is_param_opcode callinst.inst_opcode` by simp[is_param_opcode_def] >>
  drule_all normal_frame_plan_active >>
  disch_then (qx_choosel_then [`m`, `ready`, `saved`, `ra`, `rest`, `mem0`]
    strip_assume_tac) >>
  drule_all active_frame_call_entry >>
  disch_then (qx_choosel_then [`n`, `cas`, `ret_off`, `residual`]
    strip_assume_tac) >>
  qexistsl_tac [`m+n`, `cas`] >> rpt conj_tac >> TRY decide_tac
  >- (irule asm_steps_compose_ok >> qexists_tac `ready` >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  simp[normal_frame_plan_def] >> metis_tac[]
QED

Theorem normal_frame_call_step:
  normal_frame_plan rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn callinst s oms om hs h) ast /\
  joint_config_reachable vs0 unit.cu_context
    (JointConfig stk PG G tn fn callinst s oms om hs h) /\
  active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
  callinst.inst_operands = Label nm :: arg_ops /\
  lookup_function nm unit.cu_context.ctx_functions = SOME callee /\
  eval_operands arg_ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\
  f.cf_fn = fn /\ f.cf_inst = callinst /\ f.cf_state = s ==>
  ?n ast1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    normal_frame_plan rpolicy unit cpl prog vs0 es0
      (JointConfig (f::stk) PG' G' tn' callee inst' s1 oms' om' hs' h') ast1
Proof
  metis_tac[normal_frame_call_progress]
QED

Theorem normal_frame_fn_shape:
  normal_frame_plan rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast ==>
  codegen_ready_fn fn /\ ALL_DISTINCT (fn_labels fn)
Proof
  strip_tac >>
  qpat_x_assum `normal_frame_plan _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [normal_frame_plan_def])
  >- (fs[active_frame_plan_def] >> drule body_plan_inv_facts >>
      simp[codegen_ready_fn_def, venomWfTheory.wf_function_def]) >>
  fs[entry_frame_plan_def] >>
  `codegen_ready_fn fn` by metis_tac[body_fn_shape] >>
  fs[codegen_ready_fn_def, venomWfTheory.wf_function_def]
QED

Theorem normal_frame_joint_step:
  joint_config_reachable vs0 unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  normal_frame_plan rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast /\
  ~in_revert_forward fn s /\
  (inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode ==>
    source_memory_reads_disjoint cpl inst s /\
    context_source_memory_writes_disjoint cpl inst s) /\
  joint_transition unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h) ev q' ==>
  ?n ast1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    normal_frame_plan rpolicy unit cpl prog vs0 es0 q' ast1
Proof
  strip_tac >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[Once joint_transition_cases] >> rpt strip_tac >> gvs[]
  >- (drule_all normal_frame_next_step >> simp[])
  >- (drule_all normal_frame_jump_step >> metis_tac[])
  >- (fs[decode_invoke_def, AllCaseEqs()] >>
      irule normal_frame_call_step >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >> metis_tac[])
  >> drule_all normal_frame_return_step >> metis_tac[]
QED

(* Every non-RF actual edge advances assembly or decreases the remaining
   ordinary instruction rank in the same source activation and block. *)
Theorem normal_frame_joint_progress:
  joint_config_reachable vs0 unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  normal_frame_plan rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast /\
  ~in_revert_forward fn s /\
  (inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode ==>
    source_memory_reads_disjoint cpl inst s /\
    context_source_memory_writes_disjoint cpl inst s) /\
  joint_transition unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h) ev
    (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ==>
  ?n ast1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    normal_frame_plan rpolicy unit cpl prog vs0 es0
      (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ast1 /\
    (0 < n \/
     (n = 0 /\ inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
      stk' = stk /\ fn' = fn /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = SUC s.vs_inst_idx /\
      ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        LENGTH bb.bb_instructions - t.vs_inst_idx <
          LENGTH bb.bb_instructions - s.vs_inst_idx))
Proof
  strip_tac >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[Once joint_transition_cases] >> rpt strip_tac >> gvs[]
  >- (drule_all normal_frame_fn_shape >> strip_tac >>
      mp_tac (Q.INST
        [`post` |-> `s'`, `PG'` |-> `PG`, `G'` |-> `step_prov PG G inst s'`,
         `tn'` |-> `step_taint inst s s' tn`, `oms'` |-> `oms`,
         `om'` |-> `origin_step PG om inst s'`, `hs'` |-> `hs`,
         `h'` |-> `h ++ [OriginOrdinary fuel s'; OriginObserve
           (OriginSnapshot fn PG (step_prov PG G inst s')
             (origin_step PG om inst s') inst'
             (s' with vs_inst_idx := SUC s.vs_inst_idx))]`]
        (SPEC_ALL normal_frame_next_step)) >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
      disch_then (qx_choosel_then [`n`, `ast1`] strip_assume_tac) >>
      `s'.vs_current_bb = s.vs_current_bb` by
        metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
      qpat_assum `active_inst fn inst s`
        (qx_choose_then `bb` strip_assume_tac o REWRITE_RULE [active_inst_def]) >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
        (irule venomExecPropsTheory.MEM_lookup_block >> fs[fn_labels_def]) >>
      qexistsl_tac [`n`, `ast1`] >> rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      Cases_on `n = 0` >> simp[] >> qexists_tac `bb` >> simp[] >> decide_tac)
  >- (drule_all normal_frame_jump_step >> metis_tac[])
  >- (fs[decode_invoke_def, AllCaseEqs()] >>
      `?n ast1.
        0 < n /\
        asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
          prog n ast = AsmOK ast1 /\
        normal_frame_plan rpolicy unit cpl prog vs0 es0
          (JointConfig
            (<| cf_fn := fn; cf_inst := inst; cf_state := s;
                cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
            (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) fn' inst' t
            (om::oms) FEMPTY (h::hs)
            [OriginCallee cs; OriginObserve
              (OriginSnapshot fn' (MAP (op_prov G) ops) FEMPTY FEMPTY inst' t)]) ast1` by
        (irule normal_frame_call_progress >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >> metis_tac[]) >>
      metis_tac[]) >>
  drule_all normal_frame_return_step >> metis_tac[]
QED

(* Only the local range obligations at earlier occurrences are requested.
   Their source-cut producer is supplied by the joint pass simulation. *)
Theorem normal_frame_trace_prefix:
  !j.
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
  initial_ctx_rel_tail tail cpl prog unit.cu_context vs0 es0 /\
  joint_trace vs0 unit.cu_context q0 es qs
    (JointConfig laststk lastPG lastG lasttn lastfn lastinst laststate
      lastoms lastom lasths lasth) /\
  active_inst lastfn lastinst laststate /\ lastinst.inst_opcode = GAS /\
  (!k stk PG G tn fn inst s oms om hs h.
    k < LENGTH es /\
    EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
    inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    ~in_revert_forward fn s ==>
    source_memory_reads_disjoint cpl inst s /\
    context_source_memory_writes_disjoint cpl inst s) /\
  j <= LENGTH es ==>
  ?n ast.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n (entry_asm_state vs0 es0) = AsmOK ast /\
    normal_frame_plan rpolicy unit cpl prog vs0 es0 (EL j (q0::qs)) ast
Proof
  Induct >> rpt strip_tac
  >- (qexistsl_tac [`0`, `entry_asm_state vs0 es0`] >>
      simp[asm_steps_def] >> irule normal_frame_initial >>
      metis_tac[joint_trace_def]) >>
  `j < LENGTH es /\ j <= LENGTH es` by decide_tac >>
  `?n ast.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n (entry_asm_state vs0 es0) = AsmOK ast /\
    normal_frame_plan rpolicy unit cpl prog vs0 es0 (EL j (q0::qs)) ast` by
    (first_x_assum irule >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  `?stk PG G tn fn inst s oms om hs h.
    EL j (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h` by
    (Cases_on `EL j (q0::qs)` >> metis_tac[]) >>
  `normal_frame_plan rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast` by metis_tac[] >>
  drule normal_frame_fn_shape >> strip_tac >>
  `~in_revert_forward fn s` by
    (irule joint_trace_gas_nonrevert >> metis_tac[]) >>
  `joint_config_reachable vs0 unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
   joint_transition unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h)
    (EL j es) (EL (SUC j) (q0::qs))` by
    (drule joint_trace_edge_at >> disch_then (qspec_then `j` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode ==>
    source_memory_reads_disjoint cpl inst s /\
    context_source_memory_writes_disjoint cpl inst s` by metis_tac[] >>
  drule_all normal_frame_joint_step >>
  disch_then (qx_choosel_then [`m`, `next`] strip_assume_tac) >>
  qexistsl_tac [`n+m`, `next`] >> conj_tac
  >- (irule asm_steps_compose_ok >> qexists_tac `ast` >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Theorem codegen_joint_gas_prefix_count_bound:
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
  initial_ctx_rel_tail tail cpl prog unit.cu_context vs0 es0 /\
  joint_trace vs0 unit.cu_context q0 es qs
    (JointConfig laststk lastPG lastG lasttn lastfn lastinst laststate
      lastoms lastom lasths lasth) /\
  active_inst lastfn lastinst laststate /\ lastinst.inst_opcode = GAS /\
  (!k stk PG G tn fn inst s oms om hs h.
    k < LENGTH es /\
    EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
    inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    ~in_revert_forward fn s ==>
    source_memory_reads_disjoint cpl inst s /\
    context_source_memory_writes_disjoint cpl inst s) /\
  run_call es0 = SOME (result,final) /\
  ~frame_resource_starved es0 result final /\
  laststate.vs_gas_readings = DROP (k-1) vs0.vs_gas_readings /\ 0 < k ==>
  k <= LENGTH (gas_readings es0)
Proof
  strip_tac >>
  drule_all codegen_assembly_frame_prog_ok >> strip_tac >>
  `assemble prog <> []` by metis_tac[codegen_assembly_nonempty] >>
  Q.SUBGOAL_THEN `vs0.vs_call_ctx.cc_created_in_tx \/ account_already_created
    (lookup_account (FST (HD es0.contexts)).msgParams.callee
      es0.rollback.accounts)` assume_tac
  >- (gvs[initial_ctx_rel_tail_def] >> metis_tac[]) >>
  drule_all asm_frame_rel_entry >> strip_tac >>
  mp_tac (Q.INST [`j` |-> `LENGTH es`] (SPEC_ALL normal_frame_trace_prefix)) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  disch_then (qx_choosel_then [`n`, `ast`] strip_assume_tac) >>
  drule joint_trace_endpoint >> strip_tac >> gvs[] >>
  drule_all normal_frame_gas_count_bound >> simp[]
QED
