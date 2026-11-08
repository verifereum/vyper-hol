Theory concretizeAnalysisCallProjection
Ancestors venomWfProps frameOpenCall concretizeAnalysisOwnership concretizeAnalysisMetadataOwnership
  frameHistoryCfg o1PassContract removeUnusedSsaProofs relation list arithmetic
  venomExecSemantics ptrDiscipline venomInst venomWf frameJointTransition frameActivationCache
  contextCodegenRel venomExecProps frameJointTrace frameOriginHistory

Theorem active_invoke_source_call:
  MEM caller C.ctx_functions /\ active_inst caller invoke s /\
  invoke.inst_opcode = INVOKE /\ decode_invoke invoke = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME callee ==>
  invoke.inst_operands = Label name :: ops /\ source_call C caller callee
Proof
  strip_tac >>
  `invoke.inst_operands = Label name :: ops` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  `MEM invoke (fn_insts caller)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  `callee.fn_name = name` by
    (qpat_x_assum `lookup_function _ _ = _` mp_tac >>
     simp[lookup_function_def] >> strip_tac >> drule FIND_P >> simp[]) >>
  simp[source_call_def] >> conj_tac >- metis_tac[lookup_function_MEM] >>
  simp[invoke_target_instruction] >> metis_tac[]
QED

(* The saved portion stops strictly above the selected call's caller.
   In particular, a return never asks for a reverse call edge. *)
Definition call_path_stack_def:
  call_path_stack C root d stk fn <=>
    MEM fn C.ctx_functions /\ RTC (source_call C) root fn /\
    EVERY (\f. MEM f.cf_fn C.ctx_functions /\ RTC (source_call C) root f.cf_fn)
      (TAKE (LENGTH stk - SUC d) stk)
End

Definition joint_call_path_def:
  joint_call_path C root d (JointConfig stk PG G tn fn inst s oms om hs h) <=>
    call_path_stack C root d stk fn
End

Theorem joint_call_path_step:
  joint_transition C p ev q /\ joint_call_path C root d p /\
  d < activation_depth p /\ d < activation_depth q ==>
  joint_call_path C root d q
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >>
  gvs[joint_call_path_def, call_path_stack_def, activation_depth_def]
  >- suspend "push"
  >> suspend "pop"
QED

Resume joint_call_path_step[push]:
  drule_all active_invoke_source_call >> strip_tac >>
  `RTC (source_call C) root callee` by metis_tac[RTC_CASES2] >>
  simp[GSYM ADD1] >> metis_tac[lookup_function_MEM]
QED

Resume joint_call_path_step[pop]:
  `LENGTH stk - d = SUC (LENGTH stk - SUC d)` by decide_tac >> gvs[GSYM ADD1]
QED

Finalise joint_call_path_step

Theorem joint_call_path_interval:
  !j n. joint_trace vs0 C q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  joint_call_path C root d (EL n (q0::qs)) /\
  (!k. n <= k /\ k <= j ==> d < activation_depth (EL k (q0::qs))) ==>
  joint_call_path C root d (EL j (q0::qs))
Proof
  Induct_on `j` >- (rpt strip_tac >> `n = 0` by decide_tac >> gvs[]) >>
  rpt strip_tac >> Cases_on `n = SUC j` >- gvs[] >>
  `n <= j /\ j < LENGTH es` by decide_tac >>
  `joint_call_path C root d (EL j (q0::qs))` by
    (first_x_assum irule >> goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     simp[] >> qexists_tac `n` >> simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `joint_transition C (EL j (q0::qs)) (EL j es) (EL (SUC j) (q0::qs))` by
    metis_tac[joint_trace_edge_at] >>
  `d < activation_depth (EL j (q0::qs)) /\
   d < activation_depth (EL (SUC j) (q0::qs))` by
    (conj_tac >> first_x_assum irule >> decide_tac) >>
  metis_tac[joint_call_path_step]
QED

Theorem joint_reachable_function_member[local]:
  joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h) /\
  o1_ctx_shape C ==> MEM fn C.ctx_functions
Proof
  simp[joint_config_reachable_def] >> strip_tac >>
  drule joint_origin_history_projection >> strip_tac >>
  drule frame_history_cfg_invariant >>
  gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]
QED

Theorem joint_open_call_path_at:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ c < j /\ j <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 /\
  joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
  EL j (q0::qs) = JointConfig stk PG G tn owner inst s oms om hs h /\
  (!k. c < k /\ k <= j ==> LENGTH stk0 < activation_depth (EL k (q0::qs))) ==>
  ?root name ops.
    invoke.inst_opcode = INVOKE /\ invoke.inst_operands = Label name :: ops /\
    lookup_function name C.ctx_functions = SOME root /\
    source_call C caller root /\ RTC (source_call C) root owner
Proof
  strip_tac >>
  `c < LENGTH es /\ SUC c <= j` by decide_tac >>
  `joint_config_reachable vs0 C (EL c (q0::qs))` by
    metis_tac[joint_trace_edge_at] >>
  `MEM caller C.ctx_functions` by
    (qpat_x_assum `joint_config_reachable _ _ _` mp_tac >> simp[] >>
     metis_tac[joint_reachable_function_member]) >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_call_iff] >> strip_tac >>
  `invoke.inst_operands = Label nm :: ops /\ source_call C caller callee` by
    metis_tac[active_invoke_source_call] >>
  `joint_call_path C callee (LENGTH stk0) (EL (SUC c) (q0::qs))` by
    (simp[joint_call_path_def, call_path_stack_def, RTC_REFL] >>
     metis_tac[lookup_function_MEM]) >>
  `joint_call_path C callee (LENGTH stk0) (EL j (q0::qs))` by
    (irule joint_call_path_interval >> conj_tac
     >- (qexists_tac `SUC c` >> simp[] >> rpt strip_tac >>
         first_x_assum irule >> decide_tac) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >> simp[]) >>
  gvs[joint_call_path_def, call_path_stack_def] >> metis_tac[]
QED

Theorem joint_open_call_path:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ n <= j /\ j <= LENGTH es /\
  activation_depth (EL n (q0::qs)) = d /\
  d < activation_depth (EL j (q0::qs)) /\
  (!k. n <= k /\ k <= j ==> d <= activation_depth (EL k (q0::qs))) /\
  EL j (q0::qs) = JointConfig stk PG G tn current inst s oms om hs h ==>
  ?c stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 root name ops.
    n <= c /\ c < j /\ LENGTH stk0 = d /\ EL c es = NONE /\
    EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 /\
    joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
    (!k. c < k /\ k <= j ==> d < activation_depth (EL k (q0::qs))) /\
    (EL (LENGTH stk - SUC d) stk).cf_fn = caller /\
    (EL (LENGTH stk - SUC d) stk).cf_inst = invoke /\
    (EL (LENGTH stk - SUC d) stk).cf_state = s0 /\
    invoke.inst_opcode = INVOKE /\ invoke.inst_operands = Label name :: ops /\
    lookup_function name C.ctx_functions = SOME root /\
    source_call C caller root /\ RTC (source_call C) root current
Proof
  strip_tac >> drule_all joint_open_call_saved >> strip_tac >>
  `?root name ops.
    invoke.inst_opcode = INVOKE /\ invoke.inst_operands = Label name :: ops /\
    lookup_function name C.ctx_functions = SOME root /\
    source_call C owner root /\ RTC (source_call C) root current` by
    (irule joint_open_call_path_at >> simp[] >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >>
     gvs[]) >>
  qexists_tac `c` >>
  goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >>
  gvs[] >> metis_tac[]
QED
