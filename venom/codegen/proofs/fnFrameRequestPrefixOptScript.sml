(* The request step of a compiled frame through an accepted finalizer: the
   finalized program issues the step's request at the same index of the
   frame's recorded calls, paired with the step's first outcome.

   TOP-LEVEL: codegen_request_step_alignment_opt.
   Helper: asm_step_oracle, asm_steps_single_request,
   sym_step_call_request_cong, normal_frame_symbolic_plan_oracle,
   asm_sym_call_window, codegen_request_source_window,
   accepted_finalizer_call_window.
 *)
Theory fnFrameRequestPrefixOpt
Ancestors
  fnFrameRequestPrefix fnFrameSymbolicPrefix asmFinalizerPrefix
  asmFinalizerPrefixStatic asmFrameLocalStep asmFrameRel codegenSymRel
  asmSymBridge asmSymPc asmSplice asmDataEnv codegenAsmStaticWf
  jointRequestCut frameJointTrace frameJointTransition frameRawProjection
  dftGasFromListLookup fnBlockBodySteps frameRel codegenRel
  contextCodegenRel codegenEntrySim codegenEntryRel fnFramePrefixEntry
  stackPlanGen callTrace asmSymSem asmSem extCallOracle evmStepSim
  venomInst venomWf list rich_list arithmetic

(* ===== One asm step against the call oracle ===== *)

Theorem asm_consume_outcome_tl[local]:
  (asm_consume_call_outcome rq ro rs stk s = AsmOK s1 ==>
   s.as_outcomes <> [] /\ s1.as_outcomes = TL s.as_outcomes) /\
  (asm_consume_create_outcome rq stk s = AsmOK s1 ==>
   s.as_outcomes <> [] /\ s1.as_outcomes = TL s.as_outcomes)
Proof
  `SND (take_outcome rq s.as_outcomes) = TL s.as_outcomes` by
    (Cases_on `s.as_outcomes` >> simp[take_outcome_rest]) >>
  rw[asm_consume_call_outcome_def, asm_consume_create_outcome_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[asm_next_def]
QED

(* A successful step keeps the call oracle, or is a call-family opcode
   that consumes one outcome. *)
Theorem asm_step_oracle:
  asm_step lo o2pc inst a = AsmOK a1 ==>
  (a1.as_requests = a.as_requests /\ a1.as_outcomes = a.as_outcomes) \/
  (?op. inst = AsmOp op /\
     MEM op ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"] /\
     a.as_outcomes <> [] /\ a1.as_outcomes = TL a.as_outcomes)
Proof
  strip_tac >>
  Cases_on `?op. inst = AsmOp op /\ (is_evm_call_name op \/ op = "GAS")`
  >- (pop_assum (strip_assume_tac o REWRITE_RULE [is_evm_call_name_def]) >>
      gvs[asm_step_def, asm_step_op_def, asm_step_arith_def,
          asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
          asm_step_control_def, asm_step_extcall_def, asm_step_copy_def,
          asm_step_context_def] >>
      gvs[asm_exec_call_def, asm_exec_staticcall_def,
          asm_exec_delegatecall_def, asm_exec_create_def,
          asm_exec_create2_def, asm_selfdestruct_def, asm_gas_def,
          asm_push_val_def, asm_next_def, AllCaseEqs()] >>
      imp_res_tac asm_consume_outcome_tl >> gvs[]) >>
  disj1_tac >>
  mp_tac (Q.INST [`labels` |-> `lo`, `pc` |-> `o2pc`]
            frame_asm_step_observers) >>
  impl_tac >- (simp[] >> rpt strip_tac >> gvs[is_evm_call_name_def]) >>
  simp[]
QED

Theorem asm_steps_oracle_suffix[local]:
  !m a b. asm_steps lo o2pc p m a = AsmOK b ==>
    (b.as_requests = a.as_requests /\ b.as_outcomes = a.as_outcomes) \/
    (a.as_outcomes <> [] /\ LENGTH b.as_outcomes < LENGTH a.as_outcomes)
Proof
  Induct >> simp[asm_steps_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `asm_step lo o2pc (EL a.as_pc p) a` >> simp[] >>
  rename1 `asm_step _ _ _ a = AsmOK a0` >> strip_tac >>
  first_x_assum drule >> drule asm_step_oracle >> rpt strip_tac >> gvs[] >>
  Cases_on `a.as_outcomes` >> gvs[]
QED

(* A run that records new requests while consuming a single outcome does so
   at exactly one call-family step, with the oracle untouched before it. *)
Theorem asm_steps_single_request:
  !m a b. asm_steps lo o2pc p m a = AsmOK b /\
    b.as_requests <> a.as_requests /\ b.as_outcomes = TL a.as_outcomes ==>
    ?k c c' op. k < m /\ asm_steps lo o2pc p k a = AsmOK c /\
      c.as_requests = a.as_requests /\ c.as_outcomes = a.as_outcomes /\
      c.as_pc < LENGTH p /\ EL c.as_pc p = AsmOp op /\
      MEM op ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"] /\
      a.as_outcomes <> [] /\
      asm_step lo o2pc (EL c.as_pc p) c = AsmOK c' /\
      c'.as_requests = b.as_requests /\ c'.as_outcomes = TL c.as_outcomes
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (`b = a` by fs[asm_steps_def] >> pop_assum SUBST_ALL_TAC >>
      qpat_x_assum `_ <> _` mp_tac >> rewrite_tac[]) >>
  qpat_x_assum `asm_steps _ _ _ (SUC _) _ = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [asm_steps_def, AllCaseEqs()]) >>
  rename1 `asm_step _ _ _ a = AsmOK a0` >>
  drule asm_step_oracle >> strip_tac
  >- (first_x_assum (qspecl_then [`a0`, `b`] mp_tac) >>
      (impl_tac >- fs[]) >>
      disch_then (qx_choosel_then [`k`, `c`, `c'`, `op`] strip_assume_tac) >>
      qexistsl_tac [`SUC k`, `c`, `c'`, `op`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (fs[asm_steps_def] >> NO_TAC) >> metis_tac[]) >>
  qpat_x_assum `!a b. _` kall_tac >>
  `b.as_requests = a0.as_requests` by
    (qpat_x_assum `asm_steps _ _ _ m a0 = _`
       (strip_assume_tac o MATCH_MP asm_steps_oracle_suffix) >> rfs[]) >>
  qexistsl_tac [`0`, `a`, `a0`, `op`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[asm_steps_def]
QED

(* ===== The call step on the finalized program ===== *)

Theorem opt_mmap_map_eq[local]:
  !l1 l2. MAP f l1 = MAP f l2 ==> OPT_MMAP f l1 = OPT_MMAP f l2
Proof
  Induct >> Cases_on `l2` >> rw[OPT_MMAP_def] >> res_tac >> simp[]
QED

Theorem sym_step_call_concrete[local]:
  MEM op ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"] ==>
  sym_step p env (AsmOp op) ss = sym_step_concrete op ss
Proof
  rw[] >> simp[sym_step_def, sym_step_op_def, dup_table_def, swap_table_def]
QED

Theorem asm_step_op_pc_zero[local]:
  asm_step_op FEMPTY name y =
  asm_result_pc_add y.as_pc (asm_step_op FEMPTY name (y with as_pc := 0))
Proof
  qspecl_then [`name`, `y with as_pc := 0`, `y.as_pc`] mp_tac
    asm_step_op_pc_add >>
  `(y with as_pc := 0) with as_pc := (y with as_pc := 0).as_pc + y.as_pc = y`
    by simp[asm_state_component_equality] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  disch_then ACCEPT_TAC
QED

Theorem sym_step_concrete_request_cong[local]:
  !op a a' b.
  sym_step_concrete op a = SymOK a' /\
  (b.sym_base with as_pc := 0) = (a.sym_base with as_pc := 0) /\
  MAP sval_val b.sym_stack = MAP sval_val a.sym_stack /\
  FDOM b.sym_mem_labels = FDOM a.sym_mem_labels ==>
  ?b'. sym_step_concrete op b = SymOK b' /\
    b'.sym_base.as_requests = a'.sym_base.as_requests /\
    b'.sym_base.as_outcomes = a'.sym_base.as_outcomes
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH b.sym_stack = LENGTH a.sym_stack` by metis_tac[LENGTH_MAP] >>
  `OPT_MMAP sval_val (TAKE (asm_op_arity op) b.sym_stack) =
   OPT_MMAP sval_val (TAKE (asm_op_arity op) a.sym_stack)` by
    (irule opt_mmap_map_eq >> simp[MAP_TAKE]) >>
  `mem_labels_hit b.sym_mem_labels = mem_labels_hit a.sym_mem_labels` by
    simp[FUN_EQ_THM, mem_labels_hit_def] >>
  qpat_x_assum `sym_step_concrete _ a = _` mp_tac >>
  rewrite_tac[sym_step_concrete_def] >> BETA_TAC >>
  rewrite_tac[LET_THM] >> BETA_TAC >> asm_rewrite_tac[] >>
  Cases_on `LENGTH a.sym_stack < asm_op_arity op` >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >>
  Cases_on `OPT_MMAP sval_val (TAKE (asm_op_arity op) a.sym_stack)` >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >>
  rename1 `OPT_MMAP _ _ = SOME args` >>
  Cases_on `mem_labels_hit a.sym_mem_labels (asm_op_mem_reads op args)` >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >>
  `(b.sym_base with as_stack := args) with as_pc := 0 =
   (a.sym_base with as_stack := args) with as_pc := 0` by
    fs[asm_state_component_equality] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV asm_step_op_pc_zero)) >>
  pop_assum (fn th => rewrite_tac[th]) >>
  Cases_on `asm_step_op FEMPTY op ((a.sym_base with as_stack := args) with
                                   as_pc := 0)` >>
  simp[asm_result_pc_add_def, sym_lift_def] >> rpt strip_tac >> gvs[]
QED

(* A call-family step depends on the state only up to its program counter,
   the values on its stack and which memory bytes hold labels. *)
Theorem sym_step_call_request_cong:
  MEM op ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"] /\
  sym_step p env (AsmOp op) a = SymOK a' /\
  (b.sym_base with as_pc := 0) = (a.sym_base with as_pc := 0) /\
  MAP sval_val b.sym_stack = MAP sval_val a.sym_stack /\
  FDOM b.sym_mem_labels = FDOM a.sym_mem_labels ==>
  !q env'. ?b'. sym_step q env' (AsmOp op) b = SymOK b' /\
    b'.sym_base.as_requests = a'.sym_base.as_requests /\
    b'.sym_base.as_outcomes = a'.sym_base.as_outcomes
Proof
  strip_tac >> rpt gen_tac >>
  `sym_step_concrete op a = SymOK a'` by metis_tac[sym_step_call_concrete] >>
  `sym_step q env' (AsmOp op) b = sym_step_concrete op b` by
    metis_tac[sym_step_call_concrete] >>
  pop_assum SUBST1_TAC >>
  qspecl_then [`op`, `a`, `a'`, `b`] mp_tac sym_step_concrete_request_cong >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

(* ===== Oracle fields of a symbolic plan ===== *)

Theorem normal_frame_symbolic_plan_oracle:
  normal_frame_symbolic_plan env rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast ss ==>
  ast.as_requests = s.vs_requests /\ ast.as_outcomes = s.vs_outcomes
Proof
  rw[normal_frame_symbolic_plan_def] >>
  gvs[active_frame_symbolic_plan_def, entry_frame_symbolic_plan_def,
      entry_frame_plan_def, body_plan_inv_def, fn_frame_inv_def,
      context_venom_asm_rel_def, frame_view_def, fn_entry_state_rel_def,
      shared_state_rel_def, venom_asm_terminal_rel_def,
      entry_bind_pairs_oracle]
QED

Theorem normal_frame_symbolic_plan_sym_rel[local]:
  normal_frame_symbolic_plan env rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast ss ==>
  asm_sym_rel prog env ast ss
Proof
  rw[normal_frame_symbolic_plan_def] >>
  gvs[active_frame_symbolic_plan_def, entry_frame_symbolic_plan_def,
      sym_frame_inv_def]
QED

(* ===== The call step inside a symbolic run ===== *)

Theorem asm_sym_rel_oracle[local]:
  asm_sym_rel p env cs ss ==>
  ss.sym_base.as_requests = cs.as_requests /\
  ss.sym_base.as_outcomes = cs.as_outcomes /\
  ss.sym_base.as_pc = cs.as_pc
Proof
  rw[asm_sym_rel_def] >> simp[]
QED

Theorem sym_steps_split[local]:
  !k m sa sb. sym_steps p env m sa = SymOK sb /\ k <= m ==>
    ?sk. sym_steps p env k sa = SymOK sk /\
         sym_steps p env (m - k) sk = SymOK sb
Proof
  rpt strip_tac >>
  qspecl_then [`k`, `m - k`, `sa`] mp_tac sym_steps_add >>
  `k + (m - k) = m` by decide_tac >>
  pop_assum (fn th => rewrite_tac[th]) >>
  Cases_on `sym_steps p env k sa` >> gvs[]
QED

(* A related run that records new requests while consuming one outcome
   passes a call-family instruction whose symbolic step does exactly that. *)
Theorem asm_sym_call_window:
  !m a sa b sb.
  asm_static_wf p /\ asm_sym_rel p env a sa /\
  asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p m a =
    AsmOK b /\
  sym_steps p env m sa = SymOK sb /\
  b.as_requests <> a.as_requests /\ b.as_outcomes = TL a.as_outcomes ==>
  ?k sk sk' op.
    sym_steps p env k sa = SymOK sk /\
    sk.sym_base.as_pc < LENGTH p /\ EL sk.sym_base.as_pc p = AsmOp op /\
    MEM op ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"] /\
    sym_step p env (AsmOp op) sk = SymOK sk' /\
    sk.sym_base.as_requests = a.as_requests /\
    sk.sym_base.as_outcomes = a.as_outcomes /\
    sk'.sym_base.as_requests = b.as_requests /\
    sk'.sym_base.as_outcomes = TL a.as_outcomes
Proof
  rpt strip_tac >>
  drule_all asm_steps_single_request >>
  disch_then (qx_choosel_then [`k`, `c`, `c'`, `op`] strip_assume_tac) >>
  qabbrev_tac `ops = ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]` >>
  `k <= m /\ 0 < m - k` by decide_tac >>
  qspecl_then [`k`, `m`, `sa`, `sb`] mp_tac sym_steps_split >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `sk` strip_assume_tac) >>
  `?c0. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
          k a = AsmOK c0 /\ asm_sym_rel p env c0 sk` by
    metis_tac[asm_sym_steps_lockstep] >>
  `c0 = c` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  drule asm_sym_rel_oracle >> strip_tac >>
  `?sk'. sym_step p env (AsmOp op) sk = SymOK sk'` by
    (qpat_x_assum `sym_steps p env (m - k) sk = _` mp_tac >>
     gvs[sym_steps_pos] >> Cases_on `sym_step p env (AsmOp op) sk` >>
     simp[]) >>
  `sym_steps p env 1 sk = SymOK sk'` by
    (rewrite_tac[ONE, sym_steps_def] >> gvs[]) >>
  `?c1. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
          1 c = AsmOK c1 /\ asm_sym_rel p env c1 sk'` by
    metis_tac[asm_sym_steps_lockstep] >>
  `c1 = c'` by
    (qpat_x_assum `asm_steps _ _ p 1 c = _` mp_tac >>
     rewrite_tac[ONE, asm_steps_def] >> gvs[]) >>
  pop_assum SUBST_ALL_TAC >>
  drule asm_sym_rel_oracle >> strip_tac >>
  qexistsl_tac [`k`, `sk`, `sk'`, `op`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[]
QED

(* ===== The request step of the compiled frame, symbolically ===== *)

Theorem codegen_request_step_runs[local]:
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  focus_s7_symbolic_context unit prog /\
  joint_trace vs0 unit.cu_context q0 es qs
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel unit.cu_context inst s = OK s' /\
  LENGTH s.vs_requests < LENGTH s'.vs_requests /\
  (!j stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1.
    j <= LENGTH es /\
    EL j (q0::qs) = JointConfig stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1 ==>
    ~in_revert_forward fn1 s1 /\ focus_s7_symbolic_guard prog cpl fn1 inst1 s1) ==>
  ?n ast ss m ast1 ss1.
    sym_steps prog (asm_data_env prog vs0.vs_code) n
      (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    asm_sym_rel prog (asm_data_env prog vs0.vs_code) ast ss /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog m ast = AsmOK ast1 /\
    sym_steps prog (asm_data_env prog vs0.vs_code) m ss = SymOK ss1 /\
    ast.as_requests = s.vs_requests /\ ast.as_outcomes = s.vs_outcomes /\
    ast1.as_requests = s'.vs_requests /\ ast1.as_outcomes = s'.vs_outcomes
Proof
  strip_tac >>
  `EL (LENGTH es) (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h` by
    metis_tac[joint_trace_endpoint] >>
  `?n ast ss.
     asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n (entry_asm_state vs0 es0) = AsmOK ast /\
     sym_steps prog (asm_data_env prog vs0.vs_code) n
       (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
     normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy unit
       cpl prog vs0 es0 (JointConfig stk PG G tn fn inst s oms om hs h) ast ss`
    by (qpat_x_assum `EL (LENGTH es) _ = _` (SUBST1_TAC o SYM) >>
        irule normal_frame_symbolic_trace_prefix >>
        first_assum (irule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >>
        rpt strip_tac >> metis_tac[LESS_IMP_LESS_OR_EQ]) >>
  drule normal_frame_symbolic_plan_oracle >> strip_tac >>
  drule normal_frame_symbolic_plan_sym_rel >> strip_tac >>
  `EVERY wf_function unit.cu_context.ctx_functions` by
    (qpat_x_assum `codegen_context_obligations _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[codegen_context_obligations_def, codegen_ready_def,
          codegen_ready_fn_def, EVERY_MEM]) >>
  `joint_config_reachable vs0 unit.cu_context
     (JointConfig stk PG G tn fn inst s oms om hs h)` by
    metis_tac[joint_trace_reachable] >>
  `wf_function fn` by metis_tac[joint_config_raw, raw_reachable_wf] >>
  drule_all step_inst_request_outcomes >> strip_tac >>
  `~is_terminator inst.inst_opcode` by
    (qpat_x_assum `MEM inst.inst_opcode _` mp_tac >>
     rpt (pop_assum kall_tac) >> rw[] >> simp[is_terminator_def]) >>
  drule_all active_inst_next_nonterminator >> strip_tac >>
  `~in_revert_forward fn s /\ focus_s7_symbolic_guard prog cpl fn inst s` by
    (qpat_x_assum `!j stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1. _`
       (qspecl_then [`LENGTH es`, `stk`, `PG`, `G`, `tn`, `fn`, `inst`, `s`,
                     `oms`, `om`, `hs`, `h`] mp_tac) >> simp[]) >>
  `joint_transition unit.cu_context
     (JointConfig stk PG G tn fn inst s oms om hs h)
     (SOME (OriginOrdinary fuel s'))
     (JointConfig stk PG (step_prov PG G inst s') (step_taint inst s s' tn)
       fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) oms
       (origin_step PG om inst s') hs
       (h ++ [OriginOrdinary fuel s'; OriginObserve
         (OriginSnapshot fn PG (step_prov PG G inst s')
           (origin_step PG om inst s') inst'
           (s' with vs_inst_idx := SUC s.vs_inst_idx))]))` by
    (simp[joint_transition_ordinary] >> metis_tac[]) >>
  `asm_data_env prog vs0.vs_code = asm_data_env prog vs0.vs_code` by simp[] >>
  drule_all normal_frame_symbolic_joint_progress >>
  disch_then (qx_choosel_then [`m`, `ast1`, `ss1`] strip_assume_tac) >>
  qpat_x_assum `normal_frame_symbolic_plan _ _ _ _ _ _ _ _ ast1 ss1`
    (mp_tac o MATCH_MP normal_frame_symbolic_plan_oracle) >>
  strip_tac >>
  qpat_x_assum `!j stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1. _` kall_tac >>
  qpat_x_assum `MEM inst.inst_opcode _` kall_tac >>
  qexistsl_tac [`n`, `ast`, `ss`, `m`, `ast1`, `ss1`] >> gvs[]
QED

Theorem codegen_request_source_window:
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  focus_s7_symbolic_context unit prog /\
  joint_trace vs0 unit.cu_context q0 es qs
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel unit.cu_context inst s = OK s' /\
  LENGTH s.vs_requests < LENGTH s'.vs_requests /\
  (!j stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1.
    j <= LENGTH es /\
    EL j (q0::qs) = JointConfig stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1 ==>
    ~in_revert_forward fn1 s1 /\ focus_s7_symbolic_guard prog cpl fn1 inst1 s1) ==>
  ?n sk sk' op.
    sym_steps prog (asm_data_env prog vs0.vs_code) n
      (sym_init (entry_asm_state vs0 es0)) = SymOK sk /\
    sk.sym_base.as_pc < LENGTH prog /\ EL sk.sym_base.as_pc prog = AsmOp op /\
    MEM op ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"] /\
    sym_step prog (asm_data_env prog vs0.vs_code) (AsmOp op) sk = SymOK sk' /\
    sk.sym_base.as_requests = s.vs_requests /\
    sk.sym_base.as_outcomes = s.vs_outcomes /\
    sk'.sym_base.as_requests = s'.vs_requests /\
    sk'.sym_base.as_outcomes = s'.vs_outcomes
Proof
  strip_tac >>
  drule_all codegen_request_step_runs >>
  disch_then (qx_choosel_then [`n`, `ast`, `ss`, `m`, `ast1`, `ss1`]
    strip_assume_tac) >>
  qpat_x_assum `!j stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1. _` kall_tac >>
  drule_all step_inst_request_outcomes >> strip_tac >>
  qpat_x_assum `MEM inst.inst_opcode _` kall_tac >>
  `asm_static_wf prog` by fs[focus_s7_symbolic_context_def] >>
  `ast1.as_requests <> ast.as_requests` by
    (strip_tac >> gvs[]) >>
  `ast1.as_outcomes = TL ast.as_outcomes` by gvs[] >>
  qspecl_then [`m`, `ast`, `ss`, `ast1`, `ss1`] mp_tac
    (Q.INST [`p` |-> `prog`, `env` |-> `asm_data_env prog vs0.vs_code`]
       asm_sym_call_window) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`k`, `sk`, `sk'`, `op`] strip_assume_tac) >>
  qexistsl_tac [`n + k`, `sk`, `sk'`, `op`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- metis_tac[sym_steps_compose] >>
  qpat_x_assum `MEM op _` kall_tac >> gvs[]
QED

(* ===== The request step on the finalized program ===== *)

(* A symbolic run of the compiled program that reaches a call-family step
   is matched by a run of the finalized program from the same entry state,
   reaching the same request and outcome state before and after the call. *)
Theorem accepted_finalizer_call_window:
  !fin rp prog prog' E data env n sk sk' op.
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  asm_static_wf prog /\ E.as_pc = 0 /\
  env = asm_data_env prog (assemble prog ++ data) /\
  MEM op ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"] /\
  sym_steps prog env n (sym_init E) = SymOK sk /\
  sk.sym_base.as_pc < LENGTH prog /\ EL sk.sym_base.as_pc prog = AsmOp op /\
  sym_step prog env (AsmOp op) sk = SymOK sk' ==>
  ?m cb cb'.
    asm_steps (SND (compute_label_offsets prog')) (build_offset_to_pc prog')
      prog' m (E with as_code := assemble prog' ++ data) = AsmOK cb /\
    asm_steps (SND (compute_label_offsets prog')) (build_offset_to_pc prog')
      prog' (m + 1) (E with as_code := assemble prog' ++ data) = AsmOK cb' /\
    cb.as_requests = sk.sym_base.as_requests /\
    cb.as_outcomes = sk.sym_base.as_outcomes /\
    cb'.as_requests = sk'.sym_base.as_requests /\
    cb'.as_outcomes = sk'.sym_base.as_outcomes
Proof
  rpt strip_tac >>
  qspecl_then [`fin`, `rp`, `prog`, `prog'`, `data`] mp_tac
    finalizer_prefix_static >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qspecl_then [`fin`, `rp`, `prog`, `prog'`] mp_tac
    accepted_finalizers_prefix_transport >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `kk` strip_assume_tac) >>
  qpat_x_assum `!env s n a. _` (qspecl_then [`env`, `E`, `n`, `sk`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspec_then `op` mp_tac o CONJUNCT2) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                qpat_x_assum `MEM op _` mp_tac >> rw[])) >>
  disch_then (qx_choosel_then [`m`, `b`] strip_assume_tac) >>
  drule_all_then (qspecl_then [`prog'`, `env`] strip_assume_tac)
    sym_step_call_request_cong >>
  qpat_x_assum `MEM op _` kall_tac >>
  `b.sym_base.as_requests = sk.sym_base.as_requests /\
   b.sym_base.as_outcomes = sk.sym_base.as_outcomes` by
    (qpat_x_assum `(b.sym_base with as_pc := 0) = _` mp_tac >>
     simp[asm_state_component_equality]) >>
  `sym_steps prog' env (m + 1) (sym_init E) = SymOK b'` by
    (irule sym_steps_compose >> qexists_tac `b` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rewrite_tac[ONE, sym_steps_def] >> gvs[]) >>
  qabbrev_tac `E' = E with as_code := assemble prog' ++ data` >>
  `sym_init E' = sym_init E` by simp[Abbr `E'`, sym_init_def] >>
  `asm_sym_rel prog' env E' (sym_init E')` by
    (irule asm_sym_rel_init >> simp[Abbr `E'`] >>
     metis_tac[asm_data_env_ok_asm_data_env]) >>
  `?cb. asm_steps (SND (compute_label_offsets prog'))
          (build_offset_to_pc prog') prog' m E' = AsmOK cb /\
        asm_sym_rel prog' env cb b` by
    metis_tac[asm_sym_steps_lockstep] >>
  `?cb'. asm_steps (SND (compute_label_offsets prog'))
           (build_offset_to_pc prog') prog' (m + 1) E' = AsmOK cb' /\
         asm_sym_rel prog' env cb' b'` by
    metis_tac[asm_sym_steps_lockstep] >>
  imp_res_tac asm_sym_rel_oracle >>
  qexistsl_tac [`m`, `cb`, `cb'`] >> gvs[]
QED

(* TOP-LEVEL: through an accepted finalizer, a lowered request step is the
   frame's next recorded call, answered in the call trace by the head of
   the step's outcomes. *)
Theorem codegen_request_step_alignment_opt:
  !fin rpolicy unit cpl prog prog' vs0 q0 es qs es0 s s' result final.
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
  label_flow_ok unit.cu_context /\ sym_unit_static_ok unit /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  asm_frame_rel prog' vs0.vs_data_section es0
    (entry_asm_state vs0 es0 with
       as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
  joint_trace vs0 unit.cu_context q0 es qs
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel unit.cu_context inst s = OK s' /\
  LENGTH s.vs_requests < LENGTH s'.vs_requests /\
  (!j stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1.
    j <= LENGTH es /\
    EL j (q0::qs) = JointConfig stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1 ==>
    ~in_revert_forward fn1 s1 /\ focus_s7_symbolic_guard prog cpl fn1 inst1 s1) /\
  run_call es0 = SOME (result,final) /\
  ~frame_resource_starved es0 result final ==>
  LENGTH s.vs_requests < LENGTH (call_requests es0) /\
  EL (LENGTH s.vs_requests) (call_requests es0) =
    EL (LENGTH s.vs_requests) s'.vs_requests /\
  s.vs_outcomes <> [] /\
  MEM (EL (LENGTH s.vs_requests) (call_requests es0), HD s.vs_outcomes)
    (call_trace es0)
Proof
  rpt gen_tac >> strip_tac >>
  `asm_static_wf prog` by
    metis_tac[codegen_context_obligations_def, codegen_asm_static_wf] >>
  `focus_s7_symbolic_context unit prog` by
    (rewrite_tac[focus_s7_symbolic_context_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all codegen_request_source_window >>
  disch_then (qx_choosel_then [`n`, `sk`, `sk'`, `op`] strip_assume_tac) >>
  qpat_x_assum `!j stk1 PG1 G1 tn1 fn1 inst1 s1 oms1 om1 hs1 h1. _` kall_tac >>
  drule_all step_inst_request_outcomes >> strip_tac >>
  qspecl_then [`fin`, `rpolicy`, `prog`, `prog'`, `entry_asm_state vs0 es0`,
    `vs0.vs_data_section`, `asm_data_env prog vs0.vs_code`, `n`, `sk`, `sk'`,
    `op`] mp_tac accepted_finalizer_call_window >>
  (impl_tac
   >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
       >- simp[entry_asm_state_def] >>
       qpat_assum `vs0.vs_code = _` (fn th => rewrite_tac[th]))) >>
  disch_then (qx_choosel_then [`mb`, `cb`, `cb'`] strip_assume_tac) >>
  `asm_frame_prog_ok prog'` by metis_tac[finalizer_prefix_static] >>
  `asm_frame_rel_tail [] prog' vs0.vs_data_section es0
     (entry_asm_state vs0 es0 with
        as_code := assemble prog' ++ vs0.vs_data_section) es0` by
    (rewrite_tac[asm_frame_rel_tail_nil] >> first_assum ACCEPT_TAC) >>
  `?esa pa. asm_frame_rel_tail [] prog' vs0.vs_data_section es0 cb esa /\
     call_trace es0 = pa ++ call_trace esa` by
    (irule asm_frame_prefix_call_trace_tail >> metis_tac[]) >>
  `?esb pb. asm_frame_rel_tail [] prog' vs0.vs_data_section es0 cb' esb /\
     call_trace es0 = pb ++ call_trace esb` by
    (irule asm_frame_prefix_call_trace_tail >> metis_tac[]) >>
  `cb.as_requests = s.vs_requests /\ cb.as_outcomes = s.vs_outcomes /\
   cb'.as_requests = s'.vs_requests /\ cb'.as_outcomes = s'.vs_outcomes` by
    gvs[] >>
  gvs[asm_frame_rel_tail_def, asm_frame_rel_def] >>
  qspecl_then [`\rq. T`, `call_trace es0`, `pa`,
    `call_trace esa`, `pb`, `call_trace esb`, `s.vs_requests`,
    `s'.vs_requests`] mp_tac trace_request_pairing >>
  simp[listTheory.FILTER_T, GSYM call_requests_def]
QED
