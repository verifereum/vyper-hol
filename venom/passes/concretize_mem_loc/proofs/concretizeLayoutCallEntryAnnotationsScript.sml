Theory concretizeLayoutCallEntryAnnotations
Ancestors frameResolvedCoherent frameResolvedTrace frameResolvedOrigins
  frameActivationLifetime frameJointTrace frameJointTransition frameOriginUpdates
  ptrDiscipline ptrDisciplineEmptyTaint venomExecSemantics venomState
  frameOriginHistoryCompletedWrites contextCodegenRel
  finite_map list arithmetic

(* The edge is from the fixed ambient annotation sequence. *)
Theorem layout_call_annotation_edge:
  resolved_annotation_edge C n
    (JointConfig stk PG G tn fn inst s oms om hs h) NONE qc
    ids ((rp,rv)::anns) ids' anns' /\
  decode_invoke inst = SOME (name,ops) ==>
  ids' = SUC n::ids /\
  anns' = (MAP (resolved_op rv) ops,FEMPTY)::(rp,rv)::anns
Proof
  simp[resolved_annotation_edge_def, lifetime_step_def] >> strip_tac >>
  qpat_x_assum `resolved_annotation_update _ _ _ _ _` mp_tac >>
  simp[Once resolved_annotation_update_cases] >> rpt strip_tac >> gvs[]
QED

Theorem layout_resolved_argument_fresh:
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids)
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  MEM (SOME ((token,aid),site)) (MAP (resolved_op rv) ops) ==>
  token <> SUC n
Proof
  strip_tac >> drule resolved_config_current >> simp[] >> strip_tac >>
  fs[resolved_frame_ok_def] >> drule_all resolved_arguments_live >>
  simp[resolved_live_def, lifetime_ok_def] >> rpt strip_tac >>
  `MEM token (birth::ids)` by (pure_rewrite_tac[MEM_EL] >> qexists `k` >> simp[]) >>
  gvs[lifetime_ok_def, EVERY_MEM] >>
  first_x_assum drule >> simp[]
QED

Theorem layout_resolved_phis_no_predecessor:
  !insts. resolved_phis NONE FEMPTY insts = FEMPTY
Proof
  Induct >> simp[resolved_phis_def, resolved_phi_def, origin_set_def] >>
  gen_tac >> Cases_on `h.inst_outputs` >> simp[]
QED

Theorem layout_phis_taint_no_predecessor:
  !insts tn. var_taint_empty tn.t_var ==>
    var_taint_empty (phis_taint NONE tn insts)
Proof
  Induct >> simp[phis_taint_def, phi_taint_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  irule set_var_taint_empty >> simp[]
QED

(* A successful initial PHI pass cannot execute a PHI without a predecessor. *)
Theorem layout_enters_block_no_predecessor:
  enters_block fn s post /\ s.vs_prev_bb = NONE ==>
  post = s with vs_inst_idx := 0
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  drule_all eval_phis_reset_writes >> strip_tac >>
  Cases_on `bb.bb_instructions` >>
  gvs[eval_phis_def, phi_prefix_length_def, AllCaseEqs()]
QED

Theorem layout_setup_enters_block_identity:
  setup_callee fn args caller = SOME cs /\ enters_block fn cs post ==>
  post = cs
Proof
  strip_tac >> drule setup_callee_no_predecessor >> strip_tac >>
  drule_all layout_enters_block_no_predecessor >>
  gvs[setup_callee_def, AllCaseEqs()]
QED

(* Identify the sampled source with the very setup state used by the call
   certificate; no second entry-state witness is selected. *)
Theorem layout_call_sampled_entry:
  joint_transition C (JointConfig stk PG G tn caller callinst s oms om hs h) NONE
    (JointConfig stk' PG' G' tn' fn' inst' post oms' om' hs' h') /\
  decode_invoke callinst = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  post = cs /\ fn' = callee /\ enters_block callee cs cs /\
  active_inst callee inst' cs
Proof
  simp[joint_transition_call_iff] >> rpt strip_tac >> gvs[] >>
  drule_all layout_setup_enters_block_identity >> strip_tac >> gvs[]
QED

Theorem layout_trace_resolved_argument_fresh:
  joint_trace vs0 C q0 es qs q /\ n <= LENGTH es /\
  EL n (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL n (lifetime_annotations 0 [0] es) = birth::ids /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  MEM (SOME ((token,aid),site)) (MAP (resolved_op rv) ops) ==>
  token <> SUC n
Proof
  strip_tac >> drule_all joint_trace_lifetimes >> strip_tac >>
  gvs[] >> drule_all layout_resolved_argument_fresh >> simp[]
QED

val _ = export_theory();
