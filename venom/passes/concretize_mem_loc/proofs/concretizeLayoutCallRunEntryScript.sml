Theory concretizeLayoutCallRunEntry
Ancestors concretizeLayoutCallEntryAnnotations concretizeLayoutCallSetupMemory
  concretizeLayoutCallSetupFields concretizeLayoutPhaseInputs
  concretizeLayoutScopedRun concretizeLayoutPhaseOrigin concretizeLayoutArgumentRoots
  concretizeLayoutBlockEntry concretizeLayoutCallControl
  concretizeLayoutFrameEnvironment frameResolvedCoherent frameActivationLifetime
  frameJointTransition frameJointTrace concretizeStepStructure venomWf venomInstProofs1
  frameRelocationLocal concretizeLayoutSupplement concretizeLayoutParameterSegments
  venomExecProofs o1PassContract contextCodegenRel venomInst finite_map list arithmetic

Theorem layout_selected_call_scoped_run:
  !D lo vs0 C C' q0 es qs q g a n stk PG G tn callerfn callinst caller
    oms om hs hist birth ids rp rv anns ids' anns' name ops callee args cs
    target positions P caller'.
  layout_ordinary_entry D lo vs0 C C' q0 es qs q a caller caller' /\
  ~a.lop_pending /\ n = a.lop_cursor /\
  a.lop_config = JointConfig stk PG G tn callerfn callinst caller oms om hs hist /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::anns /\
  a.lop_ids = EL n (lifetime_annotations 0 [0] es) /\
  n < LENGTH es /\ EL n es = NONE /\
  joint_transition C a.lop_config NONE (EL (SUC n) (q0::qs)) /\
  resolved_annotation_edge C n a.lop_config NONE (EL (SUC n) (q0::qs))
    a.lop_ids a.lop_anns ids' anns' /\
  decode_invoke callinst = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME callee /\
  eval_operands ops caller = SOME args /\ setup_callee callee args caller = SOME cs /\
  o1_fn_shape C callerfn /\ fn_ptr_ok P callerfn /\
  MEM callinst (fn_insts callerfn) /\ taint_ok callerfn tn callinst caller /\
  EVERY bb_well_formed callee.fn_blocks /\
  target = concretize_function_with_positions positions callee /\
  ~NULL target.fn_blocks /\ caller.vs_labels = caller'.vs_labels /\
  vs0.vs_allocas = FEMPTY ==>
  ?args' ct h. eval_operands ops caller' = SOME args' /\
    setup_callee target args' caller' = SOME ct /\
    h.lop_cursor = SUC n /\ h.lop_ids = SUC n::a.lop_ids /\
    h.lop_ids = EL (SUC n) (lifetime_annotations 0 [0] es) /\
    ~h.lop_pending /\ layout_ordinary_trace vs0 C q0 es qs q h cs /\
    layout_ordinary_state D lo C' q0 es qs h cs ct /\
    layout_scoped_run D lo vs0 C C' q0 es qs q g callee target cs ct
Proof
  rpt gen_tac >> strip_tac >>
  fs[layout_ordinary_entry_def, layout_ordinary_trace_def,
     layout_ordinary_state_def] >> gvs[] >>
  `callinst.inst_opcode = INVOKE` by
    (fs[joint_transition_call_iff]) >>
  `!i token aid site. i < LENGTH args /\
      EL i (MAP (resolved_op rv) ops) = SOME ((token,aid),site) ==>
      token <> SUC a.lop_cursor` by
    (rpt gen_tac >> disch_tac >>
     `LENGTH args = LENGTH ops` by
       (drule_all argument_roots_evaluation >> strip_tac >> simp[]) >>
     `MEM (SOME ((token,aid),site)) (MAP (resolved_op rv) ops)` by
       (simp[MEM_EL] >> qexists `i` >> gvs[]) >>
     `a.lop_cursor <= LENGTH es` by simp[] >>
     drule_all layout_trace_resolved_argument_fresh >> simp[]) >>
  drule_all disciplined_invoke_setup_pushed_roots >>
  disch_then (qspec_then `callee` strip_assume_tac) >>
  drule_all relocation_environment_setup_callee >>
  disch_then (qspec_then `args'` strip_assume_tac) >> gvs[] >>
  drule local_rel_observation >> strip_tac >>
  drule_all layout_setup_local_obs >> strip_tac >>
  drule_all layout_setup_supplement >> strip_tac >>
  drule_all layout_setup_static_fields >> strip_tac >>
  `!x y. joint_relocation_demand lo (concretize_positions C') q0 es qs
      (SUC a.lop_cursor) x y ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs a.lop_cursor x y` by
    (rpt strip_tac >> irule layout_call_demand_retained >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `local_rel (\u. F)
    (guarded_ptr (retpc_var callee)
      (activation_lookup 0 (concretize_positions C') (SUC a.lop_cursor::birth::ids)
        (callee::callerfn::MAP (\f. f.cf_fn) stk))
      (FEMPTY:(string, (num#num)#(num#num)) fmap))
    (guarded_bytes (retpc_var callee)
      (FEMPTY:(string, (num#num)#(num#num)) fmap) (tn with t_var := FEMPTY))
    (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC a.lop_cursor))
    concretize_local_obs cs tc` by
    (drule_all (Q.INST [`Obs'` |-> `concretize_local_obs`] layout_setup_local_rel) >>
     disch_then irule) >>
  `relocation_taint_le
    (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC a.lop_cursor))
    (tn with t_var := FEMPTY) (a.lop_target_taint with t_var := FEMPTY)` by
    (irule layout_call_taint_restrict >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `EL a.lop_cursor qs` >>
  drule_all layout_call_sampled_entry >> strip_tac >> gvs[] >>
  drule_all layout_call_annotation_edge >> strip_tac >> gvs[] >>
  drule_all resolved_config_call_exact >>
  disch_then (qspec_then `SUC a.lop_cursor` assume_tac) >>
  `EL (SUC a.lop_cursor) (lifetime_annotations 0 [0] es) =
    SUC a.lop_cursor::birth::ids` by
    (drule_all lifetime_annotations_fresh_call >> simp[]) >>
  `lifetime_ok (SUC a.lop_cursor) (SUC a.lop_cursor::birth::ids)
    (EL (SUC a.lop_cursor) (q0::qs))` by
    (`SUC a.lop_cursor <= LENGTH es` by simp[] >>
     drule_all joint_trace_lifetimes >> simp[]) >>
  `cs.vs_prev_bb = tc.vs_prev_bb /\ cs.vs_current_bb = tc.vs_current_bb` by
    (`(HD callee.fn_blocks).bb_label =
      (HD (concretize_function_with_positions positions callee).fn_blocks).bb_label` by
       (Cases_on `callee.fn_blocks` >>
        gvs[concretize_positions_blocks, concretize_positions_block_label]) >>
     drule_all paired_setup_control >> simp[parameter_control_def]) >>
  `?bb. lookup_block cs.vs_current_bb callee.fn_blocks = SOME bb` by
    (fs[enters_block_def] >> metis_tac[]) >>
  `MEM bb callee.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb_well_formed bb` by fs[EVERY_MEM] >>
  `EVERY (\inst. MEM inst (fn_insts callee)) bb.bb_instructions` by
    (simp[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  drule_all concretize_enters_block_transport >>
  disch_then (qspec_then `positions` strip_assume_tac) >>
  drule_all layout_setup_enters_block_identity >> strip_tac >> gvs[] >>
  qpat_x_assum `joint_transition C _ NONE _` mp_tac >>
  simp[joint_transition_call_iff] >> strip_tac >> gvs[] >>
  `LENGTH es = LENGTH qs` by
    (fs[joint_trace_def] >> drule joint_chain_length >> simp[]) >>
  qabbrev_tac `h = a with <| lop_cursor := SUC a.lop_cursor;
    lop_bound := SUC a.lop_cursor; lop_pending := F;
    lop_config := EL (SUC a.lop_cursor) (q0::qs);
    lop_ids := SUC a.lop_cursor::birth::ids;
    lop_anns := (MAP (resolved_op rv) ops,FEMPTY)::(rp,rv)::anns;
    lop_target_taint := a.lop_target_taint with t_var := FEMPTY |>` >>
  `~h.lop_pending /\ layout_ordinary_trace vs0 C q0 es qs q h cs /\
    layout_ordinary_state D lo C' q0 es qs h cs tc` by
    (simp[Abbr `h`, layout_ordinary_trace_def, layout_ordinary_state_def] >>
     fs[joint_trace_def] >> drule joint_chain_length >> simp[]) >>
  qexists `h` >> simp[Abbr `h`] >>
  irule layout_scoped_run_intro >> goal_assum (drule_at Any) >> simp[]
QED

val _ = export_theory();
