(* Checked consumers of actual internal-return and branch endpoint packets.
   These lemmas do not assert existence of a callee execution. *)
Theory o1LowerDloadEndpointConsumer
Ancestors
  o1LowerDloadRunnerBoundary o1LowerDloadJointReturnBoundary
  o1LowerDloadPhiEntry o1LowerDloadEntryFetch venomWf venomInst
  o1LowerDloadJointRelation o1LowerDloadOccurrence o1LowerDloadEnvironment
  venomExecSemantics venomState contextCodegenRel finite_map pred_set list

Theorem ld_return_endpoint_consume:
  (?kr ri sr tr.
    ri.inst_opcode = RET /\ active_inst fn ri sr /\
    ld_joint_boundary vs C C' lo D (f::stk) PG G tn fn ri sr tr
      n a (ofr::U) B HP H sites X (caller'::ts) /\
    step_inst kr C ri sr = IntRet ir se /\
    sr.vs_call_ctx.cc_address = A0 /\
    step_inst kr C' ri tr = IntRet jr tr /\ r' = IntRet jr tr) /\
  A0 = f.cf_state.vs_call_ctx.cc_address /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ wf_function f.cf_fn /\
  active_inst f.cf_fn f.cf_inst f.cf_state /\ f.cf_inst.inst_opcode = INVOKE /\
  bind_outputs f.cf_inst.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state f.cf_state se)) = SOME s1 ==>
  ?next tr t1 fn'.
    r' = IntRet jr tr /\
    jr.iret_values = ir.iret_values /\ jr.iret_adopt_fmp = NONE /\
    ir.iret_adopt_fmp = NONE /\
    lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME fn' /\
    active_inst fn' f.cf_inst caller' /\
    bind_outputs f.cf_inst.inst_outputs jr.iret_values
      (adopt_return_fmp jr (merge_callee_state caller' tr)) = SOME t1 /\
    active_inst f.cf_fn next (s1 with vs_inst_idx := SUC f.cf_state.vs_inst_idx) /\
    ld_joint_boundary vs C C' lo D stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn next (s1 with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (t1 with vs_inst_idx := SUC caller'.vs_inst_idx)
      n ofr.of_owner U (DRESTRICT B {id | FST id <> a}) ofr.of_params
      (DRESTRICT ofr.of_prov (COMPL (set f.cf_inst.inst_outputs)))
      (DRESTRICT sites {id | FST id <> a})
      (DRESTRICT X {id | FST id <> a}) ts
Proof
  strip_tac >>
  drule_all ld_ret_endpoint >> strip_tac >> gvs[] >>
  drule_all ld_invoke_bind_successor >> strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) f.cf_fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  drule_all ld_joint_boundary_return >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ld_branch_endpoint_consume:
  (?kb bi sb tb te.
    MEM bi.inst_opcode [JMP; JNZ; DJMP] /\ active_inst fn bi sb /\
    ld_joint_boundary vs C C' lo D stk PG G tn fn bi sb tb
      n a U B HP H sites X ts /\
    step_inst kb C bi sb = OK se /\
    step_inst kb C' bi tb = OK te /\ r' = OK te /\
    se.vs_current_bb = te.vs_current_bb /\ se.vs_prev_bb = te.vs_prev_bb /\
    se.vs_call_ctx.cc_address = A0) /\
  wf_function fn /\ ~se.vs_halted /\ enters_block fn se s1 ==>
  ?next bb fn' te t1.
    r' = OK te /\
    lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s1.vs_inst_idx = SOME next /\ active_inst fn next s1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    enters_block fn' te t1 /\
    ld_joint_boundary vs C C' lo D stk PG (entry_prov fn se G)
      (entry_taint_vars fn se tn) fn next s1 t1
      n a U B HP (entry_prov fn se H) sites X ts /\
    s1.vs_call_ctx.cc_address = A0 /\ ~s1.vs_halted
Proof
  strip_tac >> drule_all ld_wf_enters_block_fetch >> strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  drule_all ld_joint_branch_entry >> strip_tac >>
  qpat_assum `enters_block fn se s1`
    (assume_tac o MATCH_MP ld_enters_block_call_ctx) >>
  qpat_assum `enters_block fn se s1`
    (assume_tac o MATCH_MP ld_enters_block_halted) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
