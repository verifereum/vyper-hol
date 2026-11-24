(* A rejecting external lock terminates the very same native trace. *)
Theory entryCreateLockExit
Ancestors
  nonreentrantEntryPath transientLockProps context loweringStateRelDefs
  bodyPtrDefs bodyFullHashKeccakFixed entryCreateTraceSplit entryCreateNativeResume
  fragGasOrigin fragExec exprLoweringProps instIdxIndep
  dftGasFromListTraceDefs venomExecProofs venomInstProofs venomExecSemantics venomState venomInst
  list rich_list arithmetic

(* Straight fragments use the same primitive operations as the native
   runner, which additionally advances the instruction index. *)
Theorem straight_abort_last_visit[local]:
  !code s a t.
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = Abort a t ==>
    ?pre i u v. MEM i code /\ step_inst_base i u = Abort a v /\
      create_trace_from p d k C f s = pre ++ [((p,d,i.inst_id),f,i,u)]
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  `DROP s.vs_inst_idx bb.bb_instructions <> []` by
    (strip_tac >> qpat_x_assum `isPREFIX (h::code) _` mp_tac >>
     pop_assum (fn th => rewrite_tac[th]) >> simp[]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by fs[] >>
  `DROP s.vs_inst_idx bb.bb_instructions =
     EL s.vs_inst_idx bb.bb_instructions :: DROP (SUC s.vs_inst_idx) bb.bb_instructions` by
    simp[DROP_CONS_EL] >>
  `get_instruction bb s.vs_inst_idx = SOME h /\
   isPREFIX code (DROP (SUC s.vs_inst_idx) bb.bb_instructions)` by
    fs[get_instruction_def] >>
  Cases_on `step_inst_base h s` >> gvs[run_inst_seq_def]
  >- (rename1 `step_inst_base h s = OK w` >>
      `step_inst k C h s = OK w` by simp[step_inst_non_invoke] >>
      `w.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
      drule_all create_trace_from_next >> strip_tac >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      first_x_assum (qspecl_then
        [`w with vs_inst_idx := SUC s.vs_inst_idx`, `a`,
         `t with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >>
      strip_tac >> qexistsl_tac [`((p,d,h.inst_id),f,h,s)::pre`, `i`, `u`, `v`] >>
      simp[trace_step_noninvoke]) >>
  qexistsl_tac [`[]`, `EL s.vs_inst_idx bb.bb_instructions`, `s`, `t`] >>
  simp[create_trace_from_def, Once exec_block_def] >>
  drule_then (fn th => simp[Once th, step_inst_non_invoke, trace_step_noninvoke]) trace_block_visit
QED

Theorem lock_abort_opcode[local]:
  MEM i (transient_lock_code key view sa) /\
  step_inst_base i u = Abort a v ==>
  (i.inst_opcode = ASSERT /\ a = Revert_abort) \/
  (i.inst_opcode = TSTORE /\ a = ExHalt_abort)
Proof
  Cases_on `view` >>
  rw[transient_lock_code_def] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, exec_pure2_def,
       exec_pure1_def, exec_write2_def, eval_operands_def, eval_operand_def] >>
  rw[AllCaseEqs()]
QED

Theorem rejected_lock_trace[local]:
  is_view_mut mut = (mut = View) /\
  cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
  lock_if_nr cx T (is_view_mut mut) es0 = (INR exc,es_abort) /\
  compile_guarded_body cenv T global_nonreentrant_slot T (mut = View)
    fbody rt sa = ((),st') /\
  fn_has_code sa st' func /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H : (bool # bytes32 # type_value) list # num list.
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    ghost_inv H NONE cenv cx es0 G0 tn0 s0) ==>
  ?pre i u.
    (i.inst_opcode = ASSERT \/ i.inst_opcode = TSTORE) /\
    create_trace_from p d k ctx func s0 = pre ++ [((p,d,i.inst_id),func,i,u)]
Proof
  strip_tac >>
  drule_all guarded_body_code_from_registration >> simp[] >> strip_tac >>
  `global_nonreentrant_slot < dimword (:256)` by
    simp[global_nonreentrant_slot_def, wordsTheory.dimword_def] >>
  qpat_assum `!H. stmt_state_rel H _ _ _ _ _ _ /\ _`
    (qspec_then `ARB` strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    (drule_then ACCEPT_TAC stmt_state_rel_allocas_below_fmp) >>
  `cx.txn.is_static = s0.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  drule_all (INST_TYPE [alpha |-> ``:256``] nonreentrant_entry_abort_joint_with_view) >>
  disch_then (qx_choosel_then [`a`,`s_abort`,`G_abort`,`tn_abort`]
    (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
  qabbrev_tac `code = transient_lock_code global_nonreentrant_slot (mut = View) sa` >>
  `?t. run_inst_seq code s0 = Abort a t` by
    (qpat_x_assum `(_ /\ _ /\ exc = _) \/ _` strip_assume_tac >>
     fs[Abbr `code`, transient_lock_code_execution]) >>
  `?bb. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX code (DROP s0.vs_inst_idx bb.bb_instructions)` by
    metis_tac[compile_nonreentrant_lock_transient_prefix, markerTheory.Abbrev_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    (Cases_on `mut = View` >> simp[Abbr `code`, transient_lock_code_def,
                                  mk_inst_def, is_terminator_def]) >>
  drule_all straight_abort_last_visit >>
  disch_then (qspecl_then [`p`, `k`, `d`, `ctx`] strip_assume_tac) >>
  `MEM i (transient_lock_code global_nonreentrant_slot (mut = View) sa)` by
    fs[Abbr `code`] >>
  drule_all lock_abort_opcode >> metis_tac[]
QED

(* Registration can have arbitrary earlier visits. Only its completed
   prefix equality is needed to select the actual last lock visit. *)
Theorem rejected_lock_excludes_create_last:
  is_view_mut mut = (mut = View) /\
  cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
  lock_if_nr cx T (is_view_mut mut) es0 = (INR exc,es_abort) /\
  compile_guarded_body cenv T global_nonreentrant_slot T (mut = View)
    fbody rt sa = ((),st') /\
  fn_has_code sa st' func /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H : (bool # bytes32 # type_value) list # num list.
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    ghost_inv H NONE cenv cx es0 G0 tn0 s0) /\
  ctx.ctx_entry = SOME nm /\ lookup_function nm ctx.ctx_functions = SOME func /\
  fn_entry_label func = SOME lbl /\
  lookup_block lbl func.fn_blocks = SOME bb /\
  (!b. MEM b func.fn_blocks ==> phi_prefix_length b.bb_instructions = 0) /\
  gas_origin_path mem explicit ctx func
    (vi with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
    marks0 (OK s0) /\
  (!fuel. bound <= fuel ==>
    ?p d pre. trace_context fuel ctx vi = pre ++ [((p,d,hit.inst_id),fn',hit,t)]) ==>
  hit.inst_opcode <> CREATE /\ hit.inst_opcode <> CREATE2
Proof
  strip_tac >>
  drule_all create_trace_from_completed >>
  disch_then (qx_choose_then `b` (mk_asm "resume")) >>
  qabbrev_tac `k = MAX b bound` >>
  `b <= k /\ bound <= k` by simp[Abbr `k`] >>
  `bound <= SUC k` by decide_tac >>
  asm_x "resume" (qspecl_then [`k`,`[]`,`1`] mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`reg_pre`,`rd`,`rk`] strip_assume_tac) >>
  `phi_prefix_length bb.bb_instructions = 0` by metis_tac[lookup_block_MEM] >>
  `trace_context (SUC k) ctx vi = reg_pre ++ create_trace_from [] rd rk ctx func s0` by
    (qpat_x_assum `create_trace_from [] 1 k _ _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[trace_context_def, trace_function_def, Once (cj 3 trace_defs),
          eval_phis_no_phi, create_trace_from_def]) >>
  qpat_x_assum `!fuel. bound <= fuel ==> _` (qspec_then `SUC k` mp_tac) >>
  simp[] >> strip_tac >>
  drule_all rejected_lock_trace >>
  disch_then (qspecl_then [`[]`,`rk`,`rd`] strip_assume_tac) >>
  `hit = i` by
    (qpat_x_assum `reg_pre ++ create_trace_from [] rd rk ctx func s0 = _`
       (mp_tac o AP_TERM ``LAST : list_visit list -> list_visit``) >>
     simp[listTheory.APPEND_ASSOC] >> metis_tac[]) >>
  gvs[]
QED
