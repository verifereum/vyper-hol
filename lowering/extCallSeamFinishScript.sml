(* The external-call failure suffix, sharing the generic raw-call branch. *)
Theory extCallSeamFinish
Ancestors
  extCallSeamOracle rawCallFragPath exprSimRawCallCalldata exprLoweringProps
  emitHelperProps emitHelper exprLowering venomState venomInst list rich_list
  fragGasPath compileEnv fragExec

Theorem extcall_finish_branch_path:
  emit_inst JNZ [cond;Label ok;Label fl] [] sa = (a,sx) /\
  new_block fl sx = (x,sf) /\
  emit_op RETURNDATASIZE [] sf = (z,sz) /\
  compile_alloc_buffer 0 sz = (rb,sp) /\
  emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;z] sp = (b,sc) /\
  emit_inst REVERT [rb.buf_operand;z] [] sc = (c,se) /\
  new_block ok se = (y,sk) /\
  eval_operand cond s = SOME (if success then 1w else 0w) /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  frag_path ctx sa sk (\u. u = s)
    (\u. success /\ u = jump_to ok s with vs_inst_idx := LENGTH sk.cs_current_insts)
    (\r. ?u. ~success /\ r = Abort Revert_abort u /\
               u.vs_returndata = s.vs_returndata)
Proof
  Cases_on `a` >> Cases_on `b` >> Cases_on `c` >>
  strip_tac >> irule raw_call_finish_branch_guarded_frag >>
  conj_tac >- simp[] >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst REVERT _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_void RETURNDATACOPY _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op RETURNDATASIZE _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block _ _ = _`)) >>
  qexists_tac `success` >> simp[cs_extends_refl] >>
  conj_tac
  >- (strip_tac >> irule frag_path_run_inst_seq >>
      simp[emitted_insts_def, run_inst_seq_def]) >>
  `ci_mono sf sz /\ ci_mono sz sp /\ ci_mono sp sc /\ ci_mono sc se` by
    (rpt conj_tac >> metis_tac[ci_mono_emit_op, ci_mono_compile_alloc_buffer,
       ci_mono_emit_void, ci_mono_emit_inst, pairTheory.SND]) >>
  fs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Theorem extcall_finish_path:
  comp_bind (fresh_label "extcall_fail") (\fl.
  comp_bind (fresh_label "extcall_cont") (\ok.
  comp_ignore_bind (emit_inst JNZ [cond;Label ok;Label fl] [])
  (comp_ignore_bind (new_block fl)
  (comp_bind (emit_op RETURNDATASIZE []) (\z.
  comp_bind (compile_alloc_buffer 0) (\rb.
  comp_ignore_bind (emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;z])
  (comp_ignore_bind (emit_inst REVERT [rb.buf_operand;z] [])
    (new_block ok)))))))) sa = (u,sb) /\
  eval_operand cond s = SOME (if success then 1w else 0w) /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  frag_path ctx sa sb (\t. t = s)
    (\t. success /\ t = jump_to sb.cs_current_bb s)
    (\r. ?t. ~success /\ r = Abort Revert_abort t /\
               t.vs_returndata = s.vs_returndata)
Proof
  simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule_all extcall_finish_branch_path >>
  disch_then (qspec_then `ctx` mp_tac) >>
  imp_res_tac fresh_label_props >>
  imp_res_tac new_block_props >>
  simp[frag_path_def, fn_has_code_def, emitted_blocks_def, jump_to_def]
QED

Theorem extcall_finish_shape:
  comp_bind (fresh_label "extcall_fail") (\fl.
  comp_bind (fresh_label "extcall_cont") (\ok.
  comp_ignore_bind (emit_inst JNZ [cond;Label ok;Label fl] [])
  (comp_ignore_bind (new_block fl)
  (comp_bind (emit_op RETURNDATASIZE []) (\z.
  comp_bind (compile_alloc_buffer 0) (\rb.
  comp_ignore_bind (emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;z])
  (comp_ignore_bind (emit_inst REVERT [rb.buf_operand;z] [])
    (new_block ok)))))))) sa = (u,sb) ==>
  ci_mono sa sb /\ sb.cs_current_insts = [] /\
  (!cenv. local_ptrs_reserved cenv sa ==> local_ptrs_reserved cenv sb) /\
  (!p. safe_operand sa p ==> safe_operand sb p)
Proof
  strip_tac >>
  `ci_mono sa sb` by
    (qmatch_asmsub_abbrev_tac `mf sa = (u,sb)` >>
     `sb = SND (mf sa)` by simp[] >> pop_assum SUBST1_TAC >>
     unabbrev_all_tac >>
     rpt (FIRST [irule ci_mono_bind, irule ci_mono_ignore_bind] >>
          simp[ci_mono_fresh_label, ci_mono_emit_inst, ci_mono_new_block,
               ci_mono_emit_op, ci_mono_compile_alloc_buffer, ci_mono_emit_void] >>
          rpt gen_tac)) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `_ sa = (u,sb)` mp_tac >>
      simp[comp_bind_def, comp_ignore_bind_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >>
      drule new_block_props >> simp[]) >>
  fs[ci_mono_def] >> conj_tac
  >- (rpt strip_tac >> irule local_ptrs_reserved_next_var >>
      goal_assum (drule_at Any) >> simp[]) >>
  rpt strip_tac >> irule exprSafeOperandTheory.safe_operand_mono >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem extcall_jump_wb_frame:
  wb_frame cenv es es' st s0 (jump_to l s) = wb_frame cenv es es' st s0 s
Proof
  simp[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def,
       loweringPostsTheory.popped_kept_def,
       local_region_def, lookup_var_def, jump_to_def]
QED

Theorem extcall_jump_fields:
  (jump_to l s).vs_memory = s.vs_memory /\
  (jump_to l s).vs_allocas = s.vs_allocas /\
  (jump_to l s).vs_alloca_next = s.vs_alloca_next /\
  (jump_to l s).vs_returndata = s.vs_returndata /\
  (jump_to l s).vs_halted = s.vs_halted /\
  (jump_to l s).vs_current_bb = l /\ (jump_to l s).vs_inst_idx = 0
Proof
  simp[jump_to_def]
QED
