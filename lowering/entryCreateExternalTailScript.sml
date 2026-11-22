(* A reached normal body exit starts the optional unlock and STOP, not CREATE. *)
Theory entryCreateExternalTail
Ancestors
  entryCreateNativeResume nonreentrantExit loweringHalt fragExec emitHelperProps
  dftGasFromListTraceDefs venomExecSemantics venomState venomInst list arithmetic

Theorem trace_from_stop[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id STOP [] []) ==>
  create_trace_from p d k C func s = [((p,d,id),func,mk_inst id STOP [] [],s)]
Proof
  strip_tac >>
  simp[create_trace_from_def] >>
  drule trace_block_visit >> disch_then (fn th => simp[Once th]) >>
  simp[Once exec_block_def, trace_step_noninvoke, mk_inst_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs]
QED

Theorem trace_from_tstore_stop[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id TSTORE [Lit key; Lit 0w] []) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst id' STOP [] []) /\
  ~s.vs_call_ctx.cc_static ==>
  ?prefix u. create_trace_from p d k C func s =
    prefix ++ [((p,d,id'),func,mk_inst id' STOP [] [],u)]
Proof
  strip_tac >>
  qabbrev_tac `un = mk_inst id TSTORE [Lit key; Lit 0w] []` >>
  qabbrev_tac `t = tstore key 0w s` >>
  `step_inst k C un s = OK t /\ ~is_terminator un.inst_opcode /\
   un.inst_opcode <> INVOKE /\ t.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `un`, Abbr `t`, tstore_def, mk_inst_def, is_terminator_def,
         step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def,
         eval_operand_def, eval_operands_def] >>
  drule_all create_trace_from_next >> strip_tac >>
  qexistsl_tac [`[((p,d,un.inst_id),func,un,s)]`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[trace_step_noninvoke] >> irule trace_from_stop >> gvs[] >> metis_tac[]
QED

Theorem unlock_stop_trace_last[local]:
  (if nr then compile_nonreentrant_unlock nkey T iv else comp_return ()) se =
    ((),su) /\
  emit_inst STOP [] [] su = ((),sb) /\
  fn_has_code se sb func /\
  (nr /\ ~iv ==> ~s.vs_call_ctx.cc_static) /\
  s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts ==>
  ?prefix u. create_trace_from p d k C func s =
    prefix ++ [((p,d,su.cs_next_id),func,mk_inst su.cs_next_id STOP [] [],u)]
Proof
  strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  qspecl_then [`nr`,`nkey`,`T`,`iv`,`se`,`su`] mp_tac optional_unlock_code >>
  simp[] >> strip_tac >>
  Cases_on `nr /\ ~iv` >> fs[]
  >- (qspecl_then [`se`, `sb`, `func`,
        `[mk_inst se.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] [];
          mk_inst su.cs_next_id STOP [] []]`] mp_tac fn_has_code_same_block >>
      (impl_tac >- gvs[APPEND_ASSOC]) >>
      disch_then (qx_choose_then `bb` strip_assume_tac) >>
      qpat_assum `!j. j < _ ==> _` (qspec_then `0` mp_tac) >>
      qpat_x_assum `!j. j < _ ==> _` (qspec_then `1` mp_tac) >>
      simp[ADD1] >> rpt strip_tac >>
      irule trace_from_tstore_stop >> simp[ADD1] >>
      qexistsl_tac [`se.cs_next_id`, `n2w nkey`] >> simp[]) >>
  gvs[] >> drule_all fn_has_code_same_block >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  qpat_x_assum `!j. j < _ ==> _` (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`[]`,`s`] >> simp[] >> irule trace_from_stop >> metis_tac[]
QED

Theorem completed_external_tail_excludes_create_last:
  compile_guarded_body cenv nr nkey T iv stmts NONE st = ((),sb) /\
  (if nr then compile_nonreentrant_lock nkey T iv else comp_return ()) st =
    ((),sl) /\
  compile_stmts cenv NoLoop (BaseT BoolT) stmts sl = ((),se) /\
  ~block_is_terminated se /\ fn_has_code se sb func /\
  (nr /\ ~iv ==> ~s.vs_call_ctx.cc_static) /\
  s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts /\
  (i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2) ==>
  create_trace_from p d k C func s <> pre ++ [((p',d',i.inst_id),hit,i,u)]
Proof
  strip_tac >> drule_all compile_guarded_body_stop_unlock_parts >> strip_tac >>
  drule_all_then (qspecl_then [`p`, `k`, `d`, `C`] strip_assume_tac)
    unlock_stop_trace_last >>
  strip_tac >> fs[APPEND_11_LENGTH] >> gvs[mk_inst_def]
QED
