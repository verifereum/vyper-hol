(* A single storage instruction, with all non-storage state framed. *)
Theory storageStoreFrame
Ancestors
  loweringPosts stmtSimDefs stmtSimProps
  list rich_list finite_map fragExec  stmtSimDecl emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomInst venomState

Theorem storage_emit_frame_frag:
  !ctx func cenv cx es' s tr dst addr op w st st' R.
    emit_void (if tr then TSTORE else SSTORE) [dst; op] st = ((), st') /\
    eval_operand dst s = SOME addr /\ eval_operand op s = SOME w /\
    stmt_state_rel ctx func cenv cx es'
      (if tr then tstore addr w s else sstore addr w s) ==>
    frag_exec ctx st st' (\t. t = s)
      (\t. stmt_state_rel ctx func cenv cx es' t /\
           t.vs_memory = s.vs_memory /\
           (!x. lookup_var x t = lookup_var x s) /\
           (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                    FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  rpt strip_tac >>
  `frag_exec ctx st st' (\t. t = s)
     (\t. stmt_state_rel ctx func cenv cx es' t /\
          t.vs_memory = s.vs_memory /\
          (!x. lookup_var x t = lookup_var x s) /\
          (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                   FLOOKUP t.vs_allocas aid = SOME b)) (\r. F)` by
    (imp_res_tac emitted_insts_emit_void >> imp_res_tac emit_void_extends >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts st st')` by
       (Cases_on `tr` >> gvs[venomInstTheory.mk_inst_def, is_terminator_def]) >>
     irule frag_exec_run_inst_seq >>
     fs[same_blocks_def, IS_PREFIX_APPEND3] >>
     rpt strip_tac >> gvs[] >>
     `step_inst_base (mk_inst st.cs_next_id (if tr then TSTORE else SSTORE)
                        [dst; op] []) s =
        OK (if tr then tstore addr w s else sstore addr w s)` by
       (`~s.vs_call_ctx.cc_static` by
          (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
           Cases_on `tr` >>
           simp[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
                tstore_def, sstore_def, LET_THM]) >>
        Cases_on `tr` >>
        gvs[step_inst_base_opcode_eqs, exec_write2_def, mk_inst_def]) >>
     Cases_on `tr` >> gvs[] >>
     simp[run_inst_seq_def, stmt_state_rel_inst_idx] >>
     gvs[lookup_var_def, sstore_def, tstore_def, LET_THM]) >>
  pop_assum (mp_then Any irule frag_exec_weaken) >> simp[]
QED

Theorem storage_emit_frame_run:
  !ctx func cenv cx es' s tr dst addr op w st st'.
    emit_void (if tr then TSTORE else SSTORE) [dst; op] st = ((), st') /\
    eval_operand dst s = SOME addr /\ eval_operand op s = SOME w /\
    stmt_state_rel ctx func cenv cx es'
      (if tr then tstore addr w s else sstore addr w s) /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\
        t.vs_memory = s.vs_memory /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt strip_tac >> drule_all storage_emit_frame_frag >>
  disch_then (qspec_then `\r. F` assume_tac) >>
  drule frag_exec_no_exit_run >> disch_then drule >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >> metis_tac[]
QED
