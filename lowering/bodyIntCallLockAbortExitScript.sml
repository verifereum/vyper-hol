(* Certify the same transient-lock abort endpoint that the joint path returns. *)
Theory bodyIntCallLockAbortExit
Ancestors
  transientLockProps transientLockPtr createSizeExit
  fragGasCopyLoop fragGasSeqPtr fragGasOriginPtr instSeqPtrLo
  fragExecMem fragExec memSafeRun ptrDiscipline
  emitHelperProps venomInst venomState list rich_list
  contextCodegenRel[qualified] codegenRel[qualified] unitTransformDefs[qualified] gasPathPtrExec[qualified,ignore_grammar] fragGasOriginPtrLoop[qualified,ignore_grammar] bool[qualified,ignore_grammar]

Theorem transient_lock_abort_origin_ptr_safe:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (transient_lock_code key view st) (DROP s.vs_inst_idx bb.bb_instructions) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  key_taint tn.t_trans (n2w key) = {} /\
  (tload (n2w key) s = 1w \/ (~view /\ s.vs_call_ctx.cc_static)) ==>
  ?t G' tn'.
    ~oversized_create_abort ctx
      (Abort (if tload (n2w key) s = 1w then Revert_abort else ExHalt_abort) t) /\
    (!D explicit.
      gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
        (Abort (if tload (n2w key) s = 1w then Revert_abort else ExHalt_abort) t,G',tn'))
Proof
  DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qabbrev_tac `code = transient_lock_code key view st` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) code` by
    (Cases_on `view` >> simp[Abbr `code`, transient_lock_code_def, mk_inst_opcode,
                            is_terminator_def]) >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >> Cases_on `view` >>
     simp[Abbr `code`, transient_lock_code_def, mk_inst_def,
          unitTransformDefsTheory.inst_mem_below_frontier_def, inst_dload_in_section_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def]) >>
  qabbrev_tac `a = if tload (n2w key) s = 1w then Revert_abort else ExHalt_abort` >>
  `?t. run_inst_seq code s = Abort a t` by
    (Cases_on `tload (n2w key) s = 1w` >>
     fs[Abbr `a`, Abbr `code`, transient_lock_code_execution]) >>
  `(ctx_has_dalloca ctx ==>
    !pre i post u. code = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     `MEM i code` by
       (qpat_assum `code = _ ++ _` (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
     Cases_on `view` >> fs[Abbr `code`, transient_lock_code_def] >> gvs[mk_inst_opcode]) >>
  drule_all run_inst_seq_abort_origin_ptr_uniform >> strip_tac >>
  `!D. ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code s G' tn'` by
    (gen_tac >> simp[Abbr `code`] >> irule transient_lock_abort_ptr_ghost >> simp[]) >>
  qpat_assum `!D. ?G' tn'. inst_seq_ptr D 0 _ _ _ _ _ _ _ G' tn'`
    (qspec_then `ARB` (qx_choose_then `J` (qx_choose_then `tj` assume_tac))) >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn code s J tj` by
    (gen_tac >>
     qpat_assum `!D. ?G' tn'. inst_seq_ptr D 0 _ _ _ _ _ _ _ G' tn'`
       (qspec_then `D` (qx_choose_then `J1` (qx_choose_then `tk` assume_tac))) >>
     `J1 = J /\ tk = tj` by (irule inst_seq_ptr_ghost_unique >> metis_tac[]) >>
     irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >> gvs[]) >>
  qexistsl_tac [`t with vs_inst_idx := j`, `J`, `tj`] >>
  conj_tac
  >- (Cases_on `tload (n2w key) s = 1w`
      >- simp[Abbr `a`] >>
      simp[Abbr `a`] >> irule oversized_create_abort_static >>
      qpat_x_assum `run_inst_seq code s = Abort a t` mp_tac >>
      fs[Abbr `code`, transient_lock_code_execution] >>
      disch_then (SUBST1_TAC o SYM) >>
      simp[transient_lock_checked_state_def, halt_state_def, set_returndata_def,
           update_var_def]) >>
  fs[Abbr `code`, Abbr `a`] >> metis_tac[]
QED

Theorem lock_abort_suffix_no_oversize_transfer:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (Abort a t,G1,tn1) /\
  (?u G2 tn2. ~oversized_create_abort ctx (Abort a u) /\
     !D' E. gas_origin_ptr_path (D',lo,E,ctx,func,PG)
       (s,G,tn) [] (Abort a u,G2,tn2)) ==>
  ~oversized_create_abort ctx (Abort a t)
Proof
  strip_tac >>
  qpat_assum `!D' E. gas_origin_ptr_path (D',lo,E,ctx,func,PG)
      (s,G,tn) [] (Abort a u,G2,tn2)`
    (qspecl_then [`D`,`explicit`] assume_tac) >>
  qpat_assum `gas_origin_ptr_path _ _ [] (Abort a t,G1,tn1)`
    (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
  qpat_assum `gas_origin_ptr_path _ _ [] (Abort a u,G2,tn2)`
    (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
  `exit_result (Abort a t)` by simp[exit_result_def] >>
  `exit_result (Abort a u)` by simp[exit_result_def] >>
  drule_all gasPathPtrExecTheory.gas_path_ptr_exit_unique >>
  simp[exit_result_def] >> strip_tac >>
  (metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections, gasPathPtrExecTheory.gas_path_ptr_exit_unique, fragGasOriginPtrLoopTheory.gas_origin_ptr_path_loop, fragGasOriginPtrTheory.gas_origin_ptr_path_rules, transient_lock_abort_origin_ptr_safe, fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted, fragGasCopyLoopTheory.run_inst_seq_abort_origin_ptr_uniform, fragGasSeqPtrTheory.sha_zero_origin_abort, createSizeExitTheory.oversized_create_abort_def, fragExecTheory.exit_result_def, boolTheory.F_DEF, boolTheory.T_DEF])
QED
