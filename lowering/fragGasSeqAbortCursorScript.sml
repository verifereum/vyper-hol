Theory fragGasSeqAbortCursor
Ancestors
  fragGasSeqAbort checkedPrefixCursor fragGasSeqPtr fragGasOriginPtr fragGasOrigin
  fragGasPathPtr ptrSafeRun gasCount gasEvents fragExec fragExecMem memSafeRun
  exprLoweringProps instIdxIndep venomExecSemantics venomExecProofs venomInstProofs venomState
  list rich_list arithmetic

(* The abort cursor is fixed by the executed prefix, independently of ghosts. *)
Theorem run_inst_seq_abort_origin_ptr_cursor:
  !code s a t ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) code /\
    run_inst_seq_mem_ok code s /\
    (ptrDiscipline$ctx_has_dalloca ctx ==>
      !pre i post u. code = pre ++ i::post /\
        run_inst_seq pre s = OK u ==>
        unitTransformDefs$dalloca_no_wrap i u) /\
    run_inst_seq code s = Abort a t ==>
    ?j. (?i u. MEM i code /\ lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
               get_instruction bb u.vs_inst_idx = SOME i /\
               step_inst_base i u = Abort a (t with vs_inst_idx := j)) /\
        (!D lo explicit PG G tn HG th.
          inst_seq_ptr D lo ctx func PG G tn code s HG th ==>
          gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
            (Abort a (t with vs_inst_idx := j),HG,th))
Proof
  Induct_on `code` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  `(ctx_has_dalloca ctx ==> dalloca_no_wrap h s)` by
    (disch_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> _` (mp_tac o UNDISCH) >>
     disch_then (qspecl_then [`[]`, `h`, `code`, `s`] mp_tac) >>
     simp[run_inst_seq_def]) >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, run_inst_seq_mem_ok_def]
  >- suspend "continue"
  >> suspend "abort"
QED

Resume run_inst_seq_abort_origin_ptr_cursor[continue]:
  rename1 `step_inst_base h s = OK mid` >>
  `step_inst 0 ctx h s = OK mid` by simp[step_inst_non_invoke] >>
  `~mid.vs_halted /\ mid.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by gvs[EVERY_MEM] >>
  `(ctx_has_dalloca ctx ==>
     !pre i post v. code = (pre ++ [i]) ++ post /\
       run_inst_seq pre (mid with vs_inst_idx := SUC s.vs_inst_idx) = OK v ==>
       dalloca_no_wrap i v)` by
    (pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, APPEND] >>
     MATCH_MP_TAC checked_prefix_tail_cursor >> simp[] >>
     qpat_assum `ctx_has_dalloca ctx ==> !pre i post v. _` mp_tac >>
     simp[GSYM listTheory.APPEND_ASSOC]) >>
  first_x_assum (qspec_then `mid with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  disch_then (qspecl_then [`a`,`t with vs_inst_idx := SUC s.vs_inst_idx`,`ctx`,`func`,`bb`] mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, run_inst_seq_mem_ok_inst_idx] >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `j` strip_assume_tac) >>
  qexists_tac `j` >> conj_tac
  >- (rename1 `get_instruction bb u.vs_inst_idx = SOME i` >>
      qexistsl_tac [`i`,`u`] >> simp[]) >>
  rpt strip_tac >> gvs[inst_seq_ptr_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (mid with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G h mid, step_taint h s mid tn)` by
    (drule_all straight_line_origin_ptr_edge >> simp[]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >> simp[] >>
  disch_then irule >> first_x_assum irule >> simp[]
QED

Resume run_inst_seq_abort_origin_ptr_cursor[abort]:
  qexists_tac `t.vs_inst_idx` >> simp[] >> conj_tac
  >- (qexistsl_tac [`h`,`s`] >> simp[]) >>
  rpt strip_tac >> gvs[inst_seq_ptr_def] >>
  irule (cj 3 gas_origin_ptr_path_rules) >> simp[exit_result_def] >>
  `step_inst 0 ctx h s = Abort a t` by simp[step_inst_non_invoke] >>
  simp[gas_origin_ptr_edge_def] >> conj_tac
  >- (simp[gas_origin_edge_def] >> qexists_tac `0` >>
      simp[gas_events_step_def, mem_safe_step_non_invoke, exit_result_def]) >>
  simp[gas_path_ptr_edge_def] >> qexists_tac `0` >>
  simp[gas_count_step_def, ptr_safe_step_def, exit_result_def]
QED
Finalise run_inst_seq_abort_origin_ptr_cursor
