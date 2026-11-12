(* Original-source operand availability precedes successful copy execution. *)
Theory readonlyInvokeCopyFwdHistoryAvailability
Ancestors
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdTraceOrigin
  readonlyInvokeCopyFwdProtectionOrigin readonlyInvokeCopyFwdOccurrenceAlias
  internalReturnCopyFwdAlias venomWf venomWfProps venomExecSemantics
  o1LowerDloadOccurrence venomState list finite_map words

Theorem ricf_located_event_operands_available:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index ==>
  ?dst sv dr z da sa db sb.
    (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode = MCOPY /\
    (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;Lit z] /\
    ricf_event_roots e current = SOME (dr,Var sv,Lit z) /\
    MEM da (fn_insts fn) /\ da.inst_opcode = ALLOCA /\
    da.inst_outputs = [dr] /\ da.inst_operands = [Lit z] /\
    MEM sa (fn_insts fn) /\ sa.inst_opcode = ALLOCA /\
    sa.inst_outputs = [sv] /\ sa.inst_operands = [Lit z] /\
    ircf_alias fn dr dst /\
    eval_operands (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands s =
      SOME [n2w db;n2w sb;z] /\
    FLOOKUP s.vs_allocas da.inst_id = SOME (db,w2n z) /\
    FLOOKUP s.vs_allocas sa.inst_id = SOME (sb,w2n z) /\
    FLOOKUP H dst = SOME (a,da.inst_id) /\
    FLOOKUP H sv = SOME (a,sa.inst_id) /\
    FLOOKUP B (a,da.inst_id) = SOME (db,w2n z) /\
    FLOOKUP B (a,sa.inst_id) = SOME (sb,w2n z) /\
    (!fuel. step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s =
      OK (mcopy (w2n (n2w db : bytes32)) (w2n (n2w sb : bytes32)) (w2n z) s))
Proof
  strip_tac >>
  drule occurrence_alias_reachable >> simp[] >> strip_tac >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  `MEM (EL b fn.fn_blocks) fn.fn_blocks` by simp[EL_MEM] >>
  `e.rfe_ctx.icf_dfg = dfg_build_function round` by simp[] >>
  drule_all ricf_later_round_alloca_witnesses >> strip_tac >>
  `frame_reachable vs C stk PG G tn fn
     (ricf_event_copy e (EL b fn.fn_blocks)) s` by
    metis_tac[occ_frame_reachable_projection] >>
  `ircf_alias_site_value fn s G dst /\ ircf_alias_site_value fn s G sv` by
    (conj_tac >> irule ircf_alias_reachable_operand >>
     goal_assum (drule_at Any) >> simp[]) >>
  `?db. lookup_var dst s = SOME (n2w db) /\
    FLOOKUP s.vs_allocas da.inst_id = SOME (db,w2n sz)` by
    metis_tac[ircf_alias_site_value_def] >>
  `?sb. lookup_var sv s = SOME (n2w sb) /\
    FLOOKUP s.vs_allocas sa.inst_id = SOME (sb,w2n sz)` by
    metis_tac[ircf_alias_site_value_def] >>
  `FLOOKUP H dst = SOME (a,da.inst_id) /\
   FLOOKUP H sv = SOME (a,sa.inst_id)` by
    (`MEM (Var dst) (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands /\
      MEM (Var sv) (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands` by simp[] >>
     `(ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode <> PHI` by simp[] >>
     metis_tac[occurrence_alias_reachable_operand]) >>
  `FLOOKUP B (a,da.inst_id) = SOME (db,w2n sz) /\
   FLOOKUP B (a,sa.inst_id) = SOME (sb,w2n sz)` by
    metis_tac[occ_frame_reachable_annotation, occurrence_annotation_ok_def,
              occurrence_allocas_ok_def] >>
  qexistsl_tac [`dst`,`sv`,`dr`,`sz`,`da`,`sa`,`db`,`sb`] >>
  simp[eval_operands_def, eval_operand_def, Once step_inst_def, step_inst_base_def]
QED
