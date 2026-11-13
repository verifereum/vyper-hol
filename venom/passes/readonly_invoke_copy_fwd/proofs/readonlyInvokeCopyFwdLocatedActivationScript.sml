(* Actual relational copy activation.  Phase protection is deliberately explicit;
   translation protection and source-byte equality are produced from history. *)
Theory readonlyInvokeCopyFwdLocatedActivation
Ancestors
  readonlyInvokeCopyFwdCopyFrontier readonlyInvokeCopyFwdGlobalSupport
  readonlyInvokeCopyFwdMapCopyGuards readonlyInvokeCopyFwdHistoryAvailability
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdHistoryReadExceptions occurrenceGeometry
  internalReturnCopyFwdSim o1LowerDloadOccurrence ptrDiscipline
  venomExecSemantics venomState finite_map list pred_set words pair

Theorem ricf_located_copy_cert_activate_phase_guarded:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ssa_form fn /\ fn_inst_wf fn /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;Lit z] /\
  0 < w2n z /\ FLOOKUP H dst = SOME (a,did) /\
  FLOOKUP H sv = SOME (a,sid) /\ did IN ids /\ did <> sid /\
  occurrence_natural_geometry lo a U B stk s /\
  s.vs_alloca_next <= dimword (:256) /\
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  ricf_support_agree B E tn0 s t /\
  ricf_map_origins vs C ctx0 log stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s U B sites /\
  ricf_saved_map_origins vs C ctx0 log stk U B maps /\
  (!db. FLOOKUP B (a,did) = SOME (db,w2n z) ==>
    !gam x y w k. (gam = cur \/ MEM gam curs) /\ (x,y,w) IN gam /\ k < w ==>
      ~(db <= x+k /\ x+k < db+w2n z) /\
      ~(db <= y+k /\ y+k < db+w2n z)) /\
  nop.inst_opcode = NOP /\ nop.inst_operands = [] /\ nop.inst_outputs = [] ==>
  ?db sb un.
    FLOOKUP B (a,did) = SOME (db,w2n z) /\
    FLOOKUP B (a,sid) = SOME (sb,w2n z) /\
    un = tn0 with t_mem :=
      (tn0.t_mem DIFF {i | db <= i /\ i < db+w2n z}) UNION
      {db+q | q < w2n z /\ sb+q IN tn0.t_mem} /\
    step_inst_base (ricf_event_copy e (EL b fn.fn_blocks)) s =
      OK (mcopy db sb (w2n z) s) /\
    step_inst_base nop t = OK t /\
    ricf_cert_core D ids stk PG G
      (if s.vs_prev_bb = NONE then un else entry_taint_vars fn s un)
      fn sites maps targets G0 un (cur UNION {(db,sb,w2n z)}) curs
      (mcopy db sb (w2n z) s) t /\
    ricf_support_agree B (E UNION {(a,did)}) un (mcopy db sb (w2n z) s) t
Proof
  strip_tac >> drule_all ricf_located_event_operands_available >> strip_tac >>
  gvs[] >> (
  `db+w2n z <= s.vs_alloca_next /\ sb+w2n z <= s.vs_alloca_next` by
    metis_tac[occurrence_geometry_site_bounds] >>
  `db < dimword (:256) /\ sb < dimword (:256)` by decide_tac >>
  `db+w2n z <= sb \/ sb+w2n z <= db` by
    metis_tac[occurrence_geometry_sites_disjoint, pairTheory.PAIR_EQ] >>
  `!q. q < w2n z /\ sb+q NOTIN tn0.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory` by
    (drule_all ricf_located_event_original_destination_alloca >> strip_tac >>
     metis_tac[ricf_global_source_support_agree]) >>
  `!x y w k. (x,y,w) IN ricf_site_triples sites /\ k < w ==>
    ~(db <= x+k /\ x+k < db+w2n z) /\
    ~(db <= y+k /\ y+k < db+w2n z)` by
    metis_tac[ricf_map_origins_current_copy_exclusion, FST] >>
  `!j x y w k. j < LENGTH stk /\
    (x,y,w) IN ricf_site_triples (EL j maps) /\ k < w ==>
    ~(db <= x+k /\ x+k < db+w2n z) /\
    ~(db <= y+k /\ y+k < db+w2n z)` by
    metis_tac[ricf_saved_map_origins_current_copy_exclusion, FST] >>
  `{i | db <= i /\ i < db+w2n z} SUBSET ircf_dead ids s stk` by
    (simp[SUBSET_DEF, ircf_dead_def, site_bytes_def] >> metis_tac[]) >>
  `!j i. j < LENGTH stk /\ db <= i /\ i < db+w2n z /\
    i < (EL j stk).cf_state.vs_alloca_next ==>
    i IN ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk)` by
    metis_tac[ricf_copy_saved_observer_geometry, FST] >>
  gvs[eval_operands_def, eval_operand_def, AllCaseEqs()] >> (
  conj_tac
  >- (simp[step_inst_base_opcode_eqs, eval_operand_def] >>
      `db < dimword (:256) /\ sb < dimword (:256)` by decide_tac >> simp[]) >>
  conj_tac >- simp[step_inst_base_opcode_eqs] >>
  conj_tac
  >- (irule ricf_cert_activate_copy_frontier >>
      simp[arithmeticTheory.ADD_COMM] >> conj_tac
      >- (rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
      qexistsl_tac [`tn`, `tn0`] >> simp[]) >>
  simp[arithmeticTheory.ADD_COMM] >>
  irule (SRULE [arithmeticTheory.ADD_COMM] ricf_support_source_mcopy) >>
  metis_tac[]))
QED

(* No current phase certificates: the only residual protection premise
   disappears, while arbitrary support, translations and saved targets remain. *)
Theorem ricf_located_copy_cert_activate_empty_phase:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ssa_form fn /\ fn_inst_wf fn /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;Lit z] /\
  0 < w2n z /\ FLOOKUP H dst = SOME (a,did) /\
  FLOOKUP H sv = SOME (a,sid) /\ did IN ids /\ did <> sid /\
  occurrence_natural_geometry lo a U B stk s /\
  s.vs_alloca_next <= dimword (:256) /\
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  ricf_support_agree B E tn0 s t /\
  ricf_map_origins vs C ctx0 log stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s U B sites /\
  ricf_saved_map_origins vs C ctx0 log stk U B maps /\
  cur = {} /\ EVERY (\gam. gam = {}) curs /\
  nop.inst_opcode = NOP /\ nop.inst_operands = [] /\ nop.inst_outputs = [] ==>
  ?db sb un.
    FLOOKUP B (a,did) = SOME (db,w2n z) /\
    FLOOKUP B (a,sid) = SOME (sb,w2n z) /\
    un = tn0 with t_mem :=
      (tn0.t_mem DIFF {i | db <= i /\ i < db+w2n z}) UNION
      {db+q | q < w2n z /\ sb+q IN tn0.t_mem} /\
    step_inst_base (ricf_event_copy e (EL b fn.fn_blocks)) s =
      OK (mcopy db sb (w2n z) s) /\
    step_inst_base nop t = OK t /\
    ricf_cert_core D ids stk PG G
      (if s.vs_prev_bb = NONE then un else entry_taint_vars fn s un)
      fn sites maps targets G0 un (cur UNION {(db,sb,w2n z)}) curs
      (mcopy db sb (w2n z) s) t /\
    ricf_support_agree B (E UNION {(a,did)}) un (mcopy db sb (w2n z) s) t
Proof
  strip_tac >> irule ricf_located_copy_cert_activate_phase_guarded >>
  fs[EVERY_MEM] >> metis_tac[NOT_IN_EMPTY]
QED
