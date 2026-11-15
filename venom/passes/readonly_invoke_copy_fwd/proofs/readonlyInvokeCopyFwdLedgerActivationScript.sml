(* Ordinary copy activation with protection produced by retained phase history.
   Each entry may belong to a different function transformation history. *)
Theory readonlyInvokeCopyFwdLedgerActivation
Ancestors
  readonlyInvokeCopyFwdCurrentPhaseGuard readonlyInvokeCopyFwdSavedPhaseGuard
  readonlyInvokeCopyFwdLocatedActivation readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdHistoryAvailability
  occurrenceGeometry occurrenceOrigin o1LowerDloadOccurrence ptrDiscipline
  venomExecSemantics venomState finite_map list pred_set words pair

Theorem ricf_phase_ledger_copy_exclusion:
  EVERY (\entry. ?ctxP logP.
    ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B entry) ledger /\
  cur = ricf_phase_ranges 0 ledger /\
  curs = ricf_phase_stack_ranges stk ledger /\
  active_inst fn inst s /\ inst.inst_opcode = MCOPY /\
  inst.inst_operands = [Var dst;Var sv;Lit z] /\
  eval_operands inst.inst_operands s = SOME [n2w db;n2w sb;z] /\
  db < dimword(:256) /\ FLOOKUP B (a,did) = SOME (db,w2n z) /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  occurrence_syntax_origin fn a H /\
  occurrence_natural_geometry lo a U B stk s /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\
  wf_function fn /\ ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn ==>
  !gam x y w k. (gam = cur \/ MEM gam curs) /\
    (x,y,w) IN gam /\ k < w ==>
    ~(db <= x+k /\ x+k < db+w2n z) /\
    ~(db <= y+k /\ y+k < db+w2n z)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[ricf_phase_stack_ranges_def, MEM_GENLIST] >>
  gvs[ricf_phase_ranges_def] >>
  fs[EVERY_MEM]
  >- ( `?ctxP logP. ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B (p,[])`
         by metis_tac[] >>
       fs[GSYM EVERY_MEM] >>
       drule ricf_phase_entry_current_copy_exclusion >>
       simp[] >> strip_tac >> metis_tac[]) >>
  `?ctxP logP. ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B (p,pre)`
    by metis_tac[] >>
  `pre <> []` by (Cases_on `pre` >> gvs[]) >>
  drule_all ricf_phase_entry_saved_copy_exclusion >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem ricf_located_copy_cert_activate_ledger:
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
  EVERY (\entry. ?ctxP logP.
    ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B entry) ledger /\
  cur = ricf_phase_ranges 0 ledger /\
  curs = ricf_phase_stack_ranges stk ledger /\
  active_inst fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\
  wf_function fn /\
  access_ok lo G fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\
  ~in_revert_forward fn s /\
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
  strip_tac >>
  drule_all ricf_located_event_operands_available >> strip_tac >> gvs[] >>
  `db+w2n z <= s.vs_alloca_next` by
    metis_tac[occurrence_geometry_site_bounds] >>
  `db < dimword (:256)` by decide_tac >>
  `occurrence_syntax_origin fn a H` by
    metis_tac[occ_frame_reachable_origin_certificate,
              occurrence_origin_certificate_current] >>
  `!gam x y w k.
     (gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger)) /\ (x,y,w) IN gam /\ k < w ==>
     ~(db <= x+k /\ x+k < db+w2n z) /\
     ~(db <= y+k /\ y+k < db+w2n z)` by
    (drule ricf_phase_ledger_copy_exclusion >> simp[] >> metis_tac[]) >>
  drule_at (Pat `occ_frame_reachable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ricf_located_copy_cert_activate_phase_guarded >>
  simp[] >>
  disch_then (drule_at (Pat `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[arithmeticTheory.ADD_COMM] >>
  disch_then (drule_at (Pat `ricf_located_event _ _ _ _ _ _ _ _ _`)) >>
  simp[arithmeticTheory.ADD_COMM] >> strip_tac >>
  gvs[arithmeticTheory.ADD_COMM] >>
  first_x_assum (qspecl_then [`nop`,`lo`,`E`] mp_tac) >> simp[] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[]
QED
