(* Project instruction checks on the inclusive request cut to raw safety. *)
Theory s1PrefixRawRequestSafety
Ancestors
  e2eRequestCutDefs ptrSafeRun memSafeRun contextRawReachable
  concretizePtrCoverageStaticMemReachability o1SafeUpto unitMemInv
  rawReachableFmp ctxLookupAgree o1PassContract lowerDloadDefs
  ptrDiscipline arithmetic words list

Theorem raw_safe_rq_upto_intro:
  EVERY (\f. fn_ptr_ok P f /\ fn_ptr_ok P (reachable_fn f)) ctx.ctx_functions /\
  fmp_free_ctx ctx /\ mem_inv dload_headroom_ok ctx vs /\
  w2n vs.vs_initial_fmp <= w2n vs.vs_fmp /\ code_layout_valid vs /\
  (!stk PG G tn fn inst s.
    frame_reachable vs ctx stk PG G tn fn inst s /\ request_cut k s ==>
    (!fuel. ptr_inst_ok D 0 fuel ctx fn G tn inst s) /\
    inst_mem_ok_in_fn fn inst s /\ inst_dload_in_section inst s /\
    dalloca_no_wrap inst s) ==>
  raw_safe_rq_upto D 0 k ctx vs
Proof
  strip_tac >> simp[raw_safe_rq_upto_def] >> conj_tac
  >- (simp[ptr_discipline_rq_upto_def] >> conj_tac
      >- (qexists_tac `P` >> simp[]) >>
      rpt gen_tac >> strip_tac >> first_x_assum drule_all >> strip_tac >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[ptr_inst_ok_def]) >>
  conj_tac
  >- (simp[taint_within_rq_upto_def] >> rpt strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      first_x_assum (qspec_then `fuel` mp_tac) >> simp[ptr_inst_ok_def]) >>
  rpt gen_tac >> strip_tac >> drule ptr_raw_reachable_frame >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >> conj_tac
  >- (simp[raw_mem_ok_def] >> conj_tac
      >- (`dload_headroom_ok ctx fn inst s` by fs[mem_inv_raw_reachable] >>
          fs[dload_headroom_ok_def] >> decide_tac) >>
      Cases_on `ctx_has_dalloca ctx`
      >- (first_x_assum (qspec_then `0` mp_tac) >>
          simp[ptr_inst_ok_def, allocas_below_fmp_def]) >>
      `EVERY pre_fmp_ops ctx.ctx_functions` by fs[fmp_free_ctx_def, EVERY_MEM] >>
      drule raw_reachable_fmp_fixed >> simp[] >> strip_tac >>
      drule raw_reachable_initial_fmp >> simp[]) >>
  drule raw_reachable_code_data >> strip_tac >>
  `LENGTH s.vs_code < dimword (:256)` by
    (irule LESS_EQ_LESS_TRANS >> qexists_tac `dimword (:256) DIV 2` >>
     gvs[code_layout_valid_def, DIV_LESS, ZERO_LT_dimword]) >>
  `LENGTH s.vs_data_section <= LENGTH s.vs_code` by
    gvs[code_layout_valid_def] >>
  pure_rewrite_tac[dload_offset_ok_def] >> rpt gen_tac >> disch_tac >>
  qpat_x_assum `inst_dload_in_section _ _` mp_tac >>
  pure_rewrite_tac[inst_dload_in_section_def] >>
  disch_then (qspecl_then [`op`, `off`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> gvs[] >> decide_tac
QED
