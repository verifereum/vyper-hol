Theory readonlyInvokeCopyFwdExecutionWriteClassification
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHeterogeneousMapOrigins
  readonlyInvokeCopyFwdAlignedOrigins readonlyInvokeCopyFwdReadonlyReach
  readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdHistoryVisitAccess readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdReadonlyContract readonlyInvokeCopyFwdOperationalSupport
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdValues
  o1LowerDloadOccurrence o1LowerDloadGhost o1LowerDloadPtrDiscipline
  o1LowerDloadRelocationKernel occurrenceGeometry occurrenceAccess occurrenceOrigin
  venomWfProps venomWf venomExecProps venomInst
  ptrDiscipline taintAgree venomState finite_map list pred_set words

Theorem ricf_analyzed_translation_origin_write_exclusion:
  ricf_aligned_translation_origin vs C ctxP log stk PG G tn fn inst s U B key tr /\
  ctxP.icf_rma = readonly_mem_analyze C /\
  o1_ctx_shape C /\ ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  mem_write_ops inst = SOME ops ==>
  op_prov G ops.iao_ofst <> SOME key
Proof
  strip_tac >>
  `EVERY (readonly_origin_contract (rma_is_readonly (readonly_mem_analyze C))
    (ricf_analysis_origins C)) C.ctx_functions` by
    metis_tac[ricf_analysis_readonly_origin_contract] >>
  fs[ricf_aligned_translation_origin_def, ricf_aligned_origin_at_def] >>
  metis_tac[readonly_call_reachable_no_write]
QED



Theorem ricf_execution_write_address_unmapped:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
  o1_ctx_shape C /\ ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  mem_write_ops inst = SOME ops /\ op_prov G ops.iao_ofst = SOME key ==>
  FLOOKUP sites key = NONE
Proof
  strip_tac >> Cases_on `FLOOKUP sites key` >> simp[] >>
  fs[ricf_analyzed_map_origins_def] >>
  metis_tac[ricf_analyzed_translation_origin_write_exclusion]
QED

Theorem ricf_execution_write_address_same:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
  o1_ctx_shape C /\ ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = addr /\
  (!name. addr = Var name ==> ~retpc_var fn name) /\
  op_taint tn addr = {} /\ eval_operand addr s = SOME x /\
  MEM (w2n x,len) (source_memory_write_ranges inst s) /\ 0 < len ==>
  eval_operand addr t = SOME x
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `access_ok lo G fn inst s` by metis_tac[ptr_discipline_def] >>
  `~ricf_is_zero_prov (op_prov G addr)` by
    (strip_tac >> fs[ricf_is_zero_prov_def] >>
     `?v b. addr = Var v /\ FLOOKUP G v = SOME (b,0)` by
       (Cases_on `addr` >> gvs[op_prov_def] >> metis_tac[]) >>
     gvs[op_prov_def] >>
     `len <> 0` by decide_tac >>
     drule_all access_ok_write_site_bounds >> simp[] >> decide_tac) >>
  `!key. op_prov G addr = SOME key ==> FLOOKUP sites key = NONE` by
    metis_tac[ricf_execution_write_address_unmapped] >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  drule_all (Q.INST [`op` |-> `addr`] ricf_opaque_frame_operand) >> strip_tac >>
  `ld_value_agree sites NONE {} x y` by
    (Cases_on `op_prov G addr` >>
     gvs[ricf_opaque_value_agree_def, ricf_value_agree_def, FLOOKUP_DEF]) >>
  imp_res_tac ld_value_agree_clean >> gvs[]
QED

Theorem ricf_execution_write_address:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
  o1_ctx_shape C /\ ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = addr /\
  (!name. addr = Var name ==> ~retpc_var fn name) /\
  op_taint tn addr = {} /\ eval_operand addr s = SOME x /\
  MEM (w2n x,len) (source_memory_write_ranges inst s) ==>
  ?y. eval_operand addr t = SOME y /\ (len = 0 \/ x = y)
Proof
  strip_tac >> Cases_on `len = 0`
  >- (`ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
        sites (ricf_complete_params PG s.vs_params) G tn s t` by
        fs[ricf_execution_invariant_def] >>
      drule_all (Q.INST [`op` |-> `addr`] ricf_opaque_frame_operand) >>
      strip_tac >> qexists_tac `y` >> simp[]) >>
  qexists_tac `x` >> simp[] >>
  `0 < len` by decide_tac >>
  drule ricf_execution_write_address_same >> disch_then irule >>
  simp[] >> metis_tac[]
QED

Theorem ricf_analyzed_translation_origin_write_ranges:
  ricf_aligned_translation_origin vs C ctxP log stk PG G tn fn inst s U B
    key (db,sb,sz) /\ ctxP.icf_rma = readonly_mem_analyze C /\
  o1_ctx_shape C /\ ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  occurrence_natural_geometry lo a U B stk s /\
  occurrence_env_ok B owners H G /\ access_ok lo G fn inst s /\
  ~in_revert_forward fn s /\
  MEM (off,len) (source_memory_write_ranges inst s) /\ k < sz ==>
  ~(off <= db+k /\ db+k < off+len) /\
  ~(off <= sb+k /\ sb+k < off+len)
Proof
  strip_tac >>
  `EVERY (readonly_origin_contract (rma_is_readonly (readonly_mem_analyze C))
    (ricf_analysis_origins C)) C.ctx_functions` by
    metis_tac[ricf_analysis_readonly_origin_contract] >>
  fs[ricf_aligned_translation_origin_def, ricf_aligned_origin_at_def] >>
  `(!ops. mem_write_ops inst = SOME ops ==>
      op_prov G ops.iao_ofst <> SOME (p.rpe_db,p.rpe_size)) /\
   (!ops. mem_write_ops inst = SOME ops ==>
      op_prov G ops.iao_ofst <> SOME (p.rpe_sb,p.rpe_size))` by
    metis_tac[readonly_call_reachable_no_write] >>
  metis_tac[occurrence_access_write_exclusion, arithmeticTheory.ADD_COMM]
QED

Theorem ricf_execution_map_write_ranges:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
  ricf_analyzed_saved_map_origins vs C stk PG G tn fn inst s U B maps /\
  o1_ctx_shape C /\ ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  MEM (off,len) (source_memory_write_ranges inst s) /\
  (gam = ricf_site_triples sites \/
    ?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) /\
  (db,sb,sz) IN gam /\ k < sz ==>
  ~(off <= db+k /\ db+k < off+len) /\
  ~(off <= sb+k /\ sb+k < off+len)
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `occurrence_natural_geometry lo a U B stk s /\
   occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G /\ access_ok lo G fn inst s` by
    (drule occ_frame_reachable_annotation >>
     simp[occurrence_annotation_ok_def] >> strip_tac >>
     metis_tac[occ_frame_reachable_geometry, ptr_discipline_def,
       occ_frame_reachable_projection]) >>
  `?ctxP log. ctxP.icf_rma = readonly_mem_analyze C /\
    ricf_aligned_translation_origin vs C ctxP log stk PG G tn fn inst s U B
      (db,sz) (db,sb,sz)` by
    (gvs[ricf_site_triples_def, ricf_analyzed_map_origins_def,
        ricf_analyzed_saved_map_origins_def] >>
     res_tac >>
     fs[ricf_aligned_translation_origin_def, ricf_aligned_origin_at_def] >>
     metis_tac[]) >>
  metis_tac[ricf_analyzed_translation_origin_write_ranges]
QED

Theorem ricf_execution_current_phase_write_ranges:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM (off,len) (source_memory_write_ranges inst s) /\
  (db,sb,sz) IN ricf_phase_ranges 0 ledger /\ k < sz ==>
  ~(off <= db+k /\ db+k < off+len) /\
  ~(off <= sb+k /\ sb+k < off+len)
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
   EVERY (\entry. ?ctxP logP.
      ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B entry) ledger` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `?p ctxP logP. MEM (p,[]) ledger /\
    ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B (p,[]) /\
    db = p.rpe_db /\ sb = p.rpe_sb /\ sz = p.rpe_size` by
    (fs[ricf_phase_ranges_def, EVERY_MEM] >> metis_tac[LENGTH_NIL]) >>
  `ricf_history_cursor vs C ctxP logP p [] PG G tn fn s /\
   a = p.rpe_owner /\
   FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
   FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\ 0 < p.rpe_size` by
    fs[ricf_phase_entry_def] >>
  `p.rpe_fn = fn` by metis_tac[ricf_history_cursor_owner_function] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions` by
    metis_tac[occ_frame_reachable_projection, frame_reachable_prov_support] >>
  `wf_function p.rpe_fn /\ ssa_form p.rpe_fn /\ fn_inst_wf p.rpe_fn /\
   ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts p.rpe_fn)) /\
   ricf_full_alloca_copies p.rpe_fn /\ ricf_src_alloca p.rpe_fn` by
    (fs[EVERY_MEM, wf_ssa_def, wf_function_def, fn_inst_ids_distinct_def,
       fn_insts_def, fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o,
       combinTheory.o_DEF] >> metis_tac[]) >>
  `occurrence_annotation_ok n a U B HP H stk PG G s /\
   occurrence_syntax_origin fn a H /\
   occurrence_natural_geometry lo a U B stk s /\ access_ok lo G fn inst s` by
    metis_tac[occ_frame_reachable_annotation,
      occ_frame_reachable_origin_certificate, occurrence_origin_certificate_def,
      occ_frame_reachable_geometry, occ_frame_reachable_projection,
      ptr_discipline_def] >>
  gvs[] >> `0 < p.rpe_size` by decide_tac >>
  mp_tac (Q.INST [`ctx0` |-> `ctxP`, `log` |-> `logP`, `fn` |-> `p.rpe_fn`,
    `db` |-> `p.rpe_db`, `sb` |-> `p.rpe_sb`, `z` |-> `p.rpe_size`]
    ricf_history_cursor_owner_write_ranges) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`off`,`len`,`k`] mp_tac) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
