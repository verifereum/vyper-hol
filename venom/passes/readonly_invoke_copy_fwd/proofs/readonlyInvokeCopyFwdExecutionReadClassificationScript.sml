Theory readonlyInvokeCopyFwdExecutionReadClassification
Ancestors
  allocaFrontierBound
  readonlyInvokeCopyFwdExecutionLoads readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdOpaqueReturn
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdOperationalSupport
  readonlyInvokeCopyFwdHeterogeneousSupport readonlyInvokeCopyFwdGlobalSupport
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdHistoryVisitAccess
  readonlyInvokeCopyFwdHistoryReadExceptions readonlyInvokeCopyFwdProtectionOrigin
  readonlyInvokeCopyFwdMapCoverage
  readonlyInvokeCopyFwdValues readonlyInvokeCopyFwdRel
  occurrenceGeometry occurrenceAccess occurrenceOrigin
  o1LowerDloadOccurrence o1LowerDloadRelocationKernel o1LowerDloadGhost venomWfProps venomWf
  o1LowerDloadRangeTransport o1LowerDloadPtrDiscipline o1LowerDloadJointMemoryRead
  frameViewFacts venomInst
  internalReturnCopyFwdSim ptrDiscipline taintAgree memLocDefs
  venomExecSemantics venomExecProps venomState codegenRel contextCodegenRel
  finite_map list pred_set words

Theorem ricf_execution_current_support_read_provenance:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  mem_read_ops inst = SOME ops /\
  id IN E /\ FST id = a /\ FLOOKUP B id = SOME (db,sz) /\ 0 < sz ==>
  op_prov G ops.iao_ofst <> SOME (db,sz)
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
   ricf_heterogeneous_support_origins vs C a fn U stk B E` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    metis_tac[occ_frame_reachable_annotation] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions` by
    metis_tac[occ_frame_reachable_projection, frame_reachable_prov_support] >>
  `ssa_form fn /\ fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
   ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    (fs[EVERY_MEM, wf_ssa_def, wf_function_def, fn_inst_ids_distinct_def,
       fn_insts_def, fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o,
       combinTheory.o_DEF] >> metis_tac[]) >>
  `?ctxP log p pstk RPG RG RT.
    ricf_history_origin vs C ctxP log p pstk RPG RG RT /\
    p.rpe_dst = id /\ FLOOKUP B id = SOME (p.rpe_db,p.rpe_size) /\
    ricf_live_owner_function a fn U stk (FST id) p.rpe_fn` by
    (fs[ricf_heterogeneous_support_origins_def] >> metis_tac[]) >>
  `p.rpe_fn = fn` by metis_tac[ricf_live_owner_function_current] >>
  `ssa_form p.rpe_fn /\ fn_inst_wf p.rpe_fn /\
   ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts p.rpe_fn)) /\
   ricf_full_alloca_copies p.rpe_fn /\ ricf_src_alloca p.rpe_fn` by metis_tac[] >>
  drule_all ricf_history_origin_original_allocas >> strip_tac >>
  rename1 `(ricf_event_copy p.rpe_event p.rpe_block).inst_operands =
    [Var dst;Var sv;Lit copy_size]` >>
  `p.rpe_owner = a /\ (db,sz) = (p.rpe_db,p.rpe_size)` by
    (gvs[] >> metis_tac[pairTheory.FST]) >>
  `occurrence_syntax_origin fn a H` by
    (drule occ_frame_reachable_origin_certificate >>
     simp[occurrence_origin_certificate_def]) >>
  `?cb. cb < LENGTH fn.fn_blocks /\
    s.vs_inst_idx < LENGTH (EL cb fn.fn_blocks).bb_instructions /\
    inst = EL s.vs_inst_idx (EL cb fn.fn_blocks).bb_instructions` by
    (fs[active_inst_def] >>
     `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
     metis_tac[MEM_EL]) >>
  `op_prov H ops.iao_ofst <> SOME id` by
    (fs[ricf_history_origin_def] >> gvs[] >>
     mp_tac (Q.INST [`original` |-> `p.rpe_fn`, `ai` |-> `da`, `cb` |-> `cb`,
       `ctx0` |-> `ctxP`, `e` |-> `p.rpe_event`, `a` |-> `FST p.rpe_dst`,
       `i` |-> `s.vs_inst_idx`,
       `old` |-> `EL s.vs_inst_idx (EL cb p.rpe_fn.fn_blocks).bb_instructions`,
       `dst` |-> `dst`, `src` |-> `Var sv`, `sz` |-> `Lit copy_size`]
       ricf_located_event_original_read_exclusion) >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  `occurrence_natural_geometry lo a U B stk s /\
   occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G` by
    (fs[occurrence_annotation_ok_def] >>
     metis_tac[occ_frame_reachable_geometry, ptr_discipline_def]) >>
  metis_tac[occurrence_geometry_op_positive_key]
QED



Theorem ricf_execution_current_support_read_exclusion:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  id IN E /\ FST id = a /\ FLOOKUP B id = SOME (db,sz) /\
  MEM (off,len) (source_memory_read_ranges inst s) /\ k < sz ==>
  ~(off <= db+k /\ db+k < off+len)
Proof
  strip_tac >>
  `0 < sz` by decide_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `occurrence_natural_geometry lo a U B stk s /\
   occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G /\ access_ok lo G fn inst s` by
    (drule occ_frame_reachable_annotation >>
     simp[occurrence_annotation_ok_def] >> strip_tac >>
     metis_tac[occ_frame_reachable_geometry, ptr_discipline_def,
       occ_frame_reachable_projection]) >>
  `!ops. mem_read_ops inst = SOME ops ==> op_prov G ops.iao_ofst <> SOME (db,sz)` by
    (rpt gen_tac >> strip_tac >> irule ricf_execution_current_support_read_provenance >>
     simp[] >> metis_tac[]) >>
  metis_tac[occurrence_access_read_exclusion]
QED

Theorem ricf_execution_unmapped_support_read_exclusion:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_mapped_support a B E PG G sites /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = addr /\
  op_prov G addr = SOME (db,sz) /\ FLOOKUP sites (db,sz) = NONE /\
  MEM (off,len) (source_memory_read_ranges inst s) ==>
  !i. off <= i /\ i < off+len ==> i NOTIN ricf_support_bytes B E
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
  `!id b z. id IN E /\ FLOOKUP B id = SOME (b,z) /\ 0 < z ==>
      op_prov G addr <> SOME (b,z)` by
    (map_every qx_gen_tac [`id`,`b`,`z`] >> strip_tac >> Cases_on `FST id = a`
     >- metis_tac[ricf_execution_current_support_read_provenance] >>
     strip_tac >>
     `?v. addr = Var v /\ FLOOKUP G v = SOME (b,z)` by
       (Cases_on `addr` >> gvs[op_prov_def]) >>
     `(b,z) IN FDOM sites` by
       (fs[ricf_mapped_support_def] >> metis_tac[]) >>
     gvs[FLOOKUP_DEF]) >>
  rpt strip_tac >> fs[ricf_support_bytes_def] >>
  `0 < z /\ i = b+(i-b) /\ i-b < z` by decide_tac >>
  `~(off <= b+(i-b) /\ b+(i-b) < off+len)` by
    (mp_tac (Q.INST [`k` |-> `i-b`, `z` |-> `z`,
       `owners` |-> `a::MAP (\u. u.of_owner) U`]
       (INST_TYPE [alpha |-> ``:num``] occurrence_access_read_exclusion)) >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  decide_tac
QED

Theorem ricf_execution_unmapped_read:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = addr /\
  (!name. addr = Var name ==> ~retpc_var fn name) /\
  op_taint tn addr = {} /\ eval_operand addr s = SOME x /\
  op_prov G addr = SOME (db,sz) /\ FLOOKUP sites (db,sz) = NONE /\
  MEM (w2n x,len) (source_memory_read_ranges inst s) /\ len <> 0 /\
  (!i. w2n x <= i /\ i < w2n x+len ==> i NOTIN ricf_support_bytes B E) ==>
  eval_operand addr t = SOME x /\
  (!k. k < len /\ w2n x+k NOTIN tn.t_mem ==>
    read_byte (w2n x+k) s.vs_memory = read_byte (w2n x+k) t.vs_memory)
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
   ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
     sites (ricf_complete_params PG s.vs_params) G tn s t /\
   ricf_support_agree B E tn s t` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[occ_frame_reachable_projection] >>
  `access_ok lo G fn inst s /\ lo <= vs.vs_alloca_next` by
    metis_tac[ptr_discipline_def] >>
  `occurrence_natural_geometry lo a U B stk s` by
    metis_tac[occ_frame_reachable_geometry] >>
  `?name. addr = Var name /\ FLOOKUP G name = SOME (db,sz)` by
    (Cases_on `addr` >> gvs[op_prov_def]) >>
  `db <= w2n x /\ w2n x+len <= db+sz` by
    metis_tac[access_ok_read_site_bounds] >>
  `sz <> 0` by decide_tac >>
  `?id. FLOOKUP B id = SOME (db,sz)` by
    (drule occ_frame_reachable_annotation >>
     simp[occurrence_annotation_ok_def, occurrence_env_ok_def] >> strip_tac >>
     `name IN FDOM G` by fs[FLOOKUP_DEF] >>
     `name IN FDOM H` by metis_tac[] >>
     `?id. FLOOKUP H name = SOME id` by fs[FLOOKUP_DEF] >> metis_tac[]) >>
  `w2n x+len <= s.vs_alloca_next` by
    metis_tac[occurrence_geometry_site_bounds, arithmeticTheory.LESS_EQ_TRANS] >>
  `eval_operand addr t = SOME x` by
    (drule_all (Q.INST [`op` |-> `addr`] ricf_opaque_frame_operand) >> strip_tac >>
     `ld_value_agree sites NONE {} x y` by
       gvs[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
         ricf_value_agree_def, FLOOKUP_DEF] >>
     imp_res_tac ld_value_agree_clean >> gvs[]) >>
  simp[] >> rpt strip_tac >>
  fs[ricf_support_agree_def] >>
  qpat_x_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >>
  simp[]
QED

Theorem ricf_execution_read_bytes:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_mapped_support a B E PG G sites /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = addr /\
  (!name. addr = Var name ==> ~retpc_var fn name) /\
  op_taint tn addr = {} /\ eval_operand addr s = SOME x /\
  MEM (w2n x,len) (source_memory_read_ranges inst s) ==>
  ?y. eval_operand addr t = SOME y /\
    (!k. k < len /\ w2n x+k NOTIN tn.t_mem ==>
      read_byte (w2n x+k) s.vs_memory = read_byte (w2n y+k) t.vs_memory)
Proof
  strip_tac >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  Cases_on `len = 0`
  >- (drule_all (Q.INST [`op` |-> `addr`] ricf_opaque_frame_operand) >>
      strip_tac >> qexists_tac `y` >> simp[]) >>
  Cases_on `op_prov G addr = NONE`
  >- (`eval_operand addr t = SOME x` by
        (drule_all (Q.INST [`op` |-> `addr`] ricf_opaque_frame_operand) >> strip_tac >>
         `x = y` by
           (irule ld_value_agree_clean >> qexists_tac `sites` >>
            gvs[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
              ricf_value_agree_def]) >> gvs[]) >>
      qexists_tac `x` >> simp[] >>
      mp_tac (Q.INST [`off` |-> `w2n (x:256 word)`]
        ricf_execution_unprovenanced_read) >>
      (impl_tac >- simp[]) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `?db sz. op_prov G addr = SOME (db,sz)` by
    (Cases_on `op_prov G addr` >> gvs[] >>
     rename1 `op_prov G addr = SOME key` >> Cases_on `key` >> metis_tac[]) >>
  Cases_on `FLOOKUP sites (db,sz) = NONE`
  >- (`!i. w2n x <= i /\ i < w2n x+len ==> i NOTIN ricf_support_bytes B E` by
        (mp_tac (Q.INST [`off` |-> `w2n (x:256 word)`]
           ricf_execution_unmapped_support_read_exclusion) >>
         (impl_tac >- simp[]) >> simp[]) >>
      mp_tac ricf_execution_unmapped_read >> (impl_tac >- simp[]) >>
      strip_tac >> qexists_tac `x` >> simp[]) >>
  `?sb. FLOOKUP sites (db,sz) = SOME (db,sb,sz)` by
    (fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def, ricf_sites_ok_def] >>
     Cases_on `FLOOKUP sites (db,sz)` >> gvs[] >>
     rename1 `FLOOKUP sites (db,sz) = SOME tr` >> PairCases_on `tr` >> metis_tac[]) >>
  drule_all ricf_execution_relocated_read >> strip_tac >>
  qexists_tac `y` >> simp[] >> qx_gen_tac `k` >> strip_tac >>
  qpat_x_assum `!k. k < len ==> _` (qspec_then `k` mp_tac) >>
  `w2n x+k = db+(delta+k) /\ w2n y+k = delta+(k+sb)` by decide_tac >>
  metis_tac[]
QED

Theorem ricf_execution_observer_read:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_mapped_support a B E PG G sites /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [SHA3;LOG;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = addr /\
  (!name. addr = Var name ==> ~retpc_var fn name) /\
  op_taint tn addr = {} /\ eval_operand addr s = SOME x /\
  MEM (w2n x,len) (source_memory_read_ranges inst s) ==>
  ?y. eval_operand addr t = SOME y /\
    read_memory (w2n x) len s = read_memory (w2n y) len t
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `!k. k < len ==> w2n x+k NOTIN tn.t_mem` by
    (rpt strip_tac >>
     `w2n x <= w2n x+k /\ w2n x+k < w2n x+len` by decide_tac >>
     fs[MEM] >> gvs[taint_ok_def, about_to_revert_def] >>
     qpat_x_assum `!off len i. _`
       (qspecl_then [`w2n (x:256 word)`,`len`,`w2n (x:256 word)+k`] mp_tac) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  drule_all ricf_execution_read_bytes >> strip_tac >>
  qexists_tac `y` >> simp[] >> irule read_memory_eq_from_bytes >>
  metis_tac[]
QED
