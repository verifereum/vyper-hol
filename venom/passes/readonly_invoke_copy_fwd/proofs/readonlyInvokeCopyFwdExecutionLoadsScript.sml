Theory readonlyInvokeCopyFwdExecutionLoads
Ancestors
  pointerConfinedDefs
  allocaFrontierBound
  readonlyInvokeCopyFwdExecutionLocal readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionOrdinary o1LowerDloadShared
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdSupportSeparation
  occurrenceGeometry o1LowerDloadStackFrontier o1LowerDloadJointMemoryRead
  readonlyInvokeCopyFwdOpaque frameViewFacts frameRel unitShapeDefs
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHeterogeneousMapOrigins
  readonlyInvokeCopyFwdAlignedOrigins readonlyInvokeCopyFwdEndpointBounds
  readonlyInvokeCopyFwdValues readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdMemory
  o1LowerDloadOccurrence o1LowerDloadAddressArithmetic o1LowerDloadRelocationKernel
  internalReturnCopyFwdSim unitMemInv taintAgree ptrDiscipline memLocDefs
  venomExecSemantics venomState venomInst contextCodegenRel codegenRel
  finite_map list pred_set words arithmetic

Theorem ricf_execution_fixed_read_bytes:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ off+len <= lo ==>
  !k. k < len /\ off+k NOTIN rt.t_mem ==>
    read_byte (off+k) s.vs_memory = read_byte (off+k) t.vs_memory
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
   ricf_support_agree B E rt s t` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `lo <= vs.vs_alloca_next` by fs[ptr_discipline_def] >>
  `occurrence_natural_geometry lo a U B stk s` by
    metis_tac[occ_frame_reachable_geometry] >>
  `vs.vs_alloca_next <= s.vs_alloca_next` by
    metis_tac[occ_frame_reachable_projection,
      ld_frame_reachable_current_initial_frontier] >>
  `!k. k < len ==> off+k NOTIN ricf_support_bytes B E` by
    (rpt strip_tac >> fs[ricf_support_bytes_def] >>
     `lo <= b` by metis_tac[occurrence_geometry_site_bounds] >> decide_tac) >>
  `off+len <= s.vs_alloca_next` by decide_tac >>
  mp_tac (Q.INST [`tn` |-> `rt`, `sb` |-> `off`]
    (INST_TYPE [alpha |-> ``:num # num``] ricf_support_separated_source_agree)) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ricf_execution_unprovenanced_read:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  mem_read_ops inst = SOME ops /\ op_prov G ops.iao_ofst = NONE /\
  MEM (off,len) (source_memory_read_ranges inst s) ==>
  (len = 0 \/ off+len <= lo) /\
  (!k. k < len /\ off+k NOTIN tn.t_mem ==>
    read_byte (off+k) s.vs_memory = read_byte (off+k) t.vs_memory)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `access_ok lo G fn inst s` by metis_tac[ptr_discipline_def] >>
  Cases_on `len = 0` >- simp[] >>
  `off+len <= lo` by
    (spose_not_then assume_tac >> `lo < off+len` by decide_tac >>
     `?rops v b z. mem_read_ops inst = SOME rops /\ rops.iao_ofst = Var v /\
       FLOOKUP G v = SOME (b,z) /\ b <= off /\ off+len <= b+z` by
       (gvs[access_ok_def] >> metis_tac[]) >>
     gvs[op_prov_def]) >>
  simp[] >> mp_tac (Q.INST [`rt` |-> `tn`] ricf_execution_fixed_read_bytes) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ricf_execution_zero_provenance_read_empty:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  mem_read_ops inst = SOME ops /\ ricf_is_zero_prov (op_prov G ops.iao_ofst) /\
  MEM (off,len) (source_memory_read_ranges inst s) ==> len = 0
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `access_ok lo G fn inst s` by metis_tac[ptr_discipline_def] >>
  `?name b. ops.iao_ofst = Var name /\ FLOOKUP G name = SOME (b,0)` by
    (Cases_on `ops.iao_ofst` >> gvs[ricf_is_zero_prov_def, op_prov_def]) >>
  Cases_on `len = 0` >> simp[] >>
  drule_all access_ok_read_site_bounds >> decide_tac
QED

Theorem ricf_execution_unprovenanced_observer_read:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [SHA3;LOG] /\
  mem_read_ops inst = SOME ops /\ op_prov G ops.iao_ofst = NONE /\
  MEM (off,len) (source_memory_read_ranges inst s) ==>
  read_memory off len s = read_memory off len t
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  drule_all ricf_execution_unprovenanced_read >> strip_tac >>
  irule o1LowerDloadRangeTransportTheory.read_memory_eq_from_bytes >>
  simp[] >> qx_gen_tac `k` >> strip_tac >>
  `MEM inst.inst_opcode [SHA3;LOG;CREATE;CREATE2]` by fs[MEM] >>
  `off+k NOTIN tn.t_mem` by metis_tac[taint_ok_observation_read] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ricf_execution_relocated_read:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = addr /\
  (!name. addr = Var name ==> ~retpc_var fn name) /\
  op_taint tn addr = {} /\ eval_operand addr s = SOME x /\
  op_prov G addr = SOME (db,sz) /\
  FLOOKUP sites (db,sz) = SOME (db,sb,sz) /\
  MEM (w2n x,len) (source_memory_read_ranges inst s) /\ len <> 0 ==>
  ?y delta. eval_operand addr t = SOME y /\
    w2n x = db+delta /\ w2n y = sb+delta /\ delta+len <= sz /\
    (!k. k < len ==>
      (w2n x+k IN tn.t_mem <=> w2n y+k IN tn.t_mem) /\
      (w2n x+k NOTIN tn.t_mem ==>
        read_byte (w2n x+k) s.vs_memory = read_byte (w2n y+k) t.vs_memory))
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `access_ok lo G fn inst s` by metis_tac[ptr_discipline_def] >>
  `?name. addr = Var name /\ FLOOKUP G name = SOME (db,sz)` by
    (Cases_on `addr` >> gvs[op_prov_def]) >>
  `db <= w2n x /\ w2n x+len <= db+sz` by
    metis_tac[access_ok_read_site_bounds] >>
  `sz <> 0` by decide_tac >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
     sites (ricf_complete_params PG s.vs_params) G tn s t /\
   ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B sites` by
    fs[ricf_execution_invariant_def] >>
  `?y. eval_operand addr t = SOME y /\
    ricf_value_agree sites (SOME (db,sz)) {} x y` by
    (drule_all (Q.INST [`op` |-> `addr`] ricf_opaque_frame_operand) >>
     simp[ricf_opaque_value_agree_def, ricf_is_zero_prov_def]) >>
  `db+sz < dimword (:256) /\ sb+sz < dimword (:256)` by
    (fs[ricf_heterogeneous_map_origins_def] >>
     metis_tac[ricf_aligned_translation_origin_projection,
       ricf_translation_origin_endpoint_bounds]) >>
  `y = x+n2w sb-n2w db` by
    (gvs[ricf_value_agree_def, ld_value_agree_def, FLOOKUP_DEF] >> metis_tac[]) >>
  `w2n y = sb+(w2n x-db)` by
    (qpat_assum `y = _` SUBST1_TAC >>
     irule lower_dload_translate_endpoint >> simp[] >>
     qexists_tac `sz` >> simp[] >> decide_tac) >>
  `w2n x = db+(w2n x-db) /\ (w2n x-db)+len <= sz` by decide_tac >>
  `ircf_cross tn (ricf_site_triples sites) s t /\
   (db,sb,sz) IN ricf_site_triples sites` by
    (conj_tac
     >- (fs[ricf_opaque_frame_agree_def] >> drule ricf_frame_agree_cross >> simp[]) >>
     simp[ricf_site_triples_def] >> metis_tac[]) >>
  qexistsl_tac [`y`,`w2n x-db`] >> simp[] >>
  mp_tac (Q.INST [`gam` |->
      `ricf_site_triples (sites:(num # num) |-> (num # num # num))`,
    `off` |-> `w2n (x:256 word)-db`] ricf_cross_read_bytes) >>
  impl_tac >- simp[] >> disch_tac >> qx_gen_tac `k` >> strip_tac >>
  `db+(w2n x-db)+k = k+w2n x /\
   sb+(w2n x-db)+k = k+(sb+w2n x)-db` by decide_tac >>
  metis_tac[]
QED

