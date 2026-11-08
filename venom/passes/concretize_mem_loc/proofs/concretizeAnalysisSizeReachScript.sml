Theory concretizeAnalysisSizeReach
Ancestors venomWfProps
  concretizeAnalysisSizes frameAllocationSizes frameOriginCache
  ptrDiscipline ptrDisciplineEmptyTaint contextCodegenRel
  venomWf venomInst venomExecSemantics removeUnusedSsaProofs list

Theorem frame_source_sizes_invariant:
  !vs0 ctx stk PG G tn fn inst s.
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) ctx.ctx_functions /\
  (!name entry. ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME entry ==>
    cache_sizes_ok (source_alloca_sizes entry) vs0) ==>
  (MEM fn ctx.ctx_functions /\ cache_sizes_ok (source_alloca_sizes fn) s) /\
  EVERY (\f. MEM f.cf_fn ctx.ctx_functions /\
    cache_sizes_ok (source_alloca_sizes f.cf_fn) f.cf_state) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume frame_source_sizes_invariant[entry]:
  rpt strip_tac >> simp[] >>
  `cache_sizes_ok (source_alloca_sizes fn) vs0` by metis_tac[] >>
  `cache_sizes_ok (source_alloca_sizes fn)
    (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)` by
    gvs[cache_sizes_ok_def] >>
  metis_tac[cache_sizes_ok_entry, lookup_function_MEM]
QED

Resume frame_source_sizes_invariant[next]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat,
         MEM_FLAT, MEM_MAP] >> metis_tac[MEM_EL]) >>
  `cache_sizes_ok (source_alloca_sizes fn) s'` by
    (irule source_alloca_sizes_step >> fs[EVERY_MEM] >> metis_tac[]) >>
  gvs[cache_sizes_ok_def]
QED

Resume frame_source_sizes_invariant[block]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat,
         MEM_FLAT, MEM_MAP] >> metis_tac[MEM_EL]) >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `cache_sizes_ok (source_alloca_sizes fn) s'` by
    (irule source_alloca_sizes_step >> fs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[cache_sizes_ok_entry]
QED

Resume frame_source_sizes_invariant[call]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac >>
  rename1 `setup_callee callee args caller_state = SOME cs` >>
  `cache_sizes_ok (source_alloca_sizes callee) cs` by
    metis_tac[source_alloca_sizes_callee] >>
  simp[] >> metis_tac[cache_sizes_ok_entry, lookup_function_MEM]
QED

Resume frame_source_sizes_invariant[ret]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac >>
  metis_tac[cache_sizes_ok_return]
QED

Finalise frame_source_sizes_invariant

Theorem frame_source_sizes_current:
  EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) ctx.ctx_functions /\
  (!name entry. ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME entry ==>
    cache_sizes_ok (source_alloca_sizes entry) vs0) /\
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  cache_sizes_ok (source_alloca_sizes fn) s
Proof
  metis_tac[frame_source_sizes_invariant]
QED

Theorem frame_source_sizes_saved:
  EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) ctx.ctx_functions /\
  (!name entry. ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME entry ==>
    cache_sizes_ok (source_alloca_sizes entry) vs0) /\
  frame_reachable vs0 ctx stk PG G tn fn inst s /\ MEM f stk ==>
  cache_sizes_ok (source_alloca_sizes f.cf_fn) f.cf_state
Proof
  strip_tac >> drule frame_source_sizes_invariant >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem frame_source_sizes_lookup:
  EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) ctx.ctx_functions /\
  (!name entry. ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME entry ==>
    cache_sizes_ok (source_alloca_sizes entry) vs0) /\
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
  FLOOKUP (source_alloca_sizes fn) aid = SOME sz
Proof
  metis_tac[frame_source_sizes_current, cache_sizes_ok_lookup]
QED

Theorem frame_source_sizes_empty_initial:
  EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) ctx.ctx_functions /\
  vs0.vs_allocas = FEMPTY /\
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  cache_sizes_ok (source_alloca_sizes fn) s /\
  EVERY (\f. cache_sizes_ok (source_alloca_sizes f.cf_fn) f.cf_state) stk
Proof
  strip_tac >> drule frame_source_sizes_invariant >>
  simp[cache_sizes_ok_empty, EVERY_MEM] >> metis_tac[]
QED
