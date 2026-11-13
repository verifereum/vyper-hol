Theory concretizeLayoutRequestBase
Ancestors concretizeLayoutRequestRelations concretizeLayoutCanonicalBaseCertificate
  concretizeLayoutCanonicalBaseExternal concretizeLayoutCanonicalBase
  concretizeLayoutCanonicalDriver concretizeLayoutPhaseOrigin
  concretizeMemLocDefs concretizeStepStructure oracleExecProps
  concretizeLayoutPhaseCorridor frameRankedTerminalCorridor
  frameSelectedSimulation frameFiniteExecution venomExecSemantics ptrDiscipline list

(* The paired instruction is identical in a corridor, including its opcode. *)
Theorem layout_canonical_corridor_instructions:
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INR g) ==> i = j
Proof
  simp[layout_canonical_step_witness_def, layout_canonical_block_witness_def] >>
  strip_tac >> gvs[] >>
  fs[layout_corridor_entry_def, layout_phase_normalize_def,
     ranked_terminal_entry_def, ranked_terminal_corridor_def] >>
  Cases_on `g.ltp_remaining = 0` >- gvs[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >> gvs[]
QED

Theorem concretize_positions_external_opcodes:
  MEM (concretize_inst_with_positions positions i).inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] <=>
  MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]
Proof
  simp[concretize_inst_with_positions_def] >>
  Cases_on `i.inst_opcode = ALLOCA` >> simp[] >>
  Cases_on `i.inst_outputs` >> simp[] >>
  rename1 `_ :: outs` >> Cases_on `outs` >> simp[] >>
  Cases_on `FLOOKUP positions (Allocation i.inst_id)` >>
  simp[passSharedDefsTheory.mk_nop_inst_def,
       passSharedDefsTheory.mk_assign_inst_def]
QED

Theorem layout_canonical_external_opcodes:
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t a ==>
  (MEM j.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] <=>
   MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2])
Proof
  strip_tac >> Cases_on `a`
  >- (drule layout_canonical_ordinary_step_witness >> strip_tac >>
      gvs[concretize_positions_external_opcodes]) >>
  drule layout_canonical_corridor_instructions >> simp[]
QED

(* Deterministic base execution lets an independent request boundary attach
   to the concrete target witness chosen by the existing certificate. *)
Theorem layout_request_nonexternal_success:
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t a /\ layout_request_state D s t /\
  ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  step_inst_base i s = OK post /\ step_inst_base j t = OK tpost ==>
  layout_request_state D post tpost
Proof
  strip_tac >> drule layout_canonical_external_opcodes >> strip_tac >>
  `post.vs_requests = s.vs_requests /\ tpost.vs_requests = t.vs_requests` by
    (fs[MEM] >> metis_tac[step_inst_base_oracle]) >>
  metis_tac[layout_request_state_fields]
QED

Theorem layout_request_base_lift:
  selected_base_certificate C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend) /\
  (!fn q n i s j t r r'.
    decoration_at fn i s q /\ i.inst_opcode <> INVOKE /\
    layout_request_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t /\
    step_inst_base i s = r /\ step_inst_base j t = r' /\
    (!e. r <> Error e) /\
    layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend q n q n i s j t r r' ==>
    layout_request_guard D r r') ==>
  selected_base_certificate C C' q0 path
    (layout_request_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_OS D lo vs0 C C' q0 path es qs ass qend)
Proof
  rewrite_tac[selected_base_certificate_def, selected_step_match_def] >>
  rpt strip_tac >>
  `layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t` by
    metis_tac[layout_request_ES_forget] >>
  first_x_assum drule_all >> simp[] >> strip_tac >>
  rename1 `finite_step C' j t r'` >>
  `j.inst_opcode <> INVOKE` by
    (fs[layout_canonical_ES_def] >>
     metis_tac[layout_canonical_step_witness_not_invoke]) >>
  `step_inst_base j t = r'` by
    (qpat_x_assum `finite_step C' j t r'` mp_tac >>
     simp[Once finite_step_cases]) >>
  qexists `r'` >> simp[layout_request_OS_def] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem layout_request_base_certificate:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  dead_wf D /\ taint_within D C vs0 /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  (!inst s a post. step_inst_base inst s = Abort a post ==>
    post.vs_requests = s.vs_requests) ==>
  selected_base_certificate C C' q0 path
    (layout_request_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_OS D lo vs0 C C' q0 path es qs ass qend)
Proof
  strip_tac >> match_mp_tac layout_request_base_lift >> conj_tac
  >- (drule_all layout_canonical_base_certificate >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `layout_request_state D s t` by metis_tac[layout_request_ES_requests] >>
  `layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t` by
    metis_tac[layout_request_ES_forget] >>
  qpat_x_assum `layout_canonical_ES _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [layout_canonical_ES_def]) >>
  Cases_on `r` >> Cases_on `r'` >>
  gvs[layout_request_guard_def, concretizeLayoutCanonicalDeferredTheory.layout_deferred_noninvoke,
      layout_canonical_OS_def, layout_canonical_result_def]
  >- suspend "success"
  >> metis_tac[layout_request_state_fields]
QED

Resume layout_request_base_certificate[success]:
  rename1 `step_inst_base i s = OK post` >>
  rename1 `step_inst_base j t = OK tpost` >>
  Cases_on `MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`
  >- (Cases_on `a`
      >- (drule_at (Pat `layout_canonical_step_witness _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
            layout_canonical_external_success_requests >>
          simp[] >> strip_tac >>
          metis_tac[layout_request_state_def]) >>
      rename1 `layout_canonical_step_witness _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (INR g)` >>
      gvs[layout_canonical_step_witness_def, layout_canonical_block_witness_def,
          layout_corridor_entry_def, layout_phase_normalize_def,
          ranked_terminal_entry_def, ranked_terminal_corridor_def] >>
      Cases_on `g.ltp_remaining = 0` >- gvs[] >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[] >> gvs[]) >>
  metis_tac[layout_request_nonexternal_success]
QED

Finalise layout_request_base_certificate
