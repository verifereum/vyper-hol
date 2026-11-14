Theory concretizePtrDallocaActualFresh
Ancestors
  concretizePtrHistoricalWriteExclusion concretizePtrPairedFields
  concretizePtrDallocaActualWrites concretizePtrPairedPrefix
  concretizeStepStructure codegenRel o1ContractSimplifyCfgSrcFrame unitShapeDefs
  lowerDloadOracleCallAssembly
  concretizePtrStructuralTrace concretizePtrStructuralTranscript
  concretizePtrRequestHistory concretizePtrTaintContent concretizePtrOpaqueRetpc
  concretizePtrSharedFields concretizePtrLifetime concretizePtrChronologicalHistory venomMemProofs
  ptrDiscipline venomExecSemantics venomInst opcodeClass o1PassContract venomWf
  lowerDloadPtrRawReachable list rich_list finite_map pred_set

Theorem ptr_dalloca_history_content_fmp:
  ptr_history_content tn s t ==> s.vs_fmp = t.vs_fmp
Proof
  simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def]
QED

Theorem ptr_dalloca_chrono_nop_fmp[local]:
  !C a b. ptr_chrono_step C a b ==> a.po_inst.inst_opcode = NOP ==>
    a.po_state.vs_fmp = b.po_state.vs_fmp
Proof
  ho_match_mp_tac ptr_chrono_step_ind >> simp[ptr_observe_def] >>
  rpt strip_tac >> gvs[is_terminator_def, step_inst_non_invoke, step_inst_base_def]
QED

Theorem ptr_dalloca_chrono_nop_interval_fmp:
  !hi lo. ptr_chrono_history vs0 C h a /\ lo <= hi /\ hi < LENGTH h /\
    (!k. lo <= k /\ k < hi ==> (EL k h).po_inst.inst_opcode = NOP) ==>
    (EL lo h).po_state.vs_fmp = (EL hi h).po_state.vs_fmp
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (`lo = 0` by decide_tac >> simp[]) >>
  Cases_on `lo = SUC hi` >- simp[] >>
  `lo <= hi /\ hi < LENGTH h` by decide_tac >>
  `ptr_chrono_step C (EL hi h) (EL (SUC hi) h)` by
    metis_tac[ptr_chrono_history_adjacent] >>
  `(EL hi h).po_inst.inst_opcode = NOP` by
    (first_x_assum irule >> decide_tac) >>
  drule_all ptr_dalloca_chrono_nop_fmp >> strip_tac >>
  `(EL lo h).po_state.vs_fmp = (EL hi h).po_state.vs_fmp` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  metis_tac[]
QED

Theorem ptr_dalloca_paired_post_fmp:
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries /\
  ptr_paired_samples positions h ht done H /\ q < LENGTH done ==>
  (EL (SUC (EL q done)) h).po_state.vs_fmp =
    (EL (SUC q) ht).po_state.vs_fmp
Proof
  strip_tac >>
  `SUC q < LENGTH ht` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  drule_all ptr_paired_samples_history >> strip_tac >>
  drule ptr_dalloca_history_content_fmp >> strip_tac >>
  drule_all ptr_structural_trace_nop_interval >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  metis_tac[ptr_dalloca_chrono_nop_interval_fmp]
QED

Theorem ptr_dalloca_chrono_ordinary_allocas:
  !C a b. ptr_chrono_step C a b ==>
    ~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE /\
    a.po_inst.inst_opcode <> ALLOCA ==>
    b.po_state.vs_allocas = a.po_state.vs_allocas
Proof
  ho_match_mp_tac ptr_chrono_step_ind >> rpt conj_tac >>
  simp[ptr_observe_def] >> rpt strip_tac
  >- (gvs[step_inst_non_invoke] >>
      irule step_inst_base_preserves_allocas >> qexists `inst` >> simp[]) >>
  gvs[step_inst_non_invoke] >>
  drule step_inst_base_intret_opcodes >> strip_tac >> gvs[is_terminator_def]
QED

(* No emptiness assumption is needed: an unchanged allocation map cannot
   introduce a new static site. *)
Theorem ptr_dalloca_preserved_map_fresh_bytes:
  postt.vs_allocas = t.vs_allocas /\ s.vs_fmp = t.vs_fmp /\
  posts.vs_fmp = postt.vs_fmp ==>
  new_site_bytes t postt SUBSET new_site_bytes s posts
Proof
  simp[new_site_bytes_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem ptr_dalloca_departed_no_alloca:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ q < LENGTH done /\
  a = EL (EL q done) h /\ t = EL q ht ==>
  t.po_inst.inst_opcode <> ALLOCA
Proof
  strip_tac >> drule ptr_paired_prefix_samples >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  `q < LENGTH ht /\ EL q done < LENGTH h` by
    fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_EL] >>
  drule_all ptr_paired_prefix_alignment >> strip_tac >>
  `ptr_observation_reachable vs C a` by
    (drule ptr_structural_trace_source >>
     disch_then (mp_tac o MATCH_MP ptr_chrono_history_reachable) >>
     simp[EVERY_MEM] >> strip_tac >> first_x_assum irule >>
     simp[MEM_EL] >> qexists `EL q done` >> simp[]) >>
  `MEM a.po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >>
     drule_all frame_reachable_raw_certificate >> simp[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[ptr_observation_reachable_def] >>
     drule scfg_frame_reachable_active >>
     metis_tac[ld_active_inst_member]) >>
  `inst_wf a.po_inst /\ fn_inst_ids_distinct a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_inst_wf_def,
        fn_shape_ok_def, wf_function_def,
        fn_insts_def, fn_insts_blocks_MEM, EVERY_MEM] >> metis_tac[]) >>
  `a.po_inst.inst_id = t.po_inst.inst_id` by
    (drule ptr_trace_departed_inst_ids >>
     disch_then (qspec_then `q` mp_tac) >> simp[]) >>
  `t.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst` by
    gvs[EL_APPEND_EQN, ptr_departed_cursor_instruction] >>
  metis_tac[concretize_positions_inst_no_alloca]
QED

Theorem ptr_dalloca_actual_fresh_bytes:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ q < LENGTH done /\
  a = EL (EL q done) h /\ t = EL q ht /\
  posts = (EL (SUC (EL q done)) h).po_state /\
  postt = (EL (SUC q) ht).po_state /\
  ~is_terminator t.po_inst.inst_opcode /\ t.po_inst.inst_opcode <> INVOKE ==>
  new_site_bytes t.po_state postt SUBSET new_site_bytes a.po_state posts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `t.po_inst.inst_opcode <> ALLOCA` by
    (drule_all ptr_dalloca_departed_no_alloca >> simp[]) >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  `SUC q < LENGTH ht /\ q < LENGTH ht` by
    fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  `a.po_state.vs_fmp = t.po_state.vs_fmp` by
    (drule ptr_paired_samples_history >>
     disch_then (qspec_then `q` mp_tac) >>
     simp[EL_APPEND_EQN] >> metis_tac[ptr_dalloca_history_content_fmp]) >>
  `posts.vs_fmp = postt.vs_fmp` by
    metis_tac[ptr_dalloca_paired_post_fmp] >>
  `ptr_chrono_step C' t (EL (SUC q) ht)` by
    (drule ptr_structural_trace_target >> strip_tac >>
     metis_tac[ptr_chrono_history_adjacent]) >>
  `postt.vs_allocas = t.po_state.vs_allocas` by
    metis_tac[ptr_dalloca_chrono_ordinary_allocas] >>
  irule ptr_dalloca_preserved_map_fresh_bytes >> simp[]
QED
