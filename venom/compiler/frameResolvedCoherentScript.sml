Theory frameResolvedCoherent
Ancestors venomWfProps frameResolvedReturn frameResolvedTrace frameJointTrace frameActivationLifetime
  frameJointTransition frameOriginCache venomExecSemantics venomInst
  ptrDisciplineEmptyTaint venomMemProps frameOriginHistory frameOriginReachable
  frameAllocationOwnership frameHistoryDefinitions ptrDiscipline
  contextCodegenRel removeUnusedSsaProofs arithmetic finite_map list pred_set

(* The update is intentionally stronger than pointwise resolved validity.
   Only the current annotation changes, except at an actual push or pop. *)
Inductive resolved_annotation_update:
[~call:]
  (!stk PG G tn fn inst s oms om hs h name ops ids ann saved.
    decode_invoke inst = SOME (name,ops) ==>
    resolved_annotation_update
      (JointConfig stk PG G tn fn inst s oms om hs h) NONE ids
      (ann::saved) ((MAP (resolved_op (SND ann)) ops,FEMPTY)::ann::saved))
[~ordinary:]
  (!stk PG G tn fn inst s oms om hs h fuel post birth ids ann saved.
    resolved_annotation_update
      (JointConfig stk PG G tn fn inst s oms om hs h)
      (SOME (OriginOrdinary fuel post)) (birth::ids) (ann::saved)
      ((FST ann, origin_set (SND ann) inst.inst_outputs
        (resolved_out birth post.vs_allocas (FST ann)
          (origin_out PG om inst post)))::saved))
[~block:]
  (!stk PG G tn fn inst s oms om hs h fuel post ids ann saved.
    resolved_annotation_update
      (JointConfig stk PG G tn fn inst s oms om hs h)
      (SOME (OriginBlock fuel post)) ids (ann::saved)
      ((FST ann,resolved_entry fn post (SND ann))::saved))
[~resume:]
  (!f stk PG G tn fn inst s oms om hs h fuel ret send post ids callee ann saved.
    resolved_annotation_update
      (JointConfig (f::stk) PG G tn fn inst s oms om hs h)
      (SOME (OriginResume fuel fn inst s ret send post)) ids
      (callee::ann::saved)
      ((FST ann,DRESTRICT (SND ann)
        (COMPL (set f.cf_inst.inst_outputs)))::saved))
End

Definition resolved_annotation_edge_def:
  resolved_annotation_edge C n q ev q' ids anns ids' anns' <=>
    joint_transition C q ev q' /\ ids' = lifetime_step n ev ids /\
    resolved_annotation_update q ev ids anns anns'
End

Theorem resolved_config_call_exact:
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h) NONE q' /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    ids (ann::saved) /\ decode_invoke inst = SOME (name,ops) ==>
  resolved_config_ok q' (fresh::ids)
    ((MAP (resolved_op (SND ann)) ops,FEMPTY)::ann::saved)
Proof
  simp[joint_transition_call_iff, resolved_config_ok_def] >>
  rpt strip_tac >> gvs[] >>
  simp[resolved_stack_ok_def] >>
  `s1.vs_initial_fmp = s.vs_initial_fmp` by
    metis_tac[ctxLookupAgreeHelpersTheory.enters_block_initial_fmp,
              ctxLookupAgreeHelpersTheory.setup_callee_initial_fmp] >>
  simp[] >> metis_tac[resolved_frame_callee]
QED

Theorem resolved_config_ordinary_exact:
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginOrdinary fuel post)) q' /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) (ann::saved) /\
  (inst.inst_opcode = DALLOCA ==> w2n s.vs_initial_fmp <= w2n s.vs_fmp) ==>
  resolved_config_ok q' (birth::ids)
    ((FST ann,origin_set (SND ann) inst.inst_outputs
      (resolved_out birth post.vs_allocas (FST ann)
        (origin_out PG om inst post)))::saved)
Proof
  simp[joint_transition_ordinary] >> rpt strip_tac >> gvs[] >>
  gvs[resolved_config_ok_def] >>
  `post.vs_initial_fmp = s.vs_initial_fmp` by
    metis_tac[step_inst_non_invoke, ctxLookupAgreeHelpersTheory.step_inst_base_initial_fmp] >>
  `resolved_frame_ok (w2n s.vs_initial_fmp) birth post.vs_allocas PG G om
    (FST ann) (SND ann) (birth::ids)
    ((fn,post.vs_allocas)::MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk)` by
    (irule resolved_frame_cache_transport >> goal_assum (drule_at Any) >>
     metis_tac[step_inst_cache_preserved]) >>
  simp[] >> irule resolved_frame_step >> simp[] >> rpt strip_tac >>
  drule_all resolved_dalloca_output >> simp[]
QED

Theorem resolved_config_block_exact:
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginBlock fuel post)) q' /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    ids (ann::saved) ==>
  resolved_config_ok q' ids
    ((FST ann,resolved_entry fn post (SND ann))::saved)
Proof
  simp[joint_transition_block_iff, resolved_config_ok_def] >>
  rpt strip_tac >> gvs[] >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `post.vs_initial_fmp = s.vs_initial_fmp` by
    metis_tac[step_inst_non_invoke, ctxLookupAgreeHelpersTheory.step_inst_base_initial_fmp] >>
  `s1.vs_initial_fmp = s.vs_initial_fmp` by
    metis_tac[ctxLookupAgreeHelpersTheory.enters_block_initial_fmp] >>
  `post.vs_allocas = s.vs_allocas` by
    (gvs[step_inst_non_invoke] >> metis_tac[step_inst_base_preserves_allocas]) >>
  `s1.vs_allocas = s.vs_allocas` by metis_tac[enters_block_allocas] >>
  simp[] >> metis_tac[resolved_frame_entry]
QED

Theorem resolved_annotation_transition:
  joint_transition C q ev q' /\ resolved_config_ok q ids anns /\
  (case q of JointConfig stk PG G tn fn inst s oms om hs h =>
    inst.inst_opcode = DALLOCA ==> w2n s.vs_initial_fmp <= w2n s.vs_fmp) ==>
  ?anns'. resolved_config_ok q' (lifetime_step n ev ids) anns' /\
    resolved_annotation_edge C n q ev q' ids anns
      (lifetime_step n ev ids) anns'
Proof
  Cases_on `q` >> rpt strip_tac >>
  rename1 `joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h) ev q'` >>
  `?birth births ann saved. ids = birth::births /\ anns = ann::saved` by
    (fs[resolved_config_ok_def] >> metis_tac[]) >> gvs[] >>
  drule joint_transition_label_cases >> strip_tac
  >- (gvs[] >>
      `?name ops. decode_invoke inst = SOME (name,ops)` by
        (fs[joint_transition_call_iff] >> metis_tac[]) >>
      qexists_tac `(MAP (resolved_op (SND ann)) ops,FEMPTY)::ann::saved` >>
      conj_tac
      >- (simp[lifetime_step_def] >> metis_tac[resolved_config_call_exact]) >>
      simp[resolved_annotation_edge_def] >>
      metis_tac[resolved_annotation_update_call])
  >- (gvs[] >>
      qexists_tac `(FST ann,origin_set (SND ann) inst.inst_outputs
        (resolved_out birth post.vs_allocas (FST ann)
          (origin_out PG om inst post)))::saved` >>
      conj_tac
      >- (simp[lifetime_step_def] >> metis_tac[resolved_config_ordinary_exact]) >>
      simp[resolved_annotation_edge_def, resolved_annotation_update_ordinary])
  >- (gvs[] >> qexists_tac `(FST ann,resolved_entry fn post (SND ann))::saved` >>
      conj_tac
      >- (simp[lifetime_step_def] >> metis_tac[resolved_config_block_exact]) >>
      simp[resolved_annotation_edge_def, resolved_annotation_update_block]) >>
  gvs[] >>
  drule (iffLR joint_transition_return) >> strip_tac >> gvs[] >>
  `?b bs a rest. births = b::bs /\ saved = a::rest` by
    (Cases_on `births` >> Cases_on `saved` >>
     fs[resolved_config_ok_def, resolved_stack_ok_def]) >> gvs[] >>
  qexists_tac `(FST a,DRESTRICT (SND a)
    (COMPL (set f.cf_inst.inst_outputs)))::rest` >>
  conj_tac
  >- (PairCases_on `a` >> simp[] >>
      drule resolved_config_return_exact >> disch_then drule >> simp[]) >>
  simp[resolved_annotation_edge_def, lifetime_step_def,
       resolved_annotation_update_resume]
QED

(* Completeness is preserved by every step that allocates no DALLOCA
   pointer: the frame lemmas hold at every floor. *)
Theorem resolved_complete_call:
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h) NONE q' /\
  resolved_complete (JointConfig stk PG G tn fn inst s oms om hs h) ((rp,rv)::saved) /\
  decode_invoke inst = SOME (name,ops) ==>
  resolved_complete q' ((MAP (resolved_op rv) ops,FEMPTY)::(rp,rv)::saved)
Proof
  rpt strip_tac >> gvs[joint_transition_call_iff, resolved_complete_def] >>
  simp[MAP_MAP_o, MAP_EQ_f] >> Cases >>
  simp[frameResolvedOriginsTheory.resolved_op_def, ptrDisciplineTheory.op_prov_def,
    FLOOKUP_o_f] >> CASE_TAC >> simp[]
QED

Theorem resolved_complete_ordinary:
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginOrdinary fuel post)) q' /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::saved) /\
  resolved_complete (JointConfig stk PG G tn fn inst s oms om hs h) ((rp,rv)::saved) /\
  inst.inst_opcode <> DALLOCA ==>
  resolved_complete q' ((rp,origin_set rv inst.inst_outputs
    (resolved_out birth post.vs_allocas rp (origin_out PG om inst post)))::saved)
Proof
  simp[joint_transition_ordinary] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `resolved_config_ok _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [resolved_config_ok_def]) >>
  qpat_x_assum `resolved_complete _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [resolved_complete_def]) >>
  `!d. resolved_frame_ok d birth s.vs_allocas PG G om rp rv
     (birth::ids) ((fn,s.vs_allocas)::MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk)` by
    metis_tac[resolved_frame_complete] >>
  `!d. resolved_frame_ok d birth post.vs_allocas PG (step_prov PG G inst post)
     (origin_step PG om inst post) rp
     (origin_set rv inst.inst_outputs
       (resolved_out birth post.vs_allocas rp (origin_out PG om inst post)))
     (birth::ids) ((fn,post.vs_allocas)::MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk)` by
    (gen_tac >> irule resolved_frame_step >> fs[] >>
     irule resolved_frame_cache_transport >> qexists_tac `s.vs_allocas` >>
     fs[] >> metis_tac[step_inst_cache_preserved]) >>
  simp[resolved_complete_def] >> metis_tac[resolved_frame_complete]
QED

Theorem resolved_complete_block:
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginBlock fuel post)) q' /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    ids ((rp,rv)::saved) /\
  resolved_complete (JointConfig stk PG G tn fn inst s oms om hs h) ((rp,rv)::saved) ==>
  resolved_complete q' ((rp,resolved_entry fn post rv)::saved)
Proof
  simp[joint_transition_block_iff] >> rpt strip_tac >> gvs[] >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `post.vs_allocas = s.vs_allocas` by
    (gvs[step_inst_non_invoke] >> metis_tac[step_inst_base_preserves_allocas]) >>
  qpat_x_assum `resolved_config_ok _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [resolved_config_ok_def]) >>
  qpat_x_assum `resolved_complete _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [resolved_complete_def]) >>
  `!d. resolved_frame_ok d birth s.vs_allocas PG G om rp rv
     ids ((fn,s.vs_allocas)::MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk)` by
    metis_tac[resolved_frame_complete] >>
  `!d. resolved_frame_ok d birth post.vs_allocas PG (entry_prov fn post G)
     (origin_entry fn post om) rp (resolved_entry fn post rv)
     ids ((fn,s.vs_allocas)::MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk)` by
    (gen_tac >> irule resolved_frame_entry >> fs[] >> metis_tac[]) >>
  simp[resolved_complete_def] >> metis_tac[resolved_frame_complete]
QED

Theorem resolved_complete_resume:
  joint_transition C (JointConfig (f::stk) PG G tn fn inst s oms om hs h)
    (SOME (OriginResume fuel fn inst s ret send post)) q' /\
  resolved_complete (JointConfig (f::stk) PG G tn fn inst s oms om hs h)
    (callee::(rp,rv)::saved) ==>
  resolved_complete q'
    ((rp,DRESTRICT rv (COMPL (set f.cf_inst.inst_outputs)))::saved)
Proof
  rpt strip_tac >> gvs[joint_transition_return, resolved_complete_def] >>
  qpat_x_assum `_ = f.cf_prov` (SUBST1_TAC o SYM) >>
  simp[fmap_eq_flookup] >> gen_tac >>
  Cases_on `x IN set f.cf_inst.inst_outputs` >>
  simp[FLOOKUP_o_f, FLOOKUP_DRESTRICT]
QED

Theorem resolved_config_block_complete:
  joint_transition C q (SOME (OriginBlock fuel post)) q' /\
  resolved_config_ok q ids anns ==>
  ?anns'. resolved_config_ok q' ids anns' /\
    (resolved_complete q anns ==> resolved_complete q' anns')
Proof
  Cases_on `q` >> strip_tac >>
  `?ann saved. anns = ann::saved` by (fs[resolved_config_ok_def] >> metis_tac[]) >>
  gvs[] >> rename1 `JointConfig _ _ _ _ fn _ _ _ _ _ _` >>
  PairCases_on `ann` >>
  qexists_tac `(ann0,resolved_entry fn post ann1)::saved` >>
  conj_tac >- (drule_all resolved_config_block_exact >> simp[]) >>
  strip_tac >> drule_all resolved_complete_block >> simp[]
QED

Theorem resolved_annotation_complete:
  resolved_annotation_update q ev ids anns anns' /\
  joint_transition C q ev q' /\ resolved_config_ok q ids anns /\
  resolved_complete q anns /\
  (case q of JointConfig stk PG G tn fn inst s oms om hs h =>
    inst.inst_opcode <> DALLOCA) ==>
  resolved_complete q' anns'
Proof
  rpt strip_tac >>
  qpat_x_assum `resolved_annotation_update _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [resolved_annotation_update_cases]) >>
  gvs[]
  >- (PairCases_on `ann` >> drule_all resolved_complete_call >> simp[])
  >- (PairCases_on `ann` >> drule_all resolved_complete_ordinary >> simp[])
  >- (PairCases_on `ann` >> drule_all resolved_complete_block >> simp[]) >>
  PairCases_on `ann` >> drule_all resolved_complete_resume >> simp[]
QED

Theorem resolved_edge_complete:
  resolved_annotation_edge C n q ev q' ids anns ids' anns' /\
  resolved_config_ok q ids anns /\ joint_config_reachable vs0 C q /\
  ~ctx_has_dalloca C /\ resolved_complete q anns ==>
  resolved_complete q' anns'
Proof
  rw[resolved_annotation_edge_def] >> irule resolved_annotation_complete >>
  goal_assum (drule_at (Pat `resolved_annotation_update _ _ _ _ _`)) >>
  simp[] >> Cases_on `q` >> simp[] >> metis_tac[joint_reachable_dalloca]
QED

Theorem resolved_annotation_reachable_transition:
  joint_config_reachable vs0 C q /\ ptr_discipline lo C vs0 /\
  joint_transition C q ev q' /\ resolved_config_ok q ids anns ==>
  ?anns'. resolved_config_ok q' (lifetime_step n ev ids) anns' /\
    resolved_annotation_edge C n q ev q' ids anns
      (lifetime_step n ev ids) anns'
Proof
  Cases_on `q` >> rpt strip_tac >>
  rename1 `joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h)` >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `inst.inst_opcode = DALLOCA ==> w2n s.vs_initial_fmp <= w2n s.vs_fmp` by
    (strip_tac >> drule_all joint_reachable_dalloca >> strip_tac >>
     fs[ptr_discipline_def, allocas_below_fmp_def] >> metis_tac[]) >>
  irule resolved_annotation_transition >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any)
QED

Theorem resolved_chain_coherent_annotations:
  !es n ids anns q qs r.
  joint_chain C q es qs r /\ joint_config_reachable vs0 C q /\
  ptr_discipline lo C vs0 /\ resolved_config_ok q ids anns /\
  (~ctx_has_dalloca C ==> resolved_complete q anns) ==>
  ?ass. HD ass = anns /\ LENGTH ass = SUC (LENGTH es) /\
    (!k. k <= LENGTH es ==>
      resolved_config_ok (EL k (q::qs))
        (EL k (lifetime_annotations n ids es)) (EL k ass)) /\
    (!k. k < LENGTH es ==>
      resolved_annotation_edge C (n+k) (EL k (q::qs)) (EL k es)
        (EL (SUC k) (q::qs))
        (EL k (lifetime_annotations n ids es)) (EL k ass)
        (EL (SUC k) (lifetime_annotations n ids es)) (EL (SUC k) ass)) /\
    (~ctx_has_dalloca C ==>
      !k. k <= LENGTH es ==> resolved_complete (EL k (q::qs)) (EL k ass))
Proof
  Induct >> Cases_on `qs` >> simp[joint_chain_def]
  >- (rpt strip_tac >> qexists_tac `[anns]` >> fs[lifetime_annotations_def]) >>
  rpt strip_tac >> rename1 `joint_transition C q ev next` >>
  `?anns1. resolved_config_ok next (lifetime_step n ev ids) anns1 /\
    resolved_annotation_edge C n q ev next ids anns
      (lifetime_step n ev ids) anns1` by
    metis_tac[resolved_annotation_reachable_transition] >>
  `joint_config_reachable vs0 C next` by metis_tac[joint_transition_reachable] >>
  `~ctx_has_dalloca C ==> resolved_complete next anns1` by
    metis_tac[resolved_edge_complete] >>
  first_x_assum drule >>
  disch_then (qspecl_then [`SUC n`, `lifetime_step n ev ids`, `anns1`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `anns::ass` >> simp[] >>
  conj_tac
  >- (gen_tac >> Cases_on `k` >> simp[lifetime_annotations_def]) >>
  conj_tac
  >- (gen_tac >> Cases_on `k`
      >- (Cases_on `es` >> simp[lifetime_annotations_def]) >>
      simp[lifetime_annotations_def, ADD_CLAUSES] >>
      rename1 `k < LENGTH es ==> _` >>
      qpat_x_assum `!j. j < LENGTH es ==> _` (qspec_then `k` mp_tac) >>
      simp[ADD_CLAUSES, ADD_COMM]) >>
  strip_tac >> Cases >- fs[] >>
  simp[] >> strip_tac >>
  qpat_x_assum `~ctx_has_dalloca C ==> !k. _` (drule_then irule) >> fs[]
QED

Theorem joint_trace_coherent_annotations:
  joint_trace vs0 C q0 es qs q /\ ptr_discipline lo C vs0 ==>
  ?ass. HD ass = [([],FEMPTY)] /\ LENGTH ass = SUC (LENGTH es) /\
    (!k. k <= LENGTH es ==>
      resolved_config_ok (EL k (q0::qs))
        (EL k (lifetime_annotations 0 [0] es)) (EL k ass)) /\
    (!k. k < LENGTH es ==>
      resolved_annotation_edge C k (EL k (q0::qs)) (EL k es)
        (EL (SUC k) (q0::qs))
        (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
        (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
    (~ctx_has_dalloca C ==>
      !k. k <= LENGTH es ==> resolved_complete (EL k (q0::qs)) (EL k ass))
Proof
  simp[joint_trace_def] >> strip_tac >>
  `resolved_config_ok q0 [0] [([],FEMPTY)]` by
    metis_tac[resolved_config_initial] >>
  `joint_config_reachable vs0 C q0` by metis_tac[joint_initial_reachable] >>
  drule resolved_chain_coherent_annotations >> rpt (disch_then drule) >>
  disch_then (qspec_then `0` mp_tac) >> impl_tac
  >- (strip_tac >> irule resolved_complete_initial >> metis_tac[]) >> simp[]
QED
