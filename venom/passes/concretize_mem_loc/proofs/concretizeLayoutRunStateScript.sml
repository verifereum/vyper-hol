Theory concretizeLayoutRunState
Ancestors concretizeLayoutRunTrace concretizeLayoutBlockEntry frameResolvedTrace
  frameJointTransition venomExecProofs venomExecProps venomExecSemantics
  venomState ptrDiscipline venomInst venomMemProps ptrDisciplineEmptyTaint
  concretizeLayoutPhaseOrigin frameRelocationLocal frameRelocationGuardedValues
  frameActivationLookup frameRelocationTaintOrder frameRelocationEnvironment
  concretizeLayoutReaderContext concretizeLayoutSupplement frameActivationLifetime
  frameJointTrace concretizeStepStructure finite_map contextCodegenRel
  frameRelocationBinding frameRelocationGhostCopy frameRelocationCopyTaint
  frameRelocationValues list

(* Unlike the existential block boundary, this pins the transported head map. *)
Theorem layout_run_block_annotations:
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginBlock fuel post)) q' /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    ids ((rp,rv)::saved) ==>
  resolved_config_ok q' ids ((rp,resolved_entry fn post rv)::saved)
Proof
  strip_tac >>
  gvs[joint_transition_block_iff, resolved_config_ok_def] >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `post.vs_allocas = s.vs_allocas` by
    (gvs[step_inst_non_invoke] >> metis_tac[step_inst_base_preserves_allocas]) >>
  `s1.vs_allocas = s.vs_allocas` by metis_tac[enters_block_allocas] >>
  simp[] >> metis_tac[resolved_frame_entry]
QED

Theorem layout_run_block_state:
  layout_ordinary_trace vs0 C q0 es qs q a s /\ vs0.vs_allocas = FEMPTY /\
  a.lop_cursor < LENGTH es /\
  a.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::saved /\
  EL a.lop_cursor es = SOME (OriginBlock fuel post) /\
  EL (SUC a.lop_cursor) (q0::qs) =
    JointConfig stk PG G' tn' fn inst' sentry oms om' hs h' /\
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginBlock fuel post))
    (JointConfig stk PG G' tn' fn inst' sentry oms om' hs h') /\
  EVERY bb_well_formed fn.fn_blocks /\
  (!bb. MEM bb fn.fn_blocks ==>
    EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions) /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs a.lop_cursor)
    concretize_local_obs post tpost /\
  relocation_taint_le
    (joint_relocation_demand lo (concretize_positions C') q0 es qs a.lop_cursor)
    tn a.lop_target_taint /\
  relocation_env post tpost /\ relocation_reader_context post tpost /\
  post.vs_current_bb = tpost.vs_current_bb /\ post.vs_prev_bb = tpost.vs_prev_bb /\
  concretize_supplement D tn post tpost /\
  post.vs_code = tpost.vs_code /\ post.vs_data_section = tpost.vs_data_section /\
  parameter_roots (\i x y. clean_resolved_root
    (activation_lookup (0:num) (concretize_positions C')
      (birth::ids) (fn::MAP (\f. f.cf_fn) stk))
    (resolved_parameter_entry rp i) x y) post.vs_params tpost.vs_params /\
  post.vs_initial_fmp = tpost.vs_initial_fmp ==>
  ?tentry b.
    enters_block (concretize_function_with_positions positions fn)
      tpost tentry /\
    b.lop_origin = a.lop_origin /\ ~b.lop_pending /\
    b.lop_cursor = SUC a.lop_cursor /\ b.lop_bound = SUC a.lop_bound /\
    b.lop_config = JointConfig stk PG G' tn' fn inst' sentry oms om' hs h' /\
    b.lop_ids = a.lop_ids /\
    b.lop_anns = (rp,resolved_entry fn post rv)::saved /\
    b.lop_target_taint = entry_taint_vars fn tpost a.lop_target_taint /\
    layout_ordinary_trace vs0 C q0 es qs q b sentry /\
    layout_ordinary_state D lo C' q0 es qs b sentry tentry
Proof
  strip_tac >>
  qpat_x_assum `layout_ordinary_trace _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_trace_def] >> strip_tac >>
  drule_all concretize_origin_block_transport >>
  disch_then (qspec_then `positions` strip_assume_tac) >>
  `sentry.vs_code = tentry.vs_code /\
   sentry.vs_data_section = tentry.vs_data_section /\
   sentry.vs_params = post.vs_params /\ tentry.vs_params = tpost.vs_params /\
   sentry.vs_initial_fmp = tentry.vs_initial_fmp` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_block_iff] >> strip_tac >>
     gvs[enters_block_def] >>
     imp_res_tac eval_phis_only_updates_vs_vars >>
     fs[venom_state_component_equality]) >>
  drule_all layout_run_block_annotations >> strip_tac >>
  drule_all lifetime_transition >> simp[lifetime_step_def] >> strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  qexistsl [`tentry`, `a with <|lop_pending := F;
    lop_cursor := SUC a.lop_cursor; lop_bound := SUC a.lop_bound;
    lop_config := JointConfig stk PG G' tn' fn inst' sentry oms om' hs h';
    lop_anns := (rp,resolved_entry fn post rv)::saved;
    lop_target_taint := entry_taint_vars fn tpost a.lop_target_taint|>`] >>
  simp[layout_ordinary_state_def, layout_phase_normalize_def] >>
  qexistsl [`birth`, `ids`, `rp`, `resolved_entry fn post rv`, `saved`] >> simp[]
QED

(* The initial sampled state is diagonal; no allocator-next premise is used. *)
Theorem layout_run_initial_state:
  joint_trace vs0 C q0 es qs q /\
  q0 = JointConfig [] [] FEMPTY entry_taint fn inst s [] FEMPTY hs h /\
  s.vs_allocas = FEMPTY ==>
  ?b. b.lop_origin = origin /\ ~b.lop_pending /\
    b.lop_cursor = 0 /\ b.lop_bound = 0 /\ b.lop_config = q0 /\
    b.lop_ids = [0] /\ b.lop_anns = [([],FEMPTY)] /\
    b.lop_target_taint = entry_taint /\
    layout_ordinary_trace vs0 C q0 es qs q b s /\
    layout_ordinary_state D lo C' q0 es qs b s s
Proof
  strip_tac >>
  qexists `<|lop_origin := origin; lop_pending := F; lop_cursor := 0;
    lop_bound := 0; lop_config := q0; lop_ids := [0];
    lop_anns := [([],FEMPTY)]; lop_target_taint := entry_taint|>` >>
  simp[] >> conj_tac
  >- (qmatch_goalsub_abbrev_tac `layout_ordinary_trace _ _ _ _ _ _ b _` >>
      drule layout_run_initial_trace >>
      disch_then (qspecl_then [`s`, `b`] mp_tac) >> simp[Abbr `b`]) >>
  simp[layout_ordinary_state_def, layout_phase_normalize_def] >>
  conj_tac
  >- (simp[local_rel_def, local_values_def, variable_domains_def,
        variables_agree_on_def, guarded_ptr_def, guarded_bytes_def,
        copy_ptr_def, copy_bytes_def, word_agree_except_def,
        concretize_local_obs_def, dead_result_rel_def] >>
      conj_tac >- (rpt strip_tac >> gvs[]) >>
      conj_tac
      >- (irule (SRULE[joint_memory_observation_def]
            joint_relocation_demand_initial_agreement) >> simp[]) >>
      simp[accounts_agree_except_def, transient_agree_except_def,
        imms_agree_except_def, storage_agree_except_def, word_agree_except_def] >>
      irule EVERY2_refl >> simp[request_agree_except_def,
        accounts_agree_except_def, transient_agree_except_def,
        storage_agree_except_def, word_agree_except_def]) >>
  simp[relocation_taint_le_def, demand_taint_def] >> rpt strip_tac >>
  drule joint_relocation_demand_empty_entry >> simp[] >> metis_tac[]
QED

val _ = export_theory();
