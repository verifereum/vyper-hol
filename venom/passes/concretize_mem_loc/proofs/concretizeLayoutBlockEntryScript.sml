Theory concretizeLayoutBlockEntry
Ancestors passTransform concretizeLayoutLocalPhi concretizeStepStructure concretizeStageShape
  frameRelocationBinding frameRelocationDemand frameJointDemand
  frameJointTransition frameJointTrace frameResolvedTrace
  frameResolvedOrigins contextCodegenRel venomExecProofs venomWf
  passSimulationProofs frameRelocationEnvironment concretizeLayoutReaderContext
  frameRelocationLocal frameRelocationValues frameRelocationTaintOrder
  frameRelocationCopyTaint venomState
  concretizeLayoutSupplement venomInst codegenRel frameCfgBoundary
  passSharedDefs passSimulationDefs venomExecSemantics ptrDiscipline finite_map list pred_set

(* A single normalization boundary for execution and both entry ghosts.
   Only PHIs in the original prefix are selected; all other instructions
   may be changed or deleted without exposing a later PHI in a wf block. *)
Theorem phi_entry_filter_map[local]:
  !insts.
  (!i j. i < j /\ j < LENGTH insts /\
    (EL j insts).inst_opcode = PHI ==> (EL i insts).inst_opcode = PHI) /\
  (!i. MEM i insts ==> ((f i).inst_opcode = PHI <=> i.inst_opcode = PHI)) /\
  (!i. MEM i insts /\ i.inst_opcode = PHI ==> f i = i /\ keep i) ==>
  eval_phis s (FILTER keep (MAP f insts)) = eval_phis s insts /\
  resolved_phis prev rv (FILTER keep (MAP f insts)) = resolved_phis prev rv insts /\
  phis_taint prev tn (FILTER keep (MAP f insts)) = phis_taint prev tn insts /\
  phi_prefix_length (FILTER keep (MAP f insts)) = phi_prefix_length insts
Proof
  Induct >- simp[eval_phis_def, resolved_phis_def, phis_taint_def, phi_prefix_length_def] >>
  gen_tac >> strip_tac >>
  `!i j. i < j /\ j < LENGTH insts /\
    (EL j insts).inst_opcode = PHI ==> (EL i insts).inst_opcode = PHI` by
    (rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
  Cases_on `h.inst_opcode = PHI`
  >- (gvs[] >> first_x_assum drule >> simp[] >> strip_tac >>
      gvs[eval_phis_def, resolved_phis_def, phis_taint_def, phi_prefix_length_def]) >>
  `EVERY (\i. i.inst_opcode <> PHI) insts` by
    (simp[EVERY_MEM, MEM_EL] >> rpt strip_tac >>
     qpat_x_assum `!i j. _ /\ j < LENGTH (h::insts) /\ _ ==> _`
       (qspecl_then [`0`, `SUC n`] mp_tac) >> gvs[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) (FILTER keep (MAP f (h::insts)))` by
    (gvs[EVERY_MEM, MEM_FILTER, MEM_MAP] >> metis_tac[]) >>
  Cases_on `FILTER keep (MAP f (h::insts))` >>
  gvs[eval_phis_def, resolved_phis_def, phis_taint_def, phi_prefix_length_def]
QED

Theorem concretize_block_entry_phis[local]:
  bb_well_formed bb ==>
  eval_phis s (clear_nops_block (block_map_transform
    (concretize_inst_with_positions positions) bb)).bb_instructions =
    eval_phis s bb.bb_instructions /\
  resolved_phis prev rv (clear_nops_block (block_map_transform
    (concretize_inst_with_positions positions) bb)).bb_instructions =
    resolved_phis prev rv bb.bb_instructions /\
  phis_taint prev tn (clear_nops_block (block_map_transform
    (concretize_inst_with_positions positions) bb)).bb_instructions =
    phis_taint prev tn bb.bb_instructions /\
  phi_prefix_length (clear_nops_block (block_map_transform
    (concretize_inst_with_positions positions) bb)).bb_instructions =
    phi_prefix_length bb.bb_instructions
Proof
  strip_tac >> simp[clear_nops_block_def, block_map_transform_def] >>
  irule phi_entry_filter_map >>
  gvs[bb_well_formed_def, concretize_positions_phi] >> rpt strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem concretize_enters_block_exact:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb_well_formed bb /\ enters_block fn s post ==>
  enters_block (concretize_function_with_positions positions fn) s post
Proof
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  qexistsl [`clear_nops_block (block_map_transform
    (concretize_inst_with_positions positions) bb)`, `s_phi`] >>
  simp[concretize_positions_blocks, lookup_block_map_proof,
       concretize_positions_block_label] >>
  metis_tac[concretize_block_entry_phis]
QED

Theorem concretize_enters_block_transport:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb_well_formed bb /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R
    concretize_local_obs s t /\
  relocation_taint_le R tn un /\ relocation_env s t /\
  relocation_reader_context s t /\ s.vs_prev_bb = t.vs_prev_bb /\
  s.vs_current_bb = t.vs_current_bb /\
  EVERY (\inst. MEM inst (fn_insts fn)) bb.bb_instructions /\
  concretize_supplement D tn s t /\ enters_block fn s post ==>
  ?tpost.
    enters_block (concretize_function_with_positions positions fn) t tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn) L (resolved_phis s.vs_prev_bb rv bb.bb_instructions))
      (guarded_bytes (retpc_var fn) (resolved_phis s.vs_prev_bb rv bb.bb_instructions)
        (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions)) R
      concretize_local_obs post tpost /\
    relocation_taint_le R
      (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions)
      (un with t_var := phis_taint t.vs_prev_bb un bb.bb_instructions) /\
    relocation_env post tpost /\ relocation_reader_context post tpost /\
    concretize_supplement D
      (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions) post tpost
Proof
  strip_tac >>
  qpat_x_assum `enters_block fn s post` mp_tac >>
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  drule_all (SRULE[GSYM concretize_local_obs_def, SF ETA_ss]
    (Q.INST [`D` |-> `<| d_stor := K (K UNIV); d_trans := K (K UNIV);
                         d_imm := K UNIV; d_ret := K {} |>`]
      concretize_parallel_phis_transport)) >> strip_tac >>
  qabbrev_tac `bb' = clear_nops_block
    (block_map_transform (concretize_inst_with_positions positions) bb)` >>
  qexists_tac `tpost with vs_inst_idx := phi_prefix_length bb'.bb_instructions` >>
  conj_tac
  >- (qexistsl_tac [`bb'`, `tpost`] >>
      simp[concretize_positions_blocks, lookup_block_map_proof,
           concretize_positions_block_label, Abbr `bb'`] >>
      metis_tac[concretize_block_entry_phis]) >>
  conj_tac
  >- gvs[local_rel_def, local_values_def, variable_domains_def, variables_agree_on_def,
         lookup_var_def, concretize_local_obs_def, dead_result_rel_def] >>
  fs[relocation_env_def, relocation_reader_context_def] >>
  metis_tac[concretize_supplement_phis]
QED

(* Terminator simulation supplies related poststates at the incoming demand.
   The actual block event restricts that demand before parallel PHI entry. *)
Theorem concretize_origin_block_transport:
  joint_trace vs0 C q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginBlock fuel post) /\
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginBlock fuel post))
    (JointConfig stk PG G' tn' fn inst' sentry oms om' hs h') /\
  EVERY bb_well_formed fn.fn_blocks /\
  (!bb. MEM bb fn.fn_blocks ==> EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions) /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo positions q0 es qs c) concretize_local_obs post tpost /\
  relocation_taint_le (joint_relocation_demand lo positions q0 es qs c) tn un /\
  relocation_env post tpost /\ relocation_reader_context post tpost /\
  post.vs_current_bb = tpost.vs_current_bb /\ post.vs_prev_bb = tpost.vs_prev_bb /\
  concretize_supplement D tn post tpost ==>
  ?tentry.
    enters_block (concretize_function_with_positions p fn) tpost tentry /\
    local_rel (\u. F) (guarded_ptr (retpc_var fn) L (resolved_entry fn post rv))
      (guarded_bytes (retpc_var fn) (resolved_entry fn post rv) tn')
      (joint_relocation_demand lo positions q0 es qs (SUC c)) concretize_local_obs
      sentry tentry /\
    relocation_taint_le (joint_relocation_demand lo positions q0 es qs (SUC c))
      tn' (entry_taint_vars fn tpost un) /\
    relocation_env sentry tentry /\ relocation_reader_context sentry tentry /\
    concretize_supplement D tn' sentry tentry
Proof
  strip_tac >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_block_iff] >> strip_tac >> gvs[] >>
  `inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
  `step_inst_base inst s = OK post` by gvs[step_inst_non_invoke] >>
  drule_all successful_terminator_successor >> strip_tac >>
  `!a b. joint_relocation_demand lo positions q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo positions q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     simp[joint_writes_def, step_writes_def, source_memory_write_ranges_def,
          range_bytes_def] >>
     (conj_tac >- (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def, get_successors_def] >>
        gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
        rpt (CHANGED_TAC (pairarg_tac >> gvs[])))) >>
     qexistsl_tac [`C`, `q`, `vs0`] >> simp[]) >>
  `local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo positions q0 es qs (SUC c))
    concretize_local_obs post tpost` by
    (fs[local_rel_def] >> metis_tac[demand_agree_restrict]) >>
  `relocation_taint_le (joint_relocation_demand lo positions q0 es qs (SUC c)) tn un` by
    (fs[relocation_taint_le_def, demand_taint_def] >> metis_tac[]) >>
  `?bb. lookup_block post.vs_current_bb fn.fn_blocks = SOME bb` by
    gvs[enters_block_def] >>
  `MEM bb fn.fn_blocks` by (fs[lookup_block_def] >> metis_tac[FIND_MEM]) >>
  `bb_well_formed bb` by gvs[EVERY_MEM] >>
  `EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions` by metis_tac[] >>
  drule_all concretize_enters_block_transport >>
  disch_then (qspec_then `p` strip_assume_tac) >>
  qexists_tac `tpost'` >>
  gvs[resolved_entry_def, entry_taint_vars_def]
QED
