Theory fmpStageBlockSimEntryAssembly
Ancestors
  fmpStageRel fmpStageBlockSimEntryPhis fmpStageBlockSimEntryLedger
  fmpStageOpBase fmpStageControl fmpStepLayout
  fmpStageReclaimSound fmpLowerDefs fmpLowerReclaimPlan
  o1FrameLockstep livenessProofs venomWfProps
  livenessDefs livenessTransferProofs o1PassContract unitShapeDefs
  venomWf venomInst venomExecSemantics venomState
  rich_list finite_map list

Theorem fmp_entry_lowered_analysis[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE ==>
  ?states. fmp_reclaim_states infos fn = SOME states
Proof
  simp[fmp_stage_lowered_def] >> rpt strip_tac >>
  gvs[fmp_lower_function_with_info_def, AllCaseEqs()] >>
  metis_tac[analyze_fmp_reclaims_candidate]
QED

Theorem fmp_entry_effect_cases[local]:
  !ins prev v u. phi_eff (SOME prev) v ins = SOME (Var u) ==>
    (u = v /\ EVERY (\q. ~MEM v q.inst_outputs) (collect_phis ins)) \/
    (?phi. MEM phi (collect_phis ins) /\ MEM v phi.inst_outputs /\
      resolve_phi prev phi.inst_operands = SOME (Var u))
Proof
  Induct >> simp[phi_eff_def, phi_read_def, collect_phis_def] >>
  rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `MEM v h.inst_outputs` >> simp[]
  >- (Cases_on `h.inst_outputs = [v]` >> simp[] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`prev`,`v`,`u`] mp_tac) >>
  Cases_on `phi_read (SOME prev) v ins` >> simp[phi_eff_def] >>
  metis_tac[]
QED

Theorem fmp_entry_effect_live[local]:
  wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
  fmp_reclaim_states infos fn = SOME states /\
  MEM pl (cfg_analyze fn).cfg_dfs_pre /\
  MEM sl (cfg_analyze fn).cfg_dfs_pre /\
  MEM sl (cfg_succs_of (cfg_analyze fn) pl) /\
  lookup_block pl fn.fn_blocks = SOME pb /\
  lookup_block sl fn.fn_blocks = SOME bb /\
  pb.bb_instructions <> [] /\
  MEM v (live_vars_at (liveness_analyze fn) sl
    (phi_prefix_length bb.bb_instructions)) /\
  phi_eff (SOME pl) v bb.bb_instructions = SOME (Var u) ==>
  MEM u (live_vars_at (liveness_analyze fn) pl
    (PRE (LENGTH pb.bb_instructions)))
Proof
  strip_tac >> drule_all fmp_stage_live_edge >> strip_tac >>
  drule fmp_entry_effect_cases >> strip_tac >> gvs[]
  >- (gvs[EVERY_MEM] >> metis_tac[]) >-
  (`phi = phi'` by
     (irule ssa_outputs_same_inst >>
      conj_tac >- (qexists `fn` >> simp[fn_insts_blocks_MEM] >>
        metis_tac[collect_phis_mem, lookup_block_mem]) >>
      qexists `v` >> simp[]) >>
   gvs[])
  >- gvs[EVERY_MEM] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem fmp_entry_effect_tracked[local]:
  MEM bb fn.fn_blocks /\ ~retpc_var fn v /\
  phi_eff (SOME pl) v bb.bb_instructions = SOME (Var u) ==>
  ~retpc_var fn u
Proof
  strip_tac >> drule fmp_entry_effect_cases >> strip_tac >> gvs[] >>
  `MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI` by
    metis_tac[collect_phis_mem] >>
  `MEM phi (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `MEM (Var u) phi.inst_operands` by
    metis_tac[venomExecProofsTheory.resolve_phi_MEM_el] >>
  gvs[retpc_var_def] >> metis_tac[copy_phi_var_phi]
QED

Theorem fmp_entry_jump_phis[local]:
  wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
  fmp_reclaim_states infos fn = SOME states /\
  MEM sb.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) sb.vs_current_bb) /\
  lookup_block sb.vs_current_bb fn.fn_blocks = SOME pb /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block lbl fn'.fn_blocks = SOME bb' /\
  LENGTH pb.bb_instructions = SUC sb.vs_inst_idx /\
  (!u. eval_phis u bb'.bb_instructions = eval_phis u bb.bb_instructions) /\
  phi_prefix_length bb'.bb_instructions = phi_prefix_length bb.bb_instructions /\
  fmp_env_rel sm fn (live_vars_at (liveness_analyze fn)
    sb.vs_current_bb sb.vs_inst_idx) G tn.t_var sb tb /\
  sb.vs_labels = tb.vs_labels /\ sb.vs_current_bb = tb.vs_current_bb /\
  enters_block fn (jump_to lbl sb) s1 ==>
  ?t1. enters_block fn' (jump_to lbl tb) t1 /\
    fmp_env_rel sm fn (live_vars_at (liveness_analyze fn) lbl
      (phi_prefix_length bb.bb_instructions))
      (entry_prov fn (jump_to lbl sb) G)
      (entry_taint_vars fn (jump_to lbl sb) tn).t_var s1 t1 /\
    t1 = (jump_to lbl tb) with <|vs_vars := t1.vs_vars;
      vs_inst_idx := phi_prefix_length bb.bb_instructions|> /\
    (!v. (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
      ~MEM v i.inst_outputs) ==>
      FLOOKUP t1.vs_vars v = FLOOKUP (jump_to lbl tb).vs_vars v)
Proof
  strip_tac >> irule fmp_entry_phis_transport >>
  simp[jump_to_def] >>
  qexists `live_vars_at (liveness_analyze fn)
    sb.vs_current_bb sb.vs_inst_idx` >> reverse conj_tac
  >- gvs[fmp_env_rel_def, jump_to_def] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (`pb.bb_instructions <> []` by
        (Cases_on `pb.bb_instructions` >> gvs[]) >>
      qpat_x_assum `sb.vs_current_bb = tb.vs_current_bb`
        (fn th => fs[GSYM th]) >>
      drule_all fmp_entry_effect_live >> simp[]) >>
  irule fmp_entry_effect_tracked >> goal_assum (drule_at Any) >>
  metis_tac[lookup_block_mem]
QED

Theorem fmp_entry_jump_past_root[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  lookup_block rl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  MEM (EL idx bb.bb_instructions).inst_opcode [JMP; JNZ; DJMP] /\
  (fn_is_context_entry ctx fn ==> entry_fn_no_params fn) ==>
  rp <= idx
Proof
  strip_tac >>
  `~(SUC idx = rp)` by
    (strip_tac >> drule_all fmp_stage_root_crossing >> gvs[]) >>
  qpat_x_assum `fmp_stage_root _ _ _ = _` mp_tac >>
  simp[fmp_stage_root_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  drule split_fmp_entry_users >> strip_tac >>
  gvs[lookup_block_def, FIND_def, INDEX_FIND_def] >>
  `~(idx < LENGTH users)` by
    (strip_tac >>
     `MEM (EL idx users) users` by simp[EL_MEM] >>
     fs[EVERY_MEM, EL_APPEND_EQN]) >>
  Cases_on `retpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
  decide_tac
QED

Theorem fmp_entry_jump_ledger[local]:
  wf_function fn /\ ssa_form fn /\
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  MEM pb fn.fn_blocks /\ MEM bb fn.fn_blocks /\
  MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) pb.bb_label) /\
  LENGTH pb.bb_instructions = SUC idx /\
  MEM (EL idx pb.bb_instructions).inst_opcode [JMP; JNZ; DJMP] /\
  df_at NONE states pb.bb_label idx = SOME st /\
  fmp_ledger_ok (fn_insts fn) env t lo regions /\
  MAP (\r. r.fr_mark) regions =
    SND (fmp_pop_at infos fn (liveness_analyze fn) env (pb.bb_label,idx)
      (EL idx pb.bb_instructions) st) /\
  EVERY (\r. elo <= r.fr_lo) regions /\
  fmp_ledger_link sm eb lo regions /\
  fmp_sites_ok sm fmp0 raw0 lo raw_fmp /\
  (!v. (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
      ~MEM v i.inst_outputs) ==> lookup_var v t1 = lookup_var v t) ==>
  ?st' regions'.
    df_at NONE states bb.bb_label (phi_prefix_length bb.bb_instructions) = SOME st' /\
    fmp_ledger_ok (fn_insts fn) env t1 lo regions' /\
    MAP (\r. r.fr_mark) regions' = st'.frs_stack /\
    EVERY (\r. elo <= r.fr_lo) regions' /\
    fmp_ledger_link sm eb lo regions'
Proof
  strip_tac >>
  `?st' ks. df_at NONE states bb.bb_label
       (phi_prefix_length bb.bb_instructions) = SOME st' /\
    SND (fmp_pop_at infos fn (liveness_analyze fn) env (pb.bb_label,idx)
      (EL idx pb.bb_instructions) st) = st'.frs_stack ++ ks` by
    (irule fmp_analysis_jump_phi_prefix >> simp[] >>
     metis_tac[venomExecProofsTheory.phi_prefix_length_le,
               venomExecProofsTheory.phi_prefix_length_el_phi]) >>
  qexistsl [`st'`, `TAKE (LENGTH st'.frs_stack) regions`] >> simp[] >>
  irule fmp_ledger_restrict_stack >>
  conj_tac >- metis_tac[] >> simp[] >>
  reverse conj_tac >- metis_tac[] >> qexists `t` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> rpt strip_tac >>
  `MEM r.fr_mark st'.frs_stack` by
    (`MEM r.fr_mark (MAP (\r. r.fr_mark) (TAKE (LENGTH st'.frs_stack) regions))` by
       (simp[MEM_MAP] >> metis_tac[]) >>
     gvs[MAP_TAKE, TAKE_LENGTH_APPEND]) >>
  `MEM i (fn_insts fn)` by (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  metis_tac[fmp_analysis_stack_not_phi_output]
QED

Theorem fmp_entry_state_frame[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  enters_block fn s s1 ==>
  s1 = s with <|vs_vars := s1.vs_vars;
    vs_inst_idx := phi_prefix_length bb.bb_instructions|>
Proof
  simp[contextCodegenRelTheory.enters_block_def] >> rpt strip_tac >> gvs[] >>
  drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem fmp_entry_frame_from_geometry[local]:
  wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
  fn.fn_fmp_signature = NONE /\
  lookup_block sb.vs_current_bb fn.fn_blocks = SOME pb /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block lbl fn'.fn_blocks = SOME bb' /\
  MEM pb fn.fn_blocks /\ MEM bb fn.fn_blocks /\
  LENGTH pb.bb_instructions = SUC sb.vs_inst_idx /\
  MEM (EL sb.vs_inst_idx pb.bb_instructions).inst_opcode [JMP; JNZ; DJMP] /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) sb.vs_current_bb) /\
  MEM sb.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  (!u. eval_phis u bb'.bb_instructions = eval_phis u bb.bb_instructions) /\
  phi_prefix_length bb'.bb_instructions = phi_prefix_length bb.bb_instructions /\
  (!infos ctx runner. fmp_stage_lowered infos ctx runner fn fn' ==>
    (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
      lbl <> rl /\ (fn_is_context_entry ctx fn ==> entry_fn_no_params fn) /\
      (!i. MEM i (fn_insts fn) ==> ~MEM runner i.inst_outputs)) /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions (phi_prefix_length bb.bb_instructions) =
      phi_prefix_length bb.bb_instructions) /\
  fmp_sites_ok sm fmp0 raw0 lo sb.vs_fmp /\
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tn.t_var sb tb /\
  enters_block fn (jump_to lbl sb) s1 ==>
  ?t1. enters_block fn' (jump_to lbl tb) t1 /\
    fmp_frame_rel sm fmp0 raw0 eb elo lo F fn fn' PG
      (entry_prov fn (jump_to lbl sb) G)
      (entry_taint_vars fn (jump_to lbl sb) tn).t_var s1 t1
Proof
  strip_tac >>
  qpat_x_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_frame_rel_def] >> strip_tac >>
  `?states. fmp_reclaim_states infos fn = SOME states` by
    metis_tac[fmp_entry_lowered_analysis] >>
  `?t1. enters_block fn' (jump_to lbl tb) t1 /\
    fmp_env_rel sm fn (live_vars_at (liveness_analyze fn) lbl
      (phi_prefix_length bb.bb_instructions))
      (entry_prov fn (jump_to lbl sb) G)
      (entry_taint_vars fn (jump_to lbl sb) tn).t_var s1 t1 /\
    t1 = (jump_to lbl tb) with <|vs_vars := t1.vs_vars;
      vs_inst_idx := phi_prefix_length bb.bb_instructions|> /\
    (!v. (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
      ~MEM v i.inst_outputs) ==>
      FLOOKUP t1.vs_vars v = FLOOKUP (jump_to lbl tb).vs_vars v)` by
    (irule fmp_entry_jump_phis >> simp[] >> metis_tac[]) >>
  `s1 = (jump_to lbl sb) with <|vs_vars := s1.vs_vars;
      vs_inst_idx := phi_prefix_length bb.bb_instructions|>` by
    (irule fmp_entry_state_frame >> qexists `fn` >>
     fs[jump_to_def]) >>
  qpat_x_assum `!infos ctx runner. _` drule >> strip_tac >>
  qexists `t1` >> simp[] >> simp[fmp_frame_rel_def] >>
  qexistsl [`infos`,`ctx`,`runner`] >>
  gns[venom_state_component_equality, jump_to_def, fmp_params_rel_def] >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    qpat_x_assum `!b z c id. _` drule >> simp[]) >>
  suspend "root"
QED

Resume fmp_entry_frame_from_geometry[root]:
  Cases_on `fmp_stage_root infos ctx fn` >- gvs[] >>
  rename1 `fmp_stage_root infos ctx fn = SOME p` >> PairCases_on `p` >>
  rename1 `fmp_stage_root infos ctx fn = SOME (rl,rp)` >>
  gns[] >>
  `~(tb.vs_current_bb = rl /\ sb.vs_inst_idx < rp)` by
    (strip_tac >> gns[] >>
     `rp <= sb.vs_inst_idx` by
       (irule fmp_entry_jump_past_root >>
        qexistsl [`pb`, `ctx`, `fn`, `fn'`, `infos`, `rl`, `runner`] >>
        simp[]) >> decide_tac) >>
  qpat_x_assum `?env st. _` strip_assume_tac >>
  qpat_x_assum `if _ then _ else _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  `pb.bb_label = tb.vs_current_bb /\ bb.bb_label = lbl` by
    (conj_tac >-
      (qpat_x_assum `lookup_block _ _ = SOME pb` mp_tac >>
       rewrite_tac[lookup_block_def] >> disch_then (mp_then Any mp_tac FIND_P) >> simp[]) >>
     qpat_x_assum `lookup_block _ _ = SOME bb` mp_tac >>
     rewrite_tac[lookup_block_def] >> disch_then (mp_then Any mp_tac FIND_P) >> simp[]) >>
  `?st' regions'.
    df_at NONE states lbl (phi_prefix_length bb.bb_instructions) = SOME st' /\
    fmp_ledger_ok (fn_insts fn) env t1 lo regions' /\
    MAP (\r. r.fr_mark) regions' = st'.frs_stack /\
    EVERY (\r. elo <= r.fr_lo) regions' /\
    fmp_ledger_link sm eb lo regions'` by
    (qpat_assum `bb.bb_label = lbl` (fn th => once_rewrite_tac[GSYM th]) >>
     irule fmp_entry_jump_ledger >>
     simp[] >> conj_tac >-
       (qexistsl [`sb.vs_inst_idx`, `infos`, `pb`, `regions`, `st`, `tb`] >>
        simp[lookup_var_def]) >>
     qexistsl [`fmp0`, `raw0`, `sb.vs_fmp`] >> simp[]) >>
  qexistsl [`env`, `st'`] >> simp[] >>
  conj_tac >- (irule fmp_stage_covers_phis >> simp[jump_to_def] >> metis_tac[]) >>
  reverse conj_tac >- (qexists `regions'` >> simp[]) >>
  `FLOOKUP t1.vs_vars runner = FLOOKUP tb.vs_vars runner` by
    (qpat_x_assum `!v. _` irule >> rpt strip_tac >>
     qpat_x_assum `lbl <> rl /\ _` strip_assume_tac >>
     qpat_x_assum `!i. MEM i (fn_insts fn) ==> _` (qspec_then `i` mp_tac) >>
     impl_tac >- (simp[fn_insts_def, fn_insts_blocks_MEM] >>
                  qexists `bb` >> simp[]) >> simp[]) >>
  gns[lookup_var_def]
QED

Finalise fmp_entry_frame_from_geometry

Theorem fmp_entry_stage_from_geometry:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn bi sb /\ active_inst fn bi sb /\
  MEM bi.inst_opcode [JMP; JNZ; DJMP] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn sb lo tb ts /\
  step_inst k C bi sb = OK (jump_to lbl sb) /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  enters_block fn (jump_to lbl sb) s1 /\ active_inst fn inst s1 /\
  lookup_block sb.vs_current_bb fn.fn_blocks = SOME pb /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block lbl fn'.fn_blocks = SOME bb' /\
  MEM pb fn.fn_blocks /\ MEM bb fn.fn_blocks /\
  LENGTH pb.bb_instructions = SUC sb.vs_inst_idx /\
  EL sb.vs_inst_idx pb.bb_instructions = bi /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pb.bb_label) /\
  MEM pb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  (!u. eval_phis u bb'.bb_instructions = eval_phis u bb.bb_instructions) /\
  phi_prefix_length bb'.bb_instructions = phi_prefix_length bb.bb_instructions /\
  (!infos ctx runner. fmp_stage_lowered infos ctx runner fn fn' ==>
    (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) ==> lbl <> rl) /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions (phi_prefix_length bb.bb_instructions) =
      phi_prefix_length bb.bb_instructions) ==>
  ?t1. enters_block fn' (jump_to lbl tb) t1 /\
    fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
      (entry_prov fn (jump_to lbl sb) G)
      (entry_taint_vars fn (jump_to lbl sb) tn) fn s1 lo t1 ts
Proof
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `wf_function fn /\ fn_inst_wf fn` by fs[o1_fn_shape_def] >>
  `pb.bb_label = sb.vs_current_bb` by
    (qpat_x_assum `lookup_block _ _ = SOME pb` mp_tac >>
     rewrite_tac[lookup_block_def] >>
     disch_then (mp_then Any mp_tac FIND_P) >> simp[]) >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_stage_rel_def] >> strip_tac >> gns[] >>
  `?t1. enters_block fn' (jump_to lbl tb) t1 /\
    fmp_frame_rel sm fmp0 raw0 (fmp_frame_base raw0 stk)
      (fmp_frame_lo fmp0 ts) lo F fn fn' PG
      (entry_prov fn (jump_to lbl sb) G)
      (entry_taint_vars fn (jump_to lbl sb) tn).t_var s1 t1` by
    (irule fmp_entry_frame_from_geometry >>
     simp[o1_fn_shape_def] >> suspend "witness") >>
  suspend "shared"
QED

Resume fmp_entry_stage_from_geometry[witness]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!infos ctx runner. _` drule >> strip_tac >>
  simp[] >> rpt gen_tac >> strip_tac >>
  drule_all fmp_stage_witness_pin >> strip_tac >>
  gns[o1_fn_shape_def]
QED

Resume fmp_entry_stage_from_geometry[shared]:
  `s1 = (jump_to lbl sb) with <|vs_vars := s1.vs_vars;
    vs_inst_idx := phi_prefix_length bb.bb_instructions|>` by
    (irule fmp_entry_state_frame >> qexists `fn` >> simp[jump_to_def]) >>
  `t1 = (jump_to lbl tb) with <|vs_vars := t1.vs_vars;
    vs_inst_idx := phi_prefix_length bb'.bb_instructions|>` by
    (irule fmp_entry_state_frame >> qexists `fn'` >> simp[jump_to_def]) >>
  qexists `t1` >> simp[] >>
  gns[venom_state_component_equality, jump_to_def, ptrDisciplineTheory.entry_taint_vars_def,
      o1LowerDloadSharedTheory.ld_shared_agree_def]
QED

Finalise fmp_entry_stage_from_geometry
