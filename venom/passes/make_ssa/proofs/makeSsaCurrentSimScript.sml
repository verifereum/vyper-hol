(*
 * MakeSSA (make_ssa_current_fn, the supply variant the O1 dispatcher runs)
 * keeps a function's runs and the states its frames reach.  The same
 * statements cover both O1 runs: on the first the input has no PHIs, on
 * the second it has the PHIs the first run built.
 *
 * The pass places pruned PHIs at iterated dominance frontiers, renames
 * along the dominator tree (the first definition of a variable keeps its
 * spelling, later ones take fresh supply names), and on PHI input cleans
 * up degenerate PHIs.  A run of the output matches the input's run block
 * for block; the renamed variables hold the values of the originals.
 *
 * Premises (make_ssa_input_ok unfolds to the first seven): definite
 * assignment (fn_defs_reach_uses) makes every PHI value
 * defined at its predecessor's end; all_reachable makes the dominator tree
 * cover every block, so every block is renamed; fn_phi_operands_single_def
 * keeps the liveness the pass uses exact for the variables PHIs read;
 * fn_phis_cover_preds and first_block_no_phi make every PHI the input runs
 * resolvable, so the cleanup's NOP/ASSIGN collapse cannot make the output
 * run where the input fails.  On PHI input, fn_phi_outputs_single_def
 * confines a re-placed PHI for an existing PHI's output to that PHI's own
 * block, and fn_phis_non_degenerate keeps every existing PHI a PHI through
 * cleanup, so it defines its new name before the collapsed copy reads it.
 * Every PHI's operand labels are distinct CFG predecessors of its block,
 * so the PHI the output enters resolves to the input PHI's operand.
 *)
Theory makeSsaCurrentSim
Ancestors
  o1PassLift makeSsaCurrentDefs venomWf cfgWf venomInst irSupply
  unitShapeDefs o1PassContract makeSsaCurrentLockstep o1FrameLockstep
  makeSsaCurrentForwardBlock makeSsaCurrentEdgePrefix
  makeSsaCurrentSuccessorRelation makeSsaCurrentPrefixTransport
  venomExecSemantics passSimulationDefs simplifyCfgBypassRootedEntry
  makeSsaCurrentCopyPrefixRuntime makeSsaCurrentEntryPrefix list rich_list

(* Terminating runs of the input and the output correspond. *)
Theorem make_ssa_current_fn_fn_bisim:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_bisim fn fn'
Proof
  cheat
QED

(* Every state a frame of the output reaches corresponds to one a frame of
   the input reaches, with the same alloca frame and memory ranges. *)
Theorem make_ssa_current_fn_frame_sim:
  ctx_bisim C C' /\
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  frame_sim L C C' fn fn'
Proof
  strip_tac >> drule_all make_ssa_current_fn_frame_lockstep >>
  simp[frame_lockstep_def] >> strip_tac >>
  simp[frame_sim_def] >> rpt strip_tac >>
  qpat_x_assum `!L. ?R. _` (qspec_then `L` strip_assume_tac) >>
  drule_all frame_reach_lockstep_rel >> strip_tac >>
  rename1 `R p (inst,st) sg (inst',st')` >>
  drule_all lockstep_rel >> strip_tac >>
  qexistsl_tac [`inst`, `st`] >> simp[] >>
  `execution_frame st' = execution_frame st` by fs[state_rel_def] >>
  Cases_on `p`
  >- (fs[] >> drule_all inst_mem_ranges_pair >> strip_tac >>
      simp[mem_corr_def, call_corr_def] >>
      strip_tac >>
      `inst_wf inst` by
        (fs[contextCodegenRelTheory.active_inst_def, fn_inst_wf_def, listTheory.EVERY_MEM] >>
         metis_tac[listTheory.EL_MEM]) >>
      `?nm ops. inst.inst_operands = Label nm :: ops` by
        (gvs[inst_pair_def] >> fs[inst_wf_def] >> gvs[]) >>
      drule_all inst_pair_ops >>
      fs[ops_pair_def, inst_pair_def, venomExecSemanticsTheory.decode_invoke_def,
         AllCaseEqs(), listTheory.LIST_REL_CONS2, op_rename_label] >>
      `y = Label nm` by (Cases_on `y` >> gvs[op_rename_def]) >>
      gvs[] >> metis_tac[eval_operands_rel]) >>
  fs[] >> simp[mem_corr_def, call_corr_def,
    unitMemInvTheory.inst_mem_ranges_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def]
QED

Theorem current_prepared_run_forward[local]:
  !fuel raw raw' post post' done l old bb' pre copies.
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  entry_block fn = SOME eb /\ wf_function fn' /\ wf_ssa fn' /\ fn_inst_wf fn' /\
  lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l fn'.fn_blocks = SOME bb' /\
  A l = current_block_annotations old pre /\
  LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
  raw.vs_current_bb = l /\ raw'.vs_current_bb = l /\
  enters_block fn raw post /\ enters_block fn' raw' post' /\
  post.vs_inst_idx = LENGTH (collect_phis old.bb_instructions) /\
  copies = TAKE (LENGTH pre + LENGTH (collect_phis old.bb_instructions) -
    phi_prefix_length bb'.bb_instructions)
    (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions) /\
  current_prefix_steps (PRE fuel) C copies post' done /\
  done.vs_inst_idx = LENGTH pre + LENGTH (collect_phis old.bb_instructions) /\
  current_cut_inv fn A renamed H events l
    (LENGTH (collect_phis old.bb_instructions)) post done /\
  strict_dom_vars_defined fn' done /\ fn_reachable fn' l /\
  done.vs_inst_idx <= LENGTH bb'.bb_instructions /\
  (!j x. j < done.vs_inst_idx /\ j < LENGTH bb'.bb_instructions /\
    MEM x (EL j bb'.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x done)) /\
  terminates (run_blocks fuel C fn raw) ==>
  frame_result_rel (run_blocks fuel C fn raw) (run_blocks fuel C fn' raw')
Proof
  Induct >- simp[Once run_blocks_def, terminates_def] >>
  rpt gen_tac >> strip_tac >>
  `run_block fuel C old raw = exec_block fuel C old post` by
    (irule scfg_enters_block_run_block >> qexists `fn` >> simp[]) >>
  `run_block fuel C bb' raw' = exec_block fuel C bb' post'` by
    (irule scfg_enters_block_run_block >> qexists `fn'` >>
     conj_tac >- metis_tac[] >> asm_rewrite_tac[]) >>
  `post.vs_current_bb = l` by
    (qpat_x_assum `enters_block fn raw post` mp_tac >>
     simp[contextCodegenRelTheory.enters_block_def] >> rpt strip_tac >>
     drule venomExecProofsTheory.eval_phis_preserves_current_bb >> simp[]) >>
  `LENGTH (collect_phis old.bb_instructions) <= LENGTH old.bb_instructions` by
    simp[makeSsaCurrentDemandDominanceTheory.current_collect_phis_length] >>
  `LENGTH (collect_phis old.bb_instructions) <= LENGTH (collect_phis old.bb_instructions)` by simp[] >>
  `post'.vs_inst_idx = phi_prefix_length bb'.bb_instructions` by
    (qpat_x_assum `enters_block fn' raw' post'` mp_tac >>
     qpat_x_assum `fn' = _` SUBST_ALL_TAC >>
     simp[contextCodegenRelTheory.enters_block_def] >> rpt strip_tac >>
     fs[]) >>
  `exec_block fuel C bb' post' = exec_block fuel C bb' done` by
    (irule current_prefix_steps_exec_block >>
     qexists `DROP (LENGTH pre + LENGTH (collect_phis old.bb_instructions) -
       phi_prefix_length bb'.bb_instructions)
       (DROP post'.vs_inst_idx bb'.bb_instructions)` >>
     qexists `copies` >> conj_tac >- simp[TAKE_DROP] >> fs[]) >>
  drule_all current_cut_exec_block_forward >>
  disch_then (qspecl_then [`fuel`, `C`] mp_tac) >>
  Cases_on `exec_block fuel C old post` >>
  simp[IgnAsm `fn' = _`] >> rpt strip_tac >>
  qpat_x_assum `terminates _` mp_tac >>
  simp[run_blocks_unfold, terminates_def, IgnAsm `fn' = _`]
  >- suspend "ok" >>
  Cases_on `exec_block fuel C bb' done` >>
  fs[frame_result_rel_def, IgnAsm `fn' = _`]
QED

Resume current_prepared_run_forward[ok]:
  `t'.vs_halted = v.vs_halted` by
    fs[makeSsaCurrentCutInvTheory.current_cut_inv_def, state_rel_def,
       stateFrameTheory.execution_frame_def] >>
  Cases_on `v.vs_halted`
  >- (fs[makeSsaCurrentCutInvTheory.current_cut_inv_def, state_rel_def] >>
      simp[frame_result_rel_def]) >>
  simp[IgnAsm `fn' = _`] >>
  pure_rewrite_tac[GSYM terminates_def] >>
  `wf_function fn /\ fn_inst_wf fn` by
    fs[makeSsaCurrentWfSsaTheory.current_wf_phi_context_def] >>
  `MEM old fn.fn_blocks /\ old.bb_label = l` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM,
      venomExecProofsTheory.lookup_block_label] >>
  `v.vs_prev_bb = SOME l` by
    (drule cfgNormSupplySimTheory.supply_run_block_entry_control >>
     disch_then (qspecl_then [`raw`, `v`, `fuel`, `C`, `old`] mp_tac) >>
     simp[IgnAsm `fn' = _`]) >>
  `bb_well_formed old /\ EVERY inst_wf old.bb_instructions` by
    (fs[wf_function_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM v.vs_current_bb (bb_succs old)` by
    (irule venomExecProofsTheory.exec_block_current_bb_in_succs >>
     reverse conj_tac
     >- (conj_tac
         >- (qpat_x_assum `bb_well_formed old` mp_tac >>
             simp[bb_well_formed_def]) >>
         reverse conj_tac >- asm_rewrite_tac[] >>
         qexistsl [`C`, `fuel`, `post`] >> simp[IgnAsm `fn' = _`]) >>
     qpat_x_assum `bb_well_formed old` mp_tac >>
     pure_rewrite_tac[bb_well_formed_def] >> rpt strip_tac >>
     `i < LENGTH old.bb_instructions` by decide_tac >>
     `i = PRE (LENGTH old.bb_instructions)` by metis_tac[] >> decide_tac) >>
  `fn_cfg_edge fn l v.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> qexists `old` >> simp[]) >>
  `t'.vs_current_bb = v.vs_current_bb` by
    fs[makeSsaCurrentCutInvTheory.current_cut_inv_def, state_rel_def] >>
  `v.vs_current_bb = v.vs_current_bb` by simp[] >>
  drule_all current_cut_successor_prefix_relation >> strip_tac >>
  strip_tac >>
  `?next. enters_block fn v next` by
    (qpat_x_assum `terminates (run_blocks fuel C fn v)` mp_tac >>
     Cases_on `fuel` >- simp[Once run_blocks_def, terminates_def] >>
     simp[run_blocks_unfold, run_block_def, IgnAsm `fn' = _`] >>
     `(?st. eval_phis v old_h.bb_instructions = OK st) \/
      (?e. eval_phis v old_h.bb_instructions = Error e)` by
       metis_tac[venomExecSemanticsTheory.eval_phis_ok_or_error_defs] >>
     simp[terminates_def] >> strip_tac >>
     simp[contextCodegenRelTheory.enters_block_def] >> metis_tac[]) >>
  `next.vs_inst_idx = LENGTH (collect_phis old_h.bb_instructions)` by
    (qpat_x_assum `enters_block fn v next` mp_tac >>
     simp[contextCodegenRelTheory.enters_block_def] >> rpt strip_tac >>
     simp[makeSsaCurrentPrefixSuffixOwnerTheory.current_prefix_collect_length]) >>
  `MEM bb' fn'.fn_blocks /\ MEM bb'' fn'.fn_blocks` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `EVERY inst_wf bb'.bb_instructions /\ EVERY inst_wf bb''.bb_instructions` by
    (fs[fn_inst_wf_compute, EVERY_MEM] >> metis_tac[]) >>
  `?new_h. lookup_block v.vs_current_bb renamed = SOME new_h /\
    bb'' = if blocks_have_leading_phi fn.fn_blocks
      then simplify_current_phi_block new_h else new_h` by
    (qpat_x_assum `lookup_block v.vs_current_bb fn'.fn_blocks = _` mp_tac >>
     qpat_assum `fn' = _` SUBST1_TAC >>
     simp[makeSsaCurrentCleanupShapeTheory.current_cleanup_if_lookup] >>
     Cases_on `lookup_block v.vs_current_bb renamed` >> simp[] >> metis_tac[]) >>
  `phi_prefix_length new_h.bb_instructions = LENGTH pre' +
    LENGTH (collect_phis old_h.bb_instructions)` by
    (drule_all makeSsaCurrentPrefixSuffixOwnerTheory.current_prefix_actual_endpoint >> simp[]) >>
  `done.vs_current_bb = l` by
    fs[makeSsaCurrentCutInvTheory.current_cut_inv_def, state_rel_def] >>
  `bb'.bb_label = done.vs_current_bb` by
    metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `lookup_block t'.vs_current_bb fn'.fn_blocks = SOME bb''` by metis_tac[] >>
  `fn_reachable fn' v.vs_current_bb` by
    (irule venomExecProofsTheory.fn_reachable_step >> qexists `l` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     pure_rewrite_tac[fn_cfg_edge_def] >> qexists `bb'` >>
     simp[IgnAsm `fn' = _`] >>
     qpat_assum `t'.vs_current_bb = v.vs_current_bb`
       (fn th => pure_once_rewrite_tac[GSYM th]) >>
     irule venomExecProofsTheory.exec_block_current_bb_in_succs >>
     reverse conj_tac
     >- (conj_tac
         >- (qpat_assum `wf_function fn'` mp_tac >>
             pure_rewrite_tac[wf_function_def] >> strip_tac >>
             `bb_well_formed bb'` by metis_tac[] >>
             qpat_x_assum `bb_well_formed bb'` mp_tac >>
             pure_rewrite_tac[bb_well_formed_def] >> metis_tac[]) >>
         reverse conj_tac >- metis_tac[] >>
         qexistsl [`C`, `fuel`, `done`] >> simp[IgnAsm `fn' = _`]) >>
     metis_tac[passSimulationPropsTheory.wf_non_terminator_prefix]) >>
  Cases_on `blocks_have_leading_phi fn.fn_blocks`
  >- suspend "cleaned" >>
  suspend "plain"
QED
Resume current_prepared_run_forward[cleaned]:
  `bb'' = simplify_current_phi_block new_h` by asm_rewrite_tac[] >>
  `fn' = fn with fn_blocks := simplify_current_phis_if T renamed` by
    asm_rewrite_tac[] >>
  `fn_reachable fn' done.vs_current_bb` by metis_tac[] >>
  qabbrev_tac `cs = TAKE
    (phi_prefix_length new_h.bb_instructions - phi_prefix_length bb''.bb_instructions)
    (DROP (phi_prefix_length bb''.bb_instructions) bb''.bb_instructions)` >>
  `cs = TAKE
    (phi_prefix_length new_h.bb_instructions - phi_prefix_length bb''.bb_instructions)
    (DROP (phi_prefix_length bb''.bb_instructions) bb''.bb_instructions)` by
    simp[Abbr `cs`] >>
  drule_all current_completed_edge_cleaned_prefix_total >> strip_tac >>
  `enters_block fn' t'
     (post'' with vs_inst_idx := phi_prefix_length bb''.bb_instructions)` by
    (pure_rewrite_tac[contextCodegenRelTheory.enters_block_def] >>
     qexistsl [`bb''`, `post''`] >> metis_tac[]) >>
  `cs = TAKE (LENGTH pre' + LENGTH (collect_phis old_h.bb_instructions) -
     phi_prefix_length bb''.bb_instructions)
     (DROP (phi_prefix_length bb''.bb_instructions) bb''.bb_instructions)` by
    metis_tac[] >>
  `current_prefix_steps fuel C
     (TAKE (LENGTH pre' + LENGTH (collect_phis old_h.bb_instructions) -
       phi_prefix_length bb''.bb_instructions)
       (DROP (phi_prefix_length bb''.bb_instructions) bb''.bb_instructions))
     (post'' with vs_inst_idx := phi_prefix_length bb''.bb_instructions) done'` by
    metis_tac[] >>
  qpat_assum `!post post' done fuel C. _`
    (drule_all_then strip_assume_tac) >>
  `!j. j < LENGTH cs ==> (EL j cs).inst_opcode = ASSIGN \/
      (EL j cs).inst_opcode = NOP` by
    (rpt strip_tac >>
     `j < phi_prefix_length new_h.bb_instructions -
       phi_prefix_length bb''.bb_instructions /\
      j < LENGTH (DROP (phi_prefix_length bb''.bb_instructions) bb''.bb_instructions)` by
       (qpat_x_assum `j < LENGTH cs` mp_tac >>
        simp[NoAsms, Abbr `cs`, LENGTH_TAKE_EQ, LENGTH_DROP, arithmeticTheory.MIN_DEF] >>
        rpt strip_tac >> decide_tac) >>
     `EL j cs = EL (phi_prefix_length bb''.bb_instructions + j) bb''.bb_instructions` by
       (qpat_assum `j < _ - _` mp_tac >>
        qpat_assum `j < LENGTH (DROP _ _)` mp_tac >>
        simp[NoAsms, Abbr `cs`, EL_TAKE, EL_DROP, arithmeticTheory.ADD_COMM]) >>
     pop_assum SUBST1_TAC >>
     `phi_prefix_length bb''.bb_instructions <=
        phi_prefix_length bb''.bb_instructions + j /\
      phi_prefix_length bb''.bb_instructions + j <
        phi_prefix_length new_h.bb_instructions` by decide_tac >>
     metis_tac[makeSsaCurrentLockstepShapeTheory.simplify_current_phi_block_layout]) >>
  `current_prefix_steps (PRE fuel) C cs
    (post'' with vs_inst_idx := phi_prefix_length bb''.bb_instructions) done'` by
    metis_tac[current_copy_prefix_steps_transport] >>
  first_x_assum irule >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`bb''`, `cs`, `done'`, `v.vs_current_bb`, `old_h`, `next`,
    `post'' with vs_inst_idx := phi_prefix_length bb''.bb_instructions`, `pre'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume current_prepared_run_forward[plain]:
  `bb'' = new_h` by metis_tac[] >>
  `fn_reachable fn' done.vs_current_bb` by metis_tac[] >>
  drule_all current_completed_edge_plain_prefix_total >> strip_tac >>
  `enters_block fn' t'
     (post'' with vs_inst_idx := phi_prefix_length bb''.bb_instructions)` by
    (pure_rewrite_tac[contextCodegenRelTheory.enters_block_def] >>
     qexistsl [`bb''`, `post''`] >> metis_tac[]) >>
  `TAKE (LENGTH pre' + LENGTH (collect_phis old_h.bb_instructions) -
       phi_prefix_length bb''.bb_instructions)
       (DROP (phi_prefix_length bb''.bb_instructions) bb''.bb_instructions) = []` by
    (`LENGTH pre' + LENGTH (collect_phis old_h.bb_instructions) =
      phi_prefix_length bb''.bb_instructions` by metis_tac[] >>
     pop_assum (fn th => simp[NoAsms, th])) >>
  `current_prefix_steps (PRE fuel) C
    (TAKE (LENGTH pre' + LENGTH (collect_phis old_h.bb_instructions) -
       phi_prefix_length bb''.bb_instructions)
       (DROP (phi_prefix_length bb''.bb_instructions) bb''.bb_instructions))
    (post'' with vs_inst_idx := phi_prefix_length bb''.bb_instructions)
    (post'' with vs_inst_idx := phi_prefix_length bb''.bb_instructions)` by
    (qpat_assum `TAKE _ _ = []` (fn th => simp[NoAsms, th, current_prefix_steps_def])) >>
  qpat_assum `!post post' done fuel C. _`
    (drule_all_then strip_assume_tac) >>
  first_x_assum irule >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`bb''`, `[]`,
    `post'' with vs_inst_idx := phi_prefix_length bb''.bb_instructions`,
    `v.vs_current_bb`, `old_h`, `next`,
    `post'' with vs_inst_idx := phi_prefix_length bb''.bb_instructions`, `pre'`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[NoAsms, current_prefix_steps_def] >>
  TRY (first_assum ACCEPT_TAC) >>
  disj1_tac >>
  `LENGTH pre' + LENGTH (collect_phis old_h.bb_instructions) =
    phi_prefix_length bb''.bb_instructions` by metis_tac[] >> decide_tac
QED
Finalise current_prepared_run_forward

Theorem current_entry_run_forward[local]:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\ fn_entry_state fn st /\
  terminates (run_blocks fuel C fn st) ==>
  frame_result_rel (run_blocks fuel C fn st) (run_blocks fuel C fn' st)
Proof
  strip_tac >>
  `?eb. entry_block fn = SOME eb` by
    (Cases_on `fn.fn_blocks` >> fs[fn_entry_state_def, fn_entry_label_def, entry_block_def]) >>
  `ctx_bisim C C` by metis_tac[simplifyCfgSimToolsTheory.ctx_bisim_refl] >>
  drule_all make_ssa_lockstep_phi_context >> strip_tac >>
  drule_all current_target_entry_prefix_initial >> strip_tac >>
  drule_all make_ssa_lockstep_entry_states >> strip_tac >>
  drule_all current_phi_context_entry_cut >> strip_tac >>
  `wf_function fn'` by metis_tac[o1MakeSsaStructuralShapeTheory.make_ssa_current_fn_wf_function] >>
  `fn_inst_wf fn'` by metis_tac[o1MakeSsaFormatsTheory.make_ssa_current_fn_inst_wf] >>
  `wf_ssa fn'` by
    (irule makeSsaCurrentWfSsaTheory.make_ssa_current_fn_wf_ssa >>
     qexistsl_tac [`fn`, `s`, `s'`] >>
     fs[make_ssa_input_ok_def, IgnAsm `fn' = _`] >>
     conj_tac >- first_assum ACCEPT_TAC >> metis_tac[]) >>
  `st.vs_current_bb = eb.bb_label /\ st.vs_inst_idx = 0` by
    (Cases_on `fn.fn_blocks` >> fs[fn_entry_state_def, fn_entry_label_def, entry_block_def]) >>
  irule current_prepared_run_forward >>
  rpt conj_tac >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >- metis_tac[] >>
  qexistsl_tac [`A`, `H`, `bb'`, `[]`, `st`, `events`, `eb.bb_label`, `eb`, `st`, `st`, `[]`, `renamed`, `s`, `s'`] >>
  simp[IgnAsm `fn' = _`, current_prefix_steps_def] >>
  conj_tac >- first_assum ACCEPT_TAC >> metis_tac[]
QED
