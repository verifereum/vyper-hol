Theory gasFocusMakeSsaFinite
Ancestors
  gasFocusMakeSsaLocalEvents gasEvents
  makeSsaCurrentForwardCut makeSsaCurrentForwardBlock makeSsaCurrentForwardRuntime
  makeSsaCurrentEntryPrefix makeSsaCurrentPrefixTransport makeSsaCurrentCopyPrefixRuntime
  makeSsaCurrentWfSsa makeSsaCurrentCutInv makeSsaCurrentLockstep
  makeSsaCurrentCertificate makeSsaCurrentPrefixSuffixOwner
  o1ContractMakeSsaSrc o1PassLift o1FrameLockstep
  venomExecSemantics venomExecProofs venomExecProps venomWf venomInst
  contextCodegenRel stateFrame list rich_list arithmetic makeSsaCurrentCleanupShape makeSsaCurrentLockstepShape simplifyCfgBypassRootedEntry frameGasEvents

(* Every direct ancestor above was checked against the exact NEW HELPER
   GUARD exclusion set in TO_focus_producer-lead-20261116T235445535981Z_m0071_t001;
   none is excluded. *)

Theorem current_invoke_events_pair[local]:
  inst.inst_opcode = INVOKE /\ inst_pair sg inst inst' /\
  state_rel sg st st' ==>
  gas_events_step fuel C owner' inst' st' =
  gas_events_step fuel C owner inst st
Proof
  strip_tac >>
  `inst'.inst_opcode = INVOKE` by fs[inst_pair_def] >>
  Cases_on `decode_invoke inst`
  >- (Cases_on `inst.inst_operands`
      >- (fs[inst_pair_def, gas_events_step_def, decode_invoke_def]) >>
      Cases_on `inst'.inst_operands` >> fs[inst_pair_def] >>
      rename1 `op_rename sg h h'` >>
      Cases_on `h` >> Cases_on `h'` >>
      gvs[op_rename_def, gas_events_step_def, decode_invoke_def]) >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  drule_all current_invoke_decode_args_pair >> strip_tac >>
  `!fn args. setup_callee fn args st' = setup_callee fn args st` by
    (rpt gen_tac >> irule setup_callee_execution_frame >> fs[state_rel_def]) >>
  simp[gas_events_step_def] >>
  Cases_on `lookup_function pair0 C.ctx_functions` >> simp[] >>
  Cases_on `eval_operands pair1 st` >> simp[]
QED

Theorem current_cut_block_events[local]:
  !i st st'.
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l fn'.fn_blocks = SOME bb' /\
  A l = current_block_annotations old pre /\
  LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
  LENGTH (collect_phis old.bb_instructions) <= i /\
  i <= LENGTH old.bb_instructions /\
  st.vs_current_bb = l /\ st.vs_inst_idx = i /\
  st'.vs_inst_idx = LENGTH pre + i /\
  current_cut_inv fn A renamed H events l i st st' ==>
  ?extra.
    gas_events_block fuel C fn'.fn_name bb' st' =
      gas_events_block fuel C fn.fn_name old st ++ extra /\
    (terminates (exec_block fuel C old st) ==> extra = [])
Proof
  measureInduct_on `LENGTH old.bb_instructions - i` >> rpt gen_tac >> strip_tac >>
  Cases_on `i = LENGTH old.bb_instructions`
  >- (qexists `[]` >> simp[Once gas_events_block_def, get_instruction_def] >>
      simp[Once gas_events_block_def, get_instruction_def]) >>
  `i < LENGTH old.bb_instructions` by decide_tac >>
  `inst_wf (EL i old.bb_instructions)` by
    metis_tac[fn_inst_wf_def, lookup_block_MEM, EL_MEM] >>
  drule_all current_cut_inv_ordinary_step_forward >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `bb'' = bb'` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `bb'' = bb'` SUBST_ALL_TAC >>
  `(EL (LENGTH pre + i) bb'.bb_instructions).inst_opcode =
    (EL i old.bb_instructions).inst_opcode` by fs[inst_pair_def] >>
  `gas_events_step fuel C fn'.fn_name
      (EL (LENGTH pre + i) bb'.bb_instructions) st' =
    gas_events_step fuel C fn.fn_name (EL i old.bb_instructions) st` by
    (Cases_on `(EL i old.bb_instructions).inst_opcode = GAS`
     >- (irule make_ssa_paired_gas_site >>
         simp[] >> conj_tac
         >- (qexistsl [`old`, `bb'`, `i`, `l`] >>
             gvs[makeSsaCurrentLockstepTheory.make_ssa_pos_def,
               makeSsaCurrentPrefixSuffixOwnerTheory.current_prefix_collect_length,
               ADD_COMM]) >>
         qexistsl [`s`, `s'`] >> simp[]) >>
     Cases_on `(EL i old.bb_instructions).inst_opcode = INVOKE`
     >- (irule current_invoke_events_pair >>
         fs[current_cut_inv_def] >> metis_tac[]) >>
     simp[gas_events_step_def]) >>
  once_rewrite_tac[gas_events_block_def] >>
  simp[get_instruction_def, Excl "ADD_COMM"] >>
  Cases_on `step_inst fuel C (EL i old.bb_instructions) st`
  >- suspend "ok"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "intret" >>
  suspend "error"
QED

Resume current_cut_block_events[ok]:
  qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >> fs[ADD_COMM] >>
  Cases_on `is_terminator (EL i old.bb_instructions).inst_opcode`
  >- (qexists `[]` >> gvs[]) >>
  `v.vs_current_bb = l` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`v with vs_inst_idx := SUC i`,
    `t' with vs_inst_idx := SUC (i + LENGTH pre)`] mp_tac) >>
  simp[ADD_COMM] >> strip_tac >> qexists `extra` >>
  gvs[APPEND_ASSOC] >> strip_tac >> first_x_assum irule >>
  qpat_x_assum `terminates _` mp_tac >>
  simp[Once (cj 2 run_defs), get_instruction_def]
QED
Resume current_cut_block_events[halt]:
  qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >> fs[ADD_COMM] >>
  Cases_on `step_inst fuel C (EL (i + LENGTH pre) bb'.bb_instructions) st'` >>
  qexists `[]` >> gvs[frame_result_rel_def]
QED
Resume current_cut_block_events[abort]:
  qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >> fs[ADD_COMM] >>
  Cases_on `step_inst fuel C (EL (i + LENGTH pre) bb'.bb_instructions) st'` >>
  qexists `[]` >> gvs[frame_result_rel_def]
QED
Resume current_cut_block_events[intret]:
  qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >> fs[ADD_COMM] >>
  Cases_on `step_inst fuel C (EL (i + LENGTH pre) bb'.bb_instructions) st'` >>
  qexists `[]` >> gvs[frame_result_rel_def]
QED
Resume current_cut_block_events[error]:
  gvs[ADD_COMM] >>
  simp[Once (cj 2 run_defs), get_instruction_def, terminates_not_error]
QED
Finalise current_cut_block_events

Theorem current_prepared_copies_silent[local]:
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  entry_block fn = SOME eb /\ lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l fn'.fn_blocks = SOME bb /\
  A l = current_block_annotations old pre ==>
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE)
    (TAKE (LENGTH pre + LENGTH (collect_phis old.bb_instructions) -
      phi_prefix_length bb.bb_instructions)
      (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions))
Proof
  strip_tac >>
  `?new. lookup_block l renamed = SOME new /\
    bb = if blocks_have_leading_phi fn.fn_blocks then
      simplify_current_phi_block new else new` by
    (qpat_x_assum `lookup_block l fn'.fn_blocks = _` mp_tac >>
     qpat_x_assum `fn' = _` SUBST_ALL_TAC >>
     simp[current_cleanup_if_lookup] >>
     Cases_on `lookup_block l renamed` >> simp[] >> metis_tac[]) >>
  drule_all current_prefix_actual_endpoint >> strip_tac >>
  Cases_on `blocks_have_leading_phi fn.fn_blocks`
  >- (fs[] >> rewrite_tac[EVERY_EL] >> qx_gen_tac `j` >> strip_tac >>
      `j < phi_prefix_length new.bb_instructions -
         phi_prefix_length bb.bb_instructions /\
       j < LENGTH (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
        (gvs[LENGTH_TAKE_EQ, MIN_DEF] >> decide_tac) >>
      `EL j (TAKE (phi_prefix_length new.bb_instructions -
          phi_prefix_length bb.bb_instructions)
          (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) =
        EL (phi_prefix_length bb.bb_instructions + j) bb.bb_instructions` by
        gvs[EL_TAKE, EL_DROP, ADD_COMM] >>
      pop_assum SUBST1_TAC >>
      `phi_prefix_length bb.bb_instructions <=
         phi_prefix_length bb.bb_instructions + j /\
       phi_prefix_length bb.bb_instructions + j <
         phi_prefix_length new.bb_instructions` by decide_tac >>
      `(EL (phi_prefix_length bb.bb_instructions + j) bb.bb_instructions).inst_opcode = ASSIGN \/
       (EL (phi_prefix_length bb.bb_instructions + j) bb.bb_instructions).inst_opcode = NOP` by
        metis_tac[simplify_current_phi_block_layout] >>
      gvs[LENGTH_DROP, EL_TAKE, EL_DROP, ADD_COMM]) >>
  gvs[]
QED

Theorem current_events_enters_block[local]:
  enters_block fn raw post /\
  lookup_block raw.vs_current_bb fn.fn_blocks = SOME bb ==>
  gas_events_blocks (SUC k) C fn raw =
    gas_events_block k C fn.fn_name bb post ++
    (case exec_block k C bb post of
       OK t => if t.vs_halted then [] else gas_events_blocks k C fn t
     | _ => [])
Proof
  simp[enters_block_def] >> rpt strip_tac >> gvs[] >>
  CONV_TAC (LHS_CONV (REWR_CONV gas_events_blocks_def)) >> simp[]
QED

Theorem current_prepared_finite_events[local]:
  (!s fn renamed s' A H events fn' eb l old bb raw post done k C t t' next.
    current_wf_phi_context s fn renamed s' A H events /\
    fn' = fn with fn_blocks := simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    entry_block fn = SOME eb /\ wf_function fn' /\ wf_ssa fn' /\ fn_inst_wf fn' /\
    lookup_block l fn.fn_blocks = SOME old /\ lookup_block l fn'.fn_blocks = SOME bb /\
    raw.vs_current_bb = l /\ enters_block fn raw post /\ done.vs_current_bb = l /\
    strict_dom_vars_defined fn' done /\ fn_reachable fn' l /\
    done.vs_inst_idx <= LENGTH bb.bb_instructions /\
    (!j x. j < done.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\ MEM x (EL j bb.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x done)) /\
    exec_block k C old post = OK t /\ exec_block k C bb done = OK t' /\
    current_cut_inv fn A renamed H events l (LENGTH old.bb_instructions) t t' /\
    ~t.vs_halted /\ enters_block fn t next ==>
    ?old_h bb_h pre_h post_h done_h.
      lookup_block t.vs_current_bb fn.fn_blocks = SOME old_h /\
      lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb_h /\
      A t.vs_current_bb = current_block_annotations old_h pre_h /\
      LENGTH bb_h.bb_instructions = LENGTH pre_h + LENGTH old_h.bb_instructions /\
      next.vs_inst_idx = LENGTH (collect_phis old_h.bb_instructions) /\
      enters_block fn' t' post_h /\
      post_h.vs_inst_idx = phi_prefix_length bb_h.bb_instructions /\
      current_prefix_steps k C
        (TAKE (LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) - phi_prefix_length bb_h.bb_instructions)
          (DROP (phi_prefix_length bb_h.bb_instructions) bb_h.bb_instructions)) post_h done_h /\
      (!j. j < LENGTH (TAKE (LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) - phi_prefix_length bb_h.bb_instructions)
          (DROP (phi_prefix_length bb_h.bb_instructions) bb_h.bb_instructions)) ==>
        (EL j (TAKE (LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) - phi_prefix_length bb_h.bb_instructions)
          (DROP (phi_prefix_length bb_h.bb_instructions) bb_h.bb_instructions))).inst_opcode = ASSIGN \/
        (EL j (TAKE (LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) - phi_prefix_length bb_h.bb_instructions)
          (DROP (phi_prefix_length bb_h.bb_instructions) bb_h.bb_instructions))).inst_opcode = NOP) /\
      current_cut_inv fn A renamed H events t.vs_current_bb (LENGTH (collect_phis old_h.bb_instructions)) next done_h /\
      done_h.vs_inst_idx = LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) /\
      done_h.vs_current_bb = t.vs_current_bb /\
      strict_dom_vars_defined fn' done_h /\ fn_reachable fn' t.vs_current_bb /\
      done_h.vs_inst_idx <= LENGTH bb_h.bb_instructions /\
      (!j x. j < done_h.vs_inst_idx /\ j < LENGTH bb_h.bb_instructions /\ MEM x (EL j bb_h.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x done_h))) ==>
  !fuel raw raw' post post' done l old bb' pre copies.
    make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
    first_block_no_preds fn /\ first_block_no_phi fn /\
    ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
    make_ssa_current_fn s fn = (fn',s') /\
    current_wf_phi_context s fn renamed s' A H events /\
    fn' = fn with fn_blocks := simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    entry_block fn = SOME eb /\ wf_function fn' /\ wf_ssa fn' /\ fn_inst_wf fn' /\
    lookup_block l fn.fn_blocks = SOME old /\ lookup_block l fn'.fn_blocks = SOME bb' /\
    A l = current_block_annotations old pre /\
    LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
    raw.vs_current_bb = l /\ raw'.vs_current_bb = l /\
    enters_block fn raw post /\ enters_block fn' raw' post' /\
    post.vs_inst_idx = LENGTH (collect_phis old.bb_instructions) /\
    copies = TAKE (LENGTH pre + LENGTH (collect_phis old.bb_instructions) - phi_prefix_length bb'.bb_instructions)
      (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions) /\
    current_prefix_steps (PRE fuel) C copies post' done /\
    done.vs_inst_idx = LENGTH pre + LENGTH (collect_phis old.bb_instructions) /\
    current_cut_inv fn A renamed H events l (LENGTH (collect_phis old.bb_instructions)) post done /\
    strict_dom_vars_defined fn' done /\ fn_reachable fn' l /\
    done.vs_inst_idx <= LENGTH bb'.bb_instructions /\
    (!j x. j < done.vs_inst_idx /\ j < LENGTH bb'.bb_instructions /\ MEM x (EL j bb'.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x done)) ==>
    ?extra.
      gas_events_blocks fuel C fn' raw' = gas_events_blocks fuel C fn raw ++ extra /\
      (terminates (run_blocks fuel C fn raw) ==>
        extra = [] /\ frame_result_rel (run_blocks fuel C fn raw) (run_blocks fuel C fn' raw'))
Proof
  disch_then (mk_asm "successor") >>
  Induct >- simp[gas_events_blocks_def, Once run_blocks_def, terminates_not_error] >>
  rpt gen_tac >> strip_tac >>
  `run_block fuel C old raw = exec_block fuel C old post` by
    (irule scfg_enters_block_run_block >> qexists `fn` >> simp[]) >>
  `run_block fuel C bb' raw' = exec_block fuel C bb' post'` by
    (irule scfg_enters_block_run_block >> qexists `fn'` >>
     conj_tac >- metis_tac[] >> asm_rewrite_tac[]) >>
  `post.vs_current_bb = l` by
    (qpat_x_assum `enters_block fn raw post` mp_tac >>
     simp[enters_block_def] >> rpt strip_tac >>
     drule eval_phis_preserves_current_bb >> simp[]) >>
  `LENGTH (collect_phis old.bb_instructions) <= LENGTH old.bb_instructions` by
    simp[livenessTransferProofsTheory.current_collect_phis_length] >>
  `LENGTH (collect_phis old.bb_instructions) <= LENGTH (collect_phis old.bb_instructions)` by simp[] >>
  `post'.vs_inst_idx = phi_prefix_length bb'.bb_instructions` by
    (qpat_x_assum `enters_block fn' raw' post'` mp_tac >>
     simp[enters_block_def] >> rpt strip_tac >> gvs[]) >>
  `DROP post'.vs_inst_idx bb'.bb_instructions = copies ++
    DROP (LENGTH pre + LENGTH (collect_phis old.bb_instructions) - phi_prefix_length bb'.bb_instructions)
      (DROP post'.vs_inst_idx bb'.bb_instructions)` by simp[TAKE_DROP] >>
  `exec_block fuel C bb' post' = exec_block fuel C bb' done` by
    (irule current_prefix_steps_exec_block >>
     goal_assum (drule_at Any) >> gvs[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE) copies` by
    (drule_all current_prepared_copies_silent >> simp[]) >>
  `gas_events_block fuel C fn'.fn_name bb' post' = gas_events_block fuel C fn'.fn_name bb' done` by
    (irule make_ssa_copy_prefix_gas_events >>
     goal_assum (drule_at Any) >> gvs[] >>
     qexists `DROP (LENGTH pre + LENGTH (collect_phis old.bb_instructions) - phi_prefix_length bb'.bb_instructions)
       (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions)` >>
     simp[TAKE_DROP]) >>
  `gas_events_blocks (SUC fuel) C fn raw = gas_events_block fuel C fn.fn_name old post ++
    (case exec_block fuel C old post of OK t => if t.vs_halted then [] else gas_events_blocks fuel C fn t | _ => [])` by
    (irule current_events_enters_block >> simp[]) >>
  `gas_events_blocks (SUC fuel) C fn' raw' = gas_events_block fuel C fn'.fn_name bb' done ++
    (case exec_block fuel C bb' done of OK t => if t.vs_halted then [] else gas_events_blocks fuel C fn' t | _ => [])` by
    (drule_at (Pos hd) current_events_enters_block >>
     (bossLib.gvs [])) >>
  drule_all current_cut_block_events >> disch_then (qspecl_then [`fuel`, `C`] strip_assume_tac) >>
  drule_all current_cut_exec_block_forward >> disch_then (qspecl_then [`fuel`, `C`] mp_tac) >>
  Cases_on `exec_block fuel C old post` >> simp[] >> strip_tac
  >- suspend "ok"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "intret" >> suspend "error"
QED

Resume current_prepared_finite_events[ok]:
  `t'.vs_halted = v.vs_halted` by
    fs[current_cut_inv_def, state_rel_def, execution_frame_def] >>
  `extra = []` by fs[terminates_not_error] >>
  Cases_on `v.vs_halted`
  >- (qexists `[]` >> gvs[run_blocks_unfold, frame_result_rel_def,
        current_cut_inv_def, state_rel_def]) >>
  Cases_on `?next. enters_block fn v next`
  >- suspend "successor" >>
  suspend "no_entry"
QED
Resume current_prepared_finite_events[halt]:
  Cases_on `exec_block fuel C bb' done` >>
  gvs[run_blocks_unfold, frame_result_rel_def, terminates_not_error]
QED
Resume current_prepared_finite_events[abort]:
  Cases_on `exec_block fuel C bb' done` >>
  gvs[run_blocks_unfold, frame_result_rel_def, terminates_not_error]
QED
Resume current_prepared_finite_events[intret]:
  Cases_on `exec_block fuel C bb' done` >>
  gvs[run_blocks_unfold, frame_result_rel_def, terminates_not_error]
QED
Resume current_prepared_finite_events[error]:
  gvs[run_blocks_unfold, terminates_not_error]
QED
Resume current_prepared_finite_events[successor]:
  pop_assum strip_assume_tac >>
  `done.vs_current_bb = l` by fs[current_cut_inv_def, state_rel_def] >>
  asm "successor" drule_all >> strip_tac >>
  `current_prefix_steps (PRE fuel) C
     (TAKE (LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) - phi_prefix_length bb_h.bb_instructions)
       (DROP (phi_prefix_length bb_h.bb_instructions) bb_h.bb_instructions)) post_h done_h` by
    (irule current_copy_prefix_steps_transport >>
     simp[] >> qexistsl [`C`, `fuel`] >> simp[]) >>
  `t'.vs_current_bb = v.vs_current_bb` by fs[current_cut_inv_def, state_rel_def] >>
  qpat_x_assum `!raw raw' post post' done l old bb' pre copies. _`
    (qspec_then `v` mp_tac) >> simp[IgnAsm `fn' = _`] >>
  disch_then (qspecl_then [`t'`, `next`, `post_h`, `done_h`, `pre_h`] mp_tac) >>
  simp[IgnAsm `fn' = _`] >> (impl_tac >- (gvs[] >> (gvs[]))) >> strip_tac >>
  qexists `extra'` >> gvs[run_blocks_unfold]
QED
Resume current_prepared_finite_events[no_entry]:
  `gas_events_blocks fuel C fn v = [] /\
   ~terminates (run_blocks fuel C fn v)` by
    (qpat_x_assum `~?next. enters_block fn v next` mp_tac >>
     simp[enters_block_def] >> strip_tac >>
     Cases_on `fuel` >> simp[Once gas_events_blocks_def, Once run_blocks_def, terminates_not_error] >>
     Cases_on `lookup_block v.vs_current_bb fn.fn_blocks` >> simp[] >>
     rename1 `lookup_block v.vs_current_bb fn.fn_blocks = SOME b` >>
     qspecl_then [`v`, `b.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
     gvs[] >> metis_tac[]) >>
  qexists `gas_events_blocks fuel C fn' t'` >> gvs[run_blocks_unfold]
QED
Finalise current_prepared_finite_events

Theorem current_focus_same_context_events:
  (!s fn renamed s' A H events fn' eb l old bb raw post done k C t t' next.
    current_wf_phi_context s fn renamed s' A H events /\
    fn' = fn with fn_blocks := simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    entry_block fn = SOME eb /\ wf_function fn' /\ wf_ssa fn' /\ fn_inst_wf fn' /\
    lookup_block l fn.fn_blocks = SOME old /\ lookup_block l fn'.fn_blocks = SOME bb /\
    raw.vs_current_bb = l /\ enters_block fn raw post /\ done.vs_current_bb = l /\
    strict_dom_vars_defined fn' done /\ fn_reachable fn' l /\
    done.vs_inst_idx <= LENGTH bb.bb_instructions /\
    (!j x. j < done.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\ MEM x (EL j bb.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x done)) /\
    exec_block k C old post = OK t /\ exec_block k C bb done = OK t' /\
    current_cut_inv fn A renamed H events l (LENGTH old.bb_instructions) t t' /\
    ~t.vs_halted /\ enters_block fn t next ==>
    ?old_h bb_h pre_h post_h done_h.
      lookup_block t.vs_current_bb fn.fn_blocks = SOME old_h /\
      lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb_h /\
      A t.vs_current_bb = current_block_annotations old_h pre_h /\
      LENGTH bb_h.bb_instructions = LENGTH pre_h + LENGTH old_h.bb_instructions /\
      next.vs_inst_idx = LENGTH (collect_phis old_h.bb_instructions) /\
      enters_block fn' t' post_h /\
      post_h.vs_inst_idx = phi_prefix_length bb_h.bb_instructions /\
      current_prefix_steps k C
        (TAKE (LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) - phi_prefix_length bb_h.bb_instructions)
          (DROP (phi_prefix_length bb_h.bb_instructions) bb_h.bb_instructions)) post_h done_h /\
      (!j. j < LENGTH (TAKE (LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) - phi_prefix_length bb_h.bb_instructions)
          (DROP (phi_prefix_length bb_h.bb_instructions) bb_h.bb_instructions)) ==>
        (EL j (TAKE (LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) - phi_prefix_length bb_h.bb_instructions)
          (DROP (phi_prefix_length bb_h.bb_instructions) bb_h.bb_instructions))).inst_opcode = ASSIGN \/
        (EL j (TAKE (LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) - phi_prefix_length bb_h.bb_instructions)
          (DROP (phi_prefix_length bb_h.bb_instructions) bb_h.bb_instructions))).inst_opcode = NOP) /\
      current_cut_inv fn A renamed H events t.vs_current_bb (LENGTH (collect_phis old_h.bb_instructions)) next done_h /\
      done_h.vs_inst_idx = LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) /\
      done_h.vs_current_bb = t.vs_current_bb /\
      strict_dom_vars_defined fn' done_h /\ fn_reachable fn' t.vs_current_bb /\
      done_h.vs_inst_idx <= LENGTH bb_h.bb_instructions /\
      (!j x. j < done_h.vs_inst_idx /\ j < LENGTH bb_h.bb_instructions /\ MEM x (EL j bb_h.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x done_h))) ==>
  !s fn fn' s' st fuel C.
    make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
    first_block_no_preds fn /\ first_block_no_phi fn /\
    ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
    make_ssa_current_fn s fn = (fn',s') /\ fn_entry_state fn st ==>
    ?extra.
      gas_events_blocks fuel C fn' st = gas_events_blocks fuel C fn st ++ extra /\
      (terminates (run_blocks fuel C fn st) ==>
        extra = [] /\ frame_result_rel (run_blocks fuel C fn st) (run_blocks fuel C fn' st))
Proof
  disch_then (mk_asm "successor") >> rpt gen_tac >> strip_tac >>
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
     qexistsl [`fn`, `s`, `s'`] >>
     fs[o1PassContractTheory.make_ssa_input_ok_def, IgnAsm `fn' = _`] >>
     conj_tac >- first_assum ACCEPT_TAC >> metis_tac[]) >>
  `st.vs_current_bb = eb.bb_label /\ st.vs_inst_idx = 0` by
    (Cases_on `fn.fn_blocks` >> fs[fn_entry_state_def, fn_entry_label_def, entry_block_def]) >>
  `bb' = bb` by gvs[IgnAsm `fn' = _`] >>
  qpat_x_assum `bb' = bb` SUBST_ALL_TAC >>
  irule current_prepared_finite_events >>
  (conj_tac >- asm "successor" ACCEPT_TAC) >>
  simp[IgnAsm `fn' = _`] >>
  goal_assum (drule_at (Pat `current_wf_phi_context _ _ _ _ _ _ _`)) >>
  simp[IgnAsm `fn' = _`] >>
  qexistsl [`st`, `st`, `st`] >>
  simp[IgnAsm `fn' = _`, current_prefix_steps_def] >>
  first_assum ACCEPT_TAC
QED
