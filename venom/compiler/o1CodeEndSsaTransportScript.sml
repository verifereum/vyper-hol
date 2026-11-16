Theory o1CodeEndSsaTransport
Ancestors
  o1FrameLockstep o1ContractMakeSsa o1PassContract
  venomPassSchedule unitTransformDefs
  concretizePtrCoverageStaticMemReachability frameRawProjection
  o1CodeEndSsaProtectedCleanup o1CodeEndSsaTraceOwnership o1CodeEndSsaRead
  o1LabelFlowMiddleSsa o1MakeSsaOwnership o1MakeSsaVisitTrace
  makeSsaCurrentLockstep makeSsaCurrentWfSsa makeSsaCurrentTreeTrace makeSsaDefs
  codegenSymRel venomInst venomWf list pair pred_set

Theorem code_end_ssa_runtime_owner[local]:
  current_wf_phi_context supply f renamed supply' A H events /\
  make_ssa_input_ok f /\ fn_entry_label f = SOME entry /\
  (!x. code_end_var f x ==> ?d op. MEM d (fn_insts f) /\
    d.inst_opcode = ADD /\ d.inst_operands = [op; Label "code_end"] /\
    d.inst_outputs = [x] /\
    (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
    (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
      MEM (Var x) j.inst_operands ==>
      j.inst_opcode = CODECOPY /\
      (?dst sz. j.inst_operands = [dst; Var x; sz] /\
        dst <> Var x /\ sz <> Var x) /\
      ?a b. bb.bb_instructions = a ++ [d;j] ++ b)) /\
  g = f with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi f.fn_blocks) renamed /\
  code_end_var g n /\ MEM (token,v,n) H ==>
  code_end_var f v
Proof
  strip_tac >>
  qpat_x_assum `current_wf_phi_context _ _ _ _ _ _ _` mp_tac >>
  simp[current_wf_phi_context_def, current_wf_precleanup_certificate_def] >>
  strip_tac >> gvs[] >>
  drule (cj 1 current_tree_trace_projection) >> strip_tac >>
  qabbrev_tac `ve = SND (visit_blocks [] si
    (init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) (current_dom_postorder f))))))
    ins (current_succ_map f) (current_dom_tree f))` >>
  `visit_blocks [] si
    (init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) (current_dom_postorder f))))))
    ins (current_succ_map f) (current_dom_tree f) = ((ctrs,supply',renamed),ve)` by
    (simp[Abbr `ve`] >> metis_tac[visit_erasure, PAIR, FST]) >>
  drule_all prepared_actual_tree >> strip_tac >>
  drule_all prepared_visit_common_owner >>
  disch_then (qx_choose_then `Hf` strip_assume_tac) >>
  `EVERY (\e. LIST_REL (\i j. LIST_REL (\v n. (n,v) IN Hf)
      i.inst_outputs j.inst_outputs) e.sve_before e.sve_after) ve` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  `(n,v) IN Hf` by
    (drule_all code_end_actual_trace_owner_alignment >> simp[]) >>
  `?x. (n,x) IN Hf /\ code_end_var f x` by
    (irule (cj 1 code_end_ssa_protected_facts) >>
     goal_assum $ drule_at Any >> simp[] >> metis_tac[]) >>
  `x = v` by metis_tac[current_name_owner_unique] >> gvs[]
QED

Theorem code_end_ssa_read_reflect[local]:
  current_wf_phi_context supply f renamed supply' A H events /\
  make_ssa_input_ok f /\ fn_entry_label f = SOME entry /\
  (!x. code_end_var f x ==> ?d op. MEM d (fn_insts f) /\
    d.inst_opcode = ADD /\ d.inst_operands = [op; Label "code_end"] /\
    d.inst_outputs = [x] /\
    (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
    (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
      MEM (Var x) j.inst_operands ==>
      j.inst_opcode = CODECOPY /\
      (?dst sz. j.inst_operands = [dst; Var x; sz] /\
        dst <> Var x /\ sz <> Var x) /\
      ?a b. bb.bb_instructions = a ++ [d;j] ++ b)) /\
  g = f with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi f.fn_blocks) renamed /\
  ctx_bisim C C' /\
  current_lockstep_rel f g A renamed H events p (i,s) sg (j,t) /\
  j.inst_opcode = CODECOPY /\ j.inst_operands = [dst; Var n; sz] /\
  code_end_var g n /\ eval_operand (Var n) t = SOME w ==>
  ?a v b. i.inst_opcode = CODECOPY /\ i.inst_operands = [a; Var v; b] /\
    code_end_var f v /\ eval_operand (Var v) s = SOME w /\
    t.vs_labels = s.vs_labels
Proof
  strip_tac >>
  `?eb. entry_block f = SOME eb` by
    fs[fn_entry_label_def, AllCaseEqs()] >>
  drule_all code_end_ssa_paired_read >> strip_tac >>
  drule_all code_end_ssa_runtime_owner >> strip_tac >>
  metis_tac[]
QED

Theorem code_end_ssa_certified_context[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  EVERY (\f. !x. code_end_var f x ==> ?d op. MEM d (fn_insts f) /\
    d.inst_opcode = ADD /\ d.inst_operands = [op; Label "code_end"] /\
    d.inst_outputs = [x] /\
    (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
    (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
      MEM (Var x) j.inst_operands ==>
      j.inst_opcode = CODECOPY /\
      (?dst sz. j.inst_operands = [dst; Var x; sz] /\
        dst <> Var x /\ sz <> Var x) /\
      ?a b. bb.bb_instructions = a ++ [d;j] ++ b)) C.ctx_functions ==>
  code_end_certified_ctx
    (\f g pos R. !p i s sg j t dst n sz w.
      R p (i,s) sg (j,t) /\ j.inst_opcode = CODECOPY /\
      j.inst_operands = [dst; Var n; sz] /\ code_end_var g n /\
      eval_operand (Var n) t = SOME w ==>
      ?a v b. i.inst_opcode = CODECOPY /\ i.inst_operands = [a; Var v; b] /\
        code_end_var f v /\ eval_operand (Var v) s = SOME w /\
        t.vs_labels = s.vs_labels) L C C'
Proof
  strip_tac >>
  `ctx_bisim C C'` by metis_tac[make_ssa_stage_bisim] >>
  drule make_ssa_stage_functions >> strip_tac >>
  simp[code_end_certified_ctx_def] >>
  rewrite_tac[LIST_REL_EL_EQN] >> conj_tac
  >- metis_tac[LIST_REL_LENGTH] >>
  gen_tac >> strip_tac >>
  drule_all make_ssa_stage_el >> strip_tac >>
  qabbrev_tac `f = EL n C.ctx_functions` >>
  qabbrev_tac `g = EL n C'.ctx_functions` >>
  `MEM f C.ctx_functions` by simp[Abbr `f`, EL_MEM] >>
  rename1 `make_ssa_current_fn supply f = (g,supply')` >>
  `?eb. entry_block f = SOME eb` by
    (Cases_on `f.fn_blocks` >>
     fs[wf_function_def, fn_has_entry_def, entry_block_def]) >>
  drule_all make_ssa_lockstep_phi_context >>
  disch_then (qx_choosel_then [`renamed`,`A`,`H`,`events`] strip_assume_tac) >>
  BETA_TAC >> conj_tac
  >- gvs[] >>
  conj_tac
  >- metis_tac[o1MakeSsaCfgTheory.make_ssa_current_fn_entry_label] >>
  qexistsl [`make_ssa_pos f g`,
    `current_lockstep_rel f g A renamed H events`] >>
  simp[] >> conj_tac
  >- (irule current_lockstep_sim >> metis_tac[]) >>
  rpt strip_tac >> irule code_end_ssa_read_reflect >>
  goal_assum $ drule_at Any >> simp[] >>
  fs[EVERY_MEM, fn_entry_label_def] >> metis_tac[MEM_EL]
QED

Theorem code_end_ssa_stage_bound[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  EVERY (\f. !x. code_end_var f x ==> ?d op. MEM d (fn_insts f) /\
    d.inst_opcode = ADD /\ d.inst_operands = [op; Label "code_end"] /\
    d.inst_outputs = [x] /\
    (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
    (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
      MEM (Var x) j.inst_operands ==>
      j.inst_opcode = CODECOPY /\
      (?dst sz. j.inst_operands = [dst; Var x; sz] /\
        dst <> Var x /\ sz <> Var x) /\
      ?a b. bb.bb_instructions = a ++ [d;j] ++ b)) C.ctx_functions /\
  code_end_offset_ok (raw_reachable vs) C ==>
  code_end_offset_ok (raw_reachable vs) C'
Proof
  strip_tac >> drule_all code_end_ssa_certified_context >>
  disch_then (qspec_then `vs.vs_labels` assume_tac) >>
  simp[code_end_offset_ok_def] >> rpt strip_tac >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  drule_all code_end_frame_reachable_certified >>
  disch_then (qx_choosel_then
    [`source_stack`,`source_ghost`,`source_token`,`source_fn`,`source_inst`,
     `source_state`,`source_pos`,`target_ghost`,`positions`,`relation`]
    strip_assume_tac) >>
  `raw_reachable vs C source_fn source_inst source_state` by
    (irule frame_reachable_raw >> reverse conj_tac
     >- (goal_assum $ drule_at Any) >>
     fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM]) >>
  fs[] >> first_x_assum drule_all >> strip_tac >>
  fs[code_end_offset_ok_def] >> metis_tac[]
QED

Theorem make_ssa_code_end_run_contract:
  o1_stage_contract rpolicy D (CFP_Simple VP_MakeSSA)
    (o1_walk_view rpolicy 4) (o1_pre 4)
    (\C vs. o1_inv D 4 C vs /\
      code_end_offset_ok (raw_reachable vs) C /\
      EVERY (\f. !x. code_end_var f x ==> ?d op. MEM d (fn_insts f) /\
        d.inst_opcode = ADD /\ d.inst_operands = [op; Label "code_end"] /\
        d.inst_outputs = [x] /\
        (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
        (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
          MEM (Var x) j.inst_operands ==>
          j.inst_opcode = CODECOPY /\
          (?dst sz. j.inst_operands = [dst; Var x; sz] /\
            dst <> Var x /\ sz <> Var x) /\
          ?a b. bb.bb_instructions = a ++ [d;j] ++ b)) C.ctx_functions)
    (\C vs. o1_inv D 5 C vs /\ code_end_offset_ok (raw_reachable vs) C)
Proof
  mp_tac make_ssa_run_contract_2 >>
  simp[o1_run_contract_def, o1_fn_passes_def, o1_stage_contract_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `ctx_sim_fuel (pass_fuel (CFP_Simple VP_MakeSSA) C') D C C' vs vs /\
   o1_inv D 5 C' vs` by metis_tac[] >>
  simp[] >> irule code_end_ssa_stage_bound >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
    gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  simp[] >> goal_assum $ drule_at Any >> gvs[o1_inv_def] >>
  metis_tac[]
QED
