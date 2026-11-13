(* Every frame observation has a completed-block and local-prefix decomposition. *)
Theory simplifyCfgFramePrefixes
Ancestors
  simplifyCfgFragments venomExecSemantics venomExecProofs venomInstProps
  venomWf venomInst venomState contextCodegenRel o1PassLift list

Theorem scfg_active_lookup:
  wf_function fn /\ active_inst fn i t /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb ==>
  get_instruction bb t.vs_inst_idx = SOME i
Proof
  strip_tac >> fs[active_inst_def] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  drule_all MEM_lookup_block >> strip_tac >> gvs[get_instruction_def]
QED

Theorem scfg_prefix_terminator:
  eval_phis s bb.bb_instructions = OK v /\
  a = v with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
  scfg_iprefix C bb a t /\ get_instruction bb t.vs_inst_idx = SOME i /\
  is_terminator i.inst_opcode /\ step_inst n C i t = OK u /\ ~u.vs_halted ==>
  ?k. run_block k C bb s = OK u
Proof
  strip_tac >>
  `exec_block n C bb t = OK u` by simp[Once exec_block_def] >>
  drule scfg_iprefix_continue >>
  disch_then (qspecl_then [`n`, `OK u`] mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `m` >> simp[run_block_def]
QED

Theorem scfg_enter_observe[local]:
  wf_function fn /\ enters_block fn s t /\ active_inst fn i t ==>
  ?bb v a. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK v /\
    a = v with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
    scfg_iprefix C bb a t /\ get_instruction bb t.vs_inst_idx = SOME i
Proof
  strip_tac >> fs[enters_block_def] >>
  `s_phi.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `get_instruction bb t.vs_inst_idx = SOME i` by
    (irule scfg_active_lookup >> qexists_tac `fn` >> simp[]) >>
  gvs[scfg_iprefix_rules]
QED

Theorem scfg_frame_reach_decompose:
  wf_function fn /\ frame_reach C fn s0 j t ==>
  ?s bb v a. scfg_bprefix C fn s0 s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK v /\
    a = v with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
    scfg_iprefix C bb a t /\ get_instruction bb t.vs_inst_idx = SOME j
Proof
  strip_tac >> qpat_x_assum `wf_function fn` mp_tac >>
  qpat_x_assum `frame_reach _ _ _ _ _` mp_tac >>
  map_every qid_spec_tac [`t`, `j`, `s0`, `fn`, `C`] >>
  ho_match_mp_tac frame_reach_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      drule_all scfg_enter_observe >> strip_tac >>
      qexists_tac `s0` >> simp[scfg_bprefix_rules] >> metis_tac[]) 
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      rename1 `step_inst _ _ _ t0 = OK u0` >> rename1 `active_inst _ j0 _` >>
      first_x_assum drule >> strip_tac >>
      `u0.vs_current_bb = t0.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
      `t0.vs_current_bb = s.vs_current_bb` by
        (drule scfg_iprefix_current_bb >> strip_tac >>
         drule eval_phis_preserves_current_bb >> gvs[]) >>
      `get_instruction bb (SUC t0.vs_inst_idx) = SOME j0` by
        (drule scfg_active_lookup >>
         disch_then (qspecl_then [`u0 with vs_inst_idx := SUC t0.vs_inst_idx`, `j0`, `bb`] mp_tac) >> simp[]) >>
      qexistsl_tac [`s`, `bb`, `v`, `a`] >> simp[] >>
      irule scfg_iprefix_trans >> qexists_tac `t0` >> conj_tac >- metis_tac[] >>
      irule scfg_iprefix_single >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  rename1 `step_inst _ _ _ _ = OK u0` >>
  first_x_assum drule >> strip_tac >>
  drule_all scfg_prefix_terminator >> strip_tac >>
  `scfg_bprefix C fn s u0` by metis_tac[scfg_bprefix_single] >>
  `scfg_bprefix C fn s0 u0` by metis_tac[scfg_bprefix_trans] >>
  drule_all scfg_enter_observe >> strip_tac >>
  qexists_tac `u0` >> metis_tac[]
QED
