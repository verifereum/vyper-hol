(* Restriction executes identical blocks from entry-reachable labels. *)
Theory simplifyCfgRestrictionSemantics
Ancestors
  simplifyCfgRestriction simplifyCfgSimTools venomExecProofs
  venomExecSemantics venomWf cfgTransform list relation o1PassLift simplifyCfgDefs contextCodegenRel
  simplifyCfgStruct

Theorem scfg_exec_block_reachable:
  wf_function fn /\ fn_inst_wf fn /\ fn_reachable fn l /\
  lookup_block l fn.fn_blocks = SOME bb /\
  exec_block fuel C bb
    (s with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK t ==>
  fn_reachable fn t.vs_current_bb
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = l` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    metis_tac[fn_inst_wf_def, EVERY_MEM] >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by
    (gvs[bb_well_formed_def] >> rpt strip_tac >>
     qpat_x_assum `!i. _ /\ is_terminator _ ==> _`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `MEM t.vs_current_bb (bb_succs bb)` by
    (irule venomExecProofsTheory.exec_block_current_bb_in_succs >>
     simp[] >> conj_tac >- metis_tac[bb_well_formed_def] >>
     qexistsl_tac [`C`, `fuel`,
       `s with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
     simp[phi_prefix_length_le]) >>
  irule scfg_reachable_step >> qexists_tac `l` >> simp[] >>
  simp[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem scfg_restriction_runs:
  !fuel C fn s.
  wf_function fn /\ fn_inst_wf fn /\ fn_reachable fn s.vs_current_bb ==>
  run_blocks fuel C (remove_unreachable_blocks fn) s = run_blocks fuel C fn s
Proof
  Induct_on `fuel` >- simp[run_blocks_def] >>
  rpt strip_tac >>
  `lookup_block s.vs_current_bb (remove_unreachable_blocks fn).fn_blocks =
   lookup_block s.vs_current_bb fn.fn_blocks` by
    (irule scfg_restriction_lookup_reachable >> metis_tac[wf_function_def]) >>
  rewrite_tac[run_blocks_unfold] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `run_block fuel C bb s` >> simp[] >>
  rename1 `run_block fuel C bb s = OK t` >>
  Cases_on `t.vs_halted` >> simp[] >>
  first_x_assum irule >> simp[] >>
  qpat_x_assum `run_block _ _ _ _ = OK _` mp_tac >>
  mp_tac (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  strip_tac >> simp[run_block_def] >> strip_tac >>
  irule scfg_exec_block_reachable >> metis_tac[]
QED

Theorem scfg_restriction_bisim:
  wf_function fn /\ fn_inst_wf fn ==>
  fn_bisim fn (remove_unreachable_blocks fn)
Proof
  strip_tac >> simp[fn_bisim_def, remove_unreachable_blocks_entry] >>
  conj_tac
  >- (Cases_on `fn_entry_label fn` >> simp[remove_unreachable_blocks_def]) >>
  rpt gen_tac >> strip_tac >>
  `fn_reachable fn s.vs_current_bb` by
    (gvs[fn_entry_state_def, fn_reachable_def] >>
     qexists_tac `s.vs_current_bb` >> simp[]) >>
  `!fuel. run_blocks fuel ctx (remove_unreachable_blocks fn) s =
          run_blocks fuel ctx fn s` by metis_tac[scfg_restriction_runs] >>
  simp[] >> conj_tac >> qx_gen_tac `fuel` >> strip_tac >>
  qexists_tac `fuel` >> irule run_blocks_frame_result_refl >> simp[]
QED

Theorem scfg_restriction_enters_back:
  ALL_DISTINCT (fn_labels fn) /\
  enters_block (remove_unreachable_blocks fn) s t ==> enters_block fn s t
Proof
  rw[enters_block_def] >> qexistsl_tac [`bb`, `s_phi`] >> simp[] >>
  metis_tac[scfg_restriction_lookup_back]
QED

Theorem scfg_restriction_active_back:
  active_inst (remove_unreachable_blocks fn) i s ==> active_inst fn i s
Proof
  Cases_on `fn_entry_label fn` >>
  simp[active_inst_def, remove_unreachable_blocks_def, MEM_FILTER] >>
  metis_tac[]
QED

Theorem scfg_restriction_frame_reach_back:
  ALL_DISTINCT (fn_labels fn) /\
  frame_reach C (remove_unreachable_blocks fn) s0 i s ==>
  frame_reach C fn s0 i s
Proof
  `!C fn' s0 i s. frame_reach C fn' s0 i s ==>
     !fn. fn' = remove_unreachable_blocks fn /\ ALL_DISTINCT (fn_labels fn) ==>
          frame_reach C fn s0 i s` suffices_by metis_tac[] >>
  ho_match_mp_tac frame_reach_ind >> rpt strip_tac >> gvs[] >>
  metis_tac[frame_reach_rules, scfg_restriction_enters_back,
            scfg_restriction_active_back]
QED

Theorem scfg_restriction_frame_sim:
  wf_function fn /\ fn_inst_wf fn ==>
  frame_sim L C C fn (remove_unreachable_blocks fn)
Proof
  strip_tac >> simp[frame_sim_def] >> qx_genl_tac [`s0`, `j`, `t`] >> strip_tac >>
  `frame_reach C fn s0 j t` by
    metis_tac[scfg_restriction_frame_reach_back, wf_function_def] >>
  qexistsl_tac [`j`, `t`] >> simp[mem_corr_refl] >>
  irule call_corr_refl >> metis_tac[frame_reach_active, active_inst_wf]
QED
