(* Reusable contracts for unreachable restriction followed by PHI fixup. *)
Theory simplifyCfgCleanup
Ancestors
  simplifyCfgSimTools simplifyCfgRestriction simplifyCfgRestrictionSemantics
  simplifyCfgFixupRuns simplifyCfgFixupFrames simplifyCfgDefs venomWf venomInst
  simplifyCfgStruct o1PassLift passSimulationDefs venomExecSemantics

Theorem scfg_cleanup_bisim:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn ==>
  fn_bisim fn (fix_all_phis (remove_unreachable_blocks fn))
Proof
  strip_tac >> irule fn_bisim_trans >>
  qexists_tac `remove_unreachable_blocks fn` >> conj_tac
  >- metis_tac[scfg_restriction_bisim] >>
  irule scfg_fix_all_phis_bisim >>
  simp[remove_unreachable_blocks_wf, simplifyCfgDefsTheory.remove_unreachable_blocks_fn_inst_wf, scfg_restriction_ok] >>
  rpt strip_tac >> irule scfg_restriction_blocks_reachable >>
  Cases_on `fn.fn_blocks` >> fs[wf_function_def, fn_has_entry_def, fn_entry_label_def, entry_block_def] >>
  metis_tac[]
QED

Theorem scfg_cleanup_frame_sim_same:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn ==>
  frame_sim L C C fn (fix_all_phis (remove_unreachable_blocks fn))
Proof
  strip_tac >> irule frame_sim_trans >>
  qexistsl_tac [`C`, `remove_unreachable_blocks fn`] >>
  simp[remove_unreachable_blocks_entry, scfg_restriction_frame_sim] >>
  irule scfg_fix_all_phis_frame_sim >>
  simp[remove_unreachable_blocks_wf, simplifyCfgDefsTheory.remove_unreachable_blocks_fn_inst_wf, scfg_restriction_ok] >>
  rpt strip_tac >> irule scfg_restriction_blocks_reachable >>
  Cases_on `fn.fn_blocks` >> fs[wf_function_def, fn_has_entry_def, fn_entry_label_def, entry_block_def] >>
  metis_tac[]
QED

Theorem scfg_cleanup_frame_sim:
  ctx_bisim C C' /\ wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn ==>
  frame_sim L C C' fn (fix_all_phis (remove_unreachable_blocks fn))
Proof
  strip_tac >> irule frame_sim_trans >> qexistsl_tac [`C'`, `fn`] >>
  simp[frame_sim_ctx_bisim, scfg_cleanup_frame_sim_same]
QED

Theorem scfg_cleanup_fn_bisim_fuel:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn ==>
  fn_bisim_fuel I fn (fix_all_phis (remove_unreachable_blocks fn))
Proof
  strip_tac >>
  `wf_function (remove_unreachable_blocks fn) /\
   fn_inst_wf (remove_unreachable_blocks fn) /\
   simplify_cfg_fn_ok (remove_unreachable_blocks fn)` by
    simp[remove_unreachable_blocks_wf,
         simplifyCfgDefsTheory.remove_unreachable_blocks_fn_inst_wf,
         scfg_restriction_ok] >>
  `!b. MEM b (remove_unreachable_blocks fn).fn_blocks ==>
       fn_reachable (remove_unreachable_blocks fn) b.bb_label` by
    (rpt strip_tac >> irule scfg_restriction_blocks_reachable >>
     Cases_on `fn.fn_blocks` >>
     fs[wf_function_def, fn_has_entry_def, fn_entry_label_def, entry_block_def] >>
     metis_tac[]) >>
  `(fix_all_phis (remove_unreachable_blocks fn)).fn_name = fn.fn_name` by
    (Cases_on `fn_entry_label fn` >> simp[fix_all_phis_def, remove_unreachable_blocks_def]) >>
  simp[fn_bisim_fuel_def, fix_all_phis_entry, remove_unreachable_blocks_entry] >>
  rpt gen_tac >> strip_tac >>
  `fn_reachable fn s.vs_current_bb` by
    (gvs[fn_entry_state_def, fn_reachable_def] >>
     qexists_tac `s.vs_current_bb` >> simp[]) >>
  `run_blocks fuel ctx (remove_unreachable_blocks fn) s =
   run_blocks fuel ctx fn s` by metis_tac[scfg_restriction_runs] >>
  `run_blocks fuel ctx (fix_all_phis (remove_unreachable_blocks fn)) s =
   run_blocks fuel ctx fn s` by
    (irule scfg_fix_all_phis_entry_runs_forward_same_fuel >>
     gvs[fn_entry_state_def, remove_unreachable_blocks_entry] >>
     Cases_on `run_blocks fuel ctx fn s` >> fs[terminates_def]) >>
  metis_tac[run_blocks_frame_result_refl]
QED
