(*
 * ConcretizeMemLoc (stage 2) against the O1 pass contract: the theorem
 * o1ContractTheorems re-exports, assembled from the step contract and
 * the three stage lemmas (simulation, static memory, shape).
 *)
Theory o1ContractConcretize
Ancestors
  o1PassContract venomPassSchedule venomCompilerTypes
  concretizeStepContract concretizeStageSim concretizeStageStatic
  concretizeStageShape

(* ConcretizeMemLoc reads callee layouts (the walk view): the raw
   invariant becomes the static one. *)
Theorem o1_contract_concretize_mem_loc:
  o1_step_contract_at 2 rpolicy (CFP_Simple VP_ConcretizeMemLoc) /\
  o1_run_contract rpolicy D 2
Proof
  simp[concretize_step_contract_at] >>
  `EL 2 o1_fn_passes = CFP_Simple VP_ConcretizeMemLoc` by EVAL_TAC >>
  simp[o1_run_contract_def, o1_stage_contract_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[o1_inv_def, o1_src_inv_def, o1_static_inv_def] >>
  `ctx_inst_ids_distinct C` by fs[o1_ctx_shape_def] >>
  `EVERY all_reachable C.ctx_functions /\
   EVERY fn_defs_reach_uses C.ctx_functions` by
    fs[listTheory.EVERY_MEM, make_ssa_input_ok_def] >>
  drule_all concretize_stage_shape >> strip_tac >>
  `ctx_sim D C C' vs vs` by
    (irule concretize_stage_sim >> simp[] >> metis_tac[]) >>
  `mem_inv (static_mem_ok eom) C' vs` by
    (irule concretize_stage_static_mem >> simp[] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED
