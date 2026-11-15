(*
 * ConcretizeMemLoc (stage 2) against the O1 pass contract, in the gas
 * form: the theorem o1ContractTheorems re-exports, assembled from the
 * step contract and the stage lemmas (simulation, static memory, pointer
 * discipline, taint, shape).  The output state's headroom
 * (fmp_variant_room NONE) puts the DALLOCA region above the layout end.
 *)
Theory o1ContractConcretize
Ancestors
  o1PassContract venomPassSchedule venomCompilerTypes ptrDiscipline
  ptrStaticDiscipline concretizeStepContract concretizeStageSim
  concretizeStageStatic concretizeStageFramePtr concretizeStageTaint
  concretizeStageShape

(* ConcretizeMemLoc reads callee layouts (the walk view): the raw
   invariant becomes the static one. *)
Theorem o1_contract_concretize_mem_loc:
  o1_step_contract_at 2 rpolicy (CFP_Simple VP_ConcretizeMemLoc) /\
  o1_run_contract_gas rpolicy D fmp 2
Proof
  simp[concretize_step_contract_at] >>
  `EL 2 o1_fn_passes = CFP_Simple VP_ConcretizeMemLoc` by EVAL_TAC >>
  simp[o1_run_contract_gas_def, o1_stage_contract_gas_def, fmp_variant_def,
       fmp_variant_room_def, pass_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  qexists_tac `vs'` >> simp[gas_variant_refl] >> strip_tac >>
  gvs[o1_inv_def, o1_src_inv_def, o1_static_inv_def] >>
  `ctx_inst_ids_distinct C` by fs[o1_ctx_shape_def] >>
  `EVERY all_reachable C.ctx_functions /\
   EVERY fn_defs_reach_uses C.ctx_functions` by
    fs[listTheory.EVERY_MEM, make_ssa_input_ok_def] >>
  drule_all concretize_stage_shape >> strip_tac >>
  `EVERY ssa_form C'.ctx_functions` by
    (irule concretize_stage_ssa_form >> metis_tac[]) >>
  `ctx_has_dalloca C ==>
   ?eom. max_live_eom C' = SOME eom /\ eom <= w2n vs'.vs_initial_fmp` by
    metis_tac[] >>
  `ctx_sim_fuel I D C C' vs' vs'` by
    (irule concretize_stage_sim_fuel >> simp[] >> metis_tac[]) >>
  `mem_inv (static_mem_ok eom) C' vs'` by
    (irule concretize_stage_static_mem >> simp[] >> metis_tac[]) >>
  `?P. EVERY (fn_static_ptr_ok P) C'.ctx_functions` by
    (qpat_assum `ptr_discipline lo C vs'`
       (strip_assume_tac o REWRITE_RULE [ptr_discipline_def]) >>
     qexists_tac `P` >> irule concretize_stage_static_ptr_ok >>
     qexistsl [`C`, `rpolicy`, `o1_walk_view rpolicy 2`] >>
     fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     irule fn_ptr_ok_static >> res_tac) >>
  `!stk PG G tn fn inst s.
     frame_reachable vs' C' stk PG G tn fn inst s ==>
     access_ok eom G fn inst s /\ taint_ok fn tn inst s` by
    (mp_tac (Q.INST [`vs` |-> `vs'`] concretize_stage_frame_ptr_ok) >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  `taint_within D C' vs'` by
    (irule concretize_stage_taint_within >> simp[] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED
